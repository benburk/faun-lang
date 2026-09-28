//! Shared machine-IR natural arithmetic on digits a word wide.
//!
//! A natural is held in a word. One below half a word is an immediate: the
//! word is twice the number, so its lowest bit is clear, it is no object,
//! and it holds no claim. Anything larger is an object, named by its
//! address and one: every block and constant starts on a word, so its
//! address is even and the handle naming it odd, and an object may lie
//! anywhere memory is. Numbers are the common case and objects the rare
//! one, so the tag falls where arithmetic needs no correction -- a sum of
//! immediates is the immediate of the sum, and so is a remainder -- and the
//! one taken off a handle is taken where a digit routine starts, which reads
//! the object's digits a word at a time from there. Every natural is held
//! the one way its size says, so an immediate is always the smaller of an
//! immediate and an object, and immediates are ordered as the words holding
//! them are. Most numbers a program counts with are
//! small, so most arithmetic allocates nothing: each routine answers two
//! immediates itself where the answer is one, and legalization writes that
//! case where it calls one. Otherwise an immediate operand is boxed for as
//! long as the digit routine reading it takes, and a result small enough is
//! answered as an immediate.
//!
//! Inputs are borrowed; every natural result owns a claim, which for an
//! immediate is nothing. The caller must release it. Objects have three
//! target-word headers: total block bytes, reference count, and normalized
//! digit count. Each digit is a word, and the least significant comes
//! first, so a number takes as few loop steps as a word holds it in.
//!
//! Nothing here asks a target for more than a word's arithmetic, which
//! wraps: digits are added, taken and multiplied as the `digits` module says.
//!
//! Division is Knuth's algorithm D, a digit of the quotient at a time, each
//! estimated from the top digits and corrected, with both operands scaled
//! so the divisor's top bit is set. By a single digit it is short division,
//! which scales the dividend as it reads it and allocates only the quotient.
//! Static objects have an all-ones count. Mortal objects live in a private,
//! reusable, coalescing heap, none of which is in the image: where it grows,
//! the target's `grow` gives it its first arena on the first allocation and
//! a new one at least as large as the heap so far each time it is full, or,
//! where that is more than the target has, as much as is wanted; where it
//! does not, it is a fixed arena in the globals. Where there is no more,
//! exhaustion exits with status two. A block comes back with its digits unwritten: every
//! routine but the product writes each digit it reads, and the product
//! clears its own.
//!
//! Retain requires a live borrowed object; release requires an owned claim.
//! Both reject a zero reference count with exit(2), helping expose invalid
//! lifetime schedules. This does not validate arbitrary pointers or stale
//! pointers whose storage has already been reused. They count objects --
//! cells and buffers share them -- so a natural, which may be an immediate,
//! is retained and released through `Library::retain_value` and
//! `Library::release_value`, which look first.

// The generated arithmetic follows the usual a/b, i/j, carry notation.
#![allow(clippy::many_single_char_names)]

use num_bigint::BigUint;

use super::digits::{add_carry, mul_wide, sub_borrow};
use super::{
    Binary, Builder, Class, DataId, Direction, FunctionId, Offset, Program, Relation, ValueId,
    Width,
};

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub word_bits: u16,
    /// The first arena a heap that grows asks the target for, or all of a
    /// heap that does not, which is then in the globals.
    pub heap_bytes: usize,
    /// Whether the heap asks the target for more when it is full, rather
    /// than exiting. A target whose `grow` has nothing to bound it says no.
    pub grows: bool,
    /// Whether the case of two immediates is written where a sum, a monus
    /// or an order is asked, rather than left to the call it saves: faster
    /// wherever a count goes round a loop, and larger at every site.
    pub inline_small: bool,
}

/// One inventory for helper requests, generated handles and omission tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Helper {
    Allocate,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    /// A quotient by a divisor known to fit a word, which only short
    /// division ever answers.
    DivWord,
    /// The same, for a remainder.
    ModWord,
    Compare,
    FromWord,
    ToWord,
    And,
    Or,
    Xor,
}

impl Helper {
    pub(super) const ALL: [Self; 14] = [
        Self::Allocate,
        Self::Add,
        Self::Sub,
        Self::Mul,
        Self::Div,
        Self::Mod,
        Self::DivWord,
        Self::ModWord,
        Self::Compare,
        Self::FromWord,
        Self::ToWord,
        Self::And,
        Self::Or,
        Self::Xor,
    ];

    #[expect(
        clippy::as_conversions,
        reason = "fieldless discriminants index the helper inventory"
    )]
    const fn index(self) -> usize {
        self as usize
    }

    pub(super) const fn arithmetic(op: Binary) -> Self {
        match op {
            Binary::Add => Self::Add,
            // A natural's subtraction is already truncated.
            Binary::Sub | Binary::Monus => Self::Sub,
            Binary::Mul => Self::Mul,
            Binary::Div => Self::Div,
            Binary::Mod => Self::Mod,
            Binary::And => Self::And,
            Binary::Or => Self::Or,
            Binary::Xor => Self::Xor,
            Binary::ShiftUp | Binary::ShiftDown => panic!("a shift is never of a natural"),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Needs([bool; Helper::ALL.len()]);

impl Needs {
    pub(super) const fn insert(&mut self, helper: Helper) {
        self.0[helper.index()] = true;
    }

    pub(super) const fn contains(self, helper: Helper) -> bool {
        self.0[helper.index()]
    }
}

impl<const N: usize> From<[Helper; N]> for Needs {
    fn from(helpers: [Helper; N]) -> Self {
        let mut needs = Self::default();
        for helper in helpers {
            needs.insert(helper);
        }
        needs
    }
}

/// Which natural operations [`Library::inline`] writes the immediate case of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Inline {
    Add,
    Monus,
    Compare,
}

/// Exported handles for requested operations; dependencies stay internal.
///
/// `retain` and `release` count claims on an object: a cell's, a buffer's or
/// a natural's. A natural value may instead be an immediate, which holds no
/// claim, so a natural is retained and released through
/// [`Library::retain_value`] and [`Library::release_value`], which look first.
#[derive(Clone, Debug)]
pub(super) struct Library {
    pub retain: FunctionId,
    pub release: FunctionId,
    /// Retain a natural where it is an object: one call wherever a natural
    /// is kept, rather than the look written out at each.
    keep: FunctionId,
    /// Release a natural where it is an object.
    drop: FunctionId,
    /// Whether [`Self::inline`] writes the case of two immediates out.
    inline_small: bool,
    /// Where immediates begin, as [`half`] says.
    pub half: u64,
    helpers: [Option<FunctionId>; Helper::ALL.len()],
}

impl Library {
    /// The value a natural known before the program runs is held as, where
    /// it is small enough to be an immediate.
    pub(super) fn small(&self, b: &mut Builder<'_>, n: u64) -> Option<ValueId> {
        (n < self.half).then(|| small(b, n))
    }

    /// The immediate holding `n`, a word known to be below half a word.
    pub(super) fn small_word(b: &mut Builder<'_>, n: ValueId) -> ValueId {
        small_word(b, n)
    }

    /// The handle naming a natural constant laid out as an object.
    pub(super) fn constant_handle(b: &mut Builder<'_>, data: DataId) -> ValueId {
        let at = b.address_of(data);
        handle(b, at)
    }

    /// Take another claim to a natural, where it is an object.
    pub(super) fn retain_value(&self, b: &mut Builder<'_>, value: ValueId) -> ValueId {
        b.call(self.keep, &[value]);
        value
    }

    /// Give up a claim to a natural, where it is an object.
    pub(super) fn release_value(&self, b: &mut Builder<'_>, value: ValueId) {
        b.call(self.drop, &[value]);
    }

    /// `a op c` for two naturals, with the case of two immediates whose
    /// answer is one written here and anything else left to the helper:
    /// a sum below half a word, a monus, or an order.
    ///
    /// The helper answers the same where both are immediates; this is only
    /// the call it saves, which for a count in a loop is most of its work.
    #[expect(
        clippy::too_many_lines,
        reason = "each operation inlines its own immediate case beside the shared fallback"
    )]
    pub(super) fn inline(
        &self,
        b: &mut Builder<'_>,
        op: Inline,
        a: ValueId,
        c: ValueId,
    ) -> ValueId {
        let helper = match op {
            Inline::Add => self.require(Helper::Add),
            Inline::Monus => self.require(Helper::Sub),
            Inline::Compare => self.require(Helper::Compare),
        };
        if !self.inline_small {
            return b.call_one(helper, &[a, c]);
        }
        let result = match op {
            Inline::Add | Inline::Monus => A,
            Inline::Compare => W,
        };
        let objects = either_object(b, a, c);
        let called = |b: &mut Builder<'_>| {
            let out = b.call_one(helper, &[a, c]);
            b.yield_(&[out]);
        };
        b.if_(objects, &[result], called, |b| {
            // Immediates are ordered as the words holding them are, and
            // differ by what those words differ by.
            let x = b.convert(W, a);
            let y = b.convert(W, c);
            match op {
                Inline::Add => {
                    // Each holds twice its number, so their sum holds
                    // twice the sum, unless the sum reaches half a
                    // word, which is exactly where adding goes past the
                    // word's top.
                    let sum = add(b, x, y);
                    let outside = lt(b, sum, x);
                    let out = b.if_(outside, &[A], called, |b| {
                        let held = b.convert(A, sum);
                        b.yield_(&[held]);
                    })[0];
                    b.yield_(&[out]);
                }
                Inline::Monus => {
                    // Twice the difference, or nought: what holds it.
                    let rest = b.binary(Binary::Monus, x, y);
                    let held = b.convert(A, rest);
                    b.yield_(&[held]);
                }
                Inline::Compare => {
                    let less = lt(b, x, y);
                    let same = eq(b, x, y);
                    let one = number(b, 1);
                    let apart = sub(b, one, same);
                    let up = add(b, one, apart);
                    let order = sub(b, up, less);
                    let order = sub(b, order, less);
                    b.yield_(&[order]);
                }
            }
        })[0]
    }

    pub(super) const fn get(&self, helper: Helper) -> Option<FunctionId> {
        self.helpers[helper.index()]
    }

    pub(super) const fn require(&self, helper: Helper) -> FunctionId {
        self.get(helper)
            .expect("requested natural helper was generated")
    }

    const fn insert(&mut self, helper: Helper, function: FunctionId) {
        self.helpers[helper.index()] = Some(function);
    }
}

const A: Class = Class::Address;
const W: Class = Class::Word;

impl Config {
    pub(super) const fn layout(self) -> super::Layout {
        super::Layout {
            word_bits: self.word_bits,
        }
    }

    fn checked(self) -> Result<(usize, u64), String> {
        if !matches!(self.word_bits, 16 | 32 | 64) {
            return Err("natural runtime needs a 16, 32, or 64 bit word".to_owned());
        }
        let bytes = usize::from(self.word_bits / 8);
        let max = u64::MAX >> (64 - self.word_bits);
        if self.heap_bytes < 4 * bytes
            || !self.heap_bytes.is_multiple_of(bytes)
            || !u64::try_from(self.heap_bytes).is_ok_and(|n| n <= max)
            || u32::try_from(self.heap_bytes).is_err()
        {
            return Err(
                "natural heap must fit a word, be word-aligned, and hold a header and digit"
                    .to_owned(),
            );
        }
        Ok((bytes, max))
    }
}

fn header(bytes: &mut [u8], at: usize, value: u64, word: usize) {
    bytes[at * word..(at + 1) * word].copy_from_slice(&value.to_le_bytes()[..word]);
}

/// Append an immortal natural in the runtime representation.
///
/// # Errors
/// If the configuration or object size does not fit the target.
pub(super) fn constant(
    program: &mut Program,
    config: Config,
    magnitude: &BigUint,
) -> Result<DataId, String> {
    let (word, max) = config.checked()?;
    let mut digits = magnitude.to_bytes_le();
    while digits.last() == Some(&0) {
        digits.pop();
    }
    // Little-endian bytes are little-endian words, the last padded out.
    let count = digits.len().div_ceil(word);
    digits.resize(count * word, 0);
    let size = count
        .checked_add(3)
        .and_then(|n| n.checked_mul(word))
        .ok_or_else(|| "natural constant is too large".to_owned())?;
    if !u64::try_from(size).is_ok_and(|n| n <= max) || u32::try_from(size).is_err() {
        return Err("natural constant does not fit the target address space".to_owned());
    }
    let padding = (word - program.data().len() % word) % word;
    if program
        .data()
        .len()
        .checked_add(padding)
        .and_then(|n| n.checked_add(size))
        .is_none_or(|n| u32::try_from(n).is_err())
    {
        return Err("natural constants exceed the data pool".to_owned());
    }
    program.bind_layout(config.layout())?;
    if padding != 0 {
        program.intern(&vec![0; padding]);
    }
    let mut bytes = vec![0; size];
    header(&mut bytes, 0, size64(size), word);
    header(&mut bytes, 1, max, word);
    header(&mut bytes, 2, size64(count), word);
    bytes[3 * word..3 * word + digits.len()].copy_from_slice(&digits);
    Ok(program.intern(&bytes))
}

fn size64(n: usize) -> u64 {
    u64::try_from(n).expect("a checked pool size fits u64")
}

fn number(b: &mut Builder<'_>, n: u64) -> ValueId {
    b.constant(W, n)
}

fn add(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.binary(Binary::Add, a, c)
}

fn sub(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.binary(Binary::Sub, a, c)
}

fn eq(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.compare(Relation::Equal, a, c)
}

fn lt(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.compare(Relation::Less, a, c)
}

fn address(b: &mut Builder<'_>, base: ValueId, offset: ValueId) -> ValueId {
    let base = b.convert(W, base);
    let at = add(b, base, offset);
    b.convert(A, at)
}

fn length(b: &mut Builder<'_>, a: ValueId) -> ValueId {
    b.load(Width::Word, a, Offset::Words(2))
}

fn set_length(b: &mut Builder<'_>, a: ValueId, n: ValueId) {
    b.store(Width::Word, a, Offset::Words(2), n);
}

fn digit_address(b: &mut Builder<'_>, a: ValueId, i: ValueId, word: usize) -> ValueId {
    let bytes = number(b, size64(word));
    let offset = b.binary(Binary::Mul, i, bytes);
    let header = number(b, size64(3 * word));
    let offset = add(b, offset, header);
    address(b, a, offset)
}

fn read_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, word: usize) -> ValueId {
    let at = digit_address(b, a, i, word);
    b.load(Width::Word, at, Offset::Bytes(0))
}

fn write_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, v: ValueId, word: usize) {
    let at = digit_address(b, a, i, word);
    b.store(Width::Word, at, Offset::Bytes(0), v);
}

/// The bits of a target's word, from its bytes.
fn word_bits(word: usize) -> u16 {
    u16::try_from(word * 8).expect("a word's bits fit u16")
}

fn declare(p: &mut Program, name: &str, params: &[Class], result: &[Class]) -> FunctionId {
    p.declare(name, params, result)
}

/// Append only the requested arithmetic families and their dependencies.
///
/// Helper calls have at most four arguments and one result; loops carry at
/// most two values, so the library also fits the narrowest target's ABI.
///
/// # Errors
/// If the heap configuration is invalid. The generated library declares
/// nonreturning `exit(word)`; the target must supply that contract.
#[expect(
    clippy::too_many_lines,
    reason = "the library is generated in the order its routines depend on one another"
)]
pub(super) fn append(
    program: &mut Program,
    config: Config,
    needs: Needs,
) -> Result<Library, String> {
    let (word, max) = config.checked()?;
    let half = half(config.word_bits);
    // What a request for no bytes is answered with. No natural is held as
    // it: nought is an immediate like every other small number.
    let empty = constant(program, config, &BigUint::default())?;
    let (retain, release, fail) = claims(program, max);
    let mut library = Library {
        retain,
        release,
        keep: unless_small(program, "nat.keep", retain),
        drop: unless_small(program, "nat.drop", release),
        inline_small: config.inline_small,
        half,
        helpers: [None; Helper::ALL.len()],
    };
    let arithmetic = Helper::ALL.into_iter().any(|helper| {
        needs.contains(helper) && !matches!(helper, Helper::Compare | Helper::ToWord)
    });
    let narrow = (arithmetic || needs.contains(Helper::ToWord)).then(|| narrowing(program, word));
    let compare = (needs.contains(Helper::Compare)
        || [Helper::Sub, Helper::Div, Helper::Mod]
            .into_iter()
            .any(|h| needs.contains(h)))
    .then(|| comparison(program, word));
    if let Some(compare) = compare
        && needs.contains(Helper::Compare)
    {
        library.insert(Helper::Compare, comparing(program, compare));
    }
    if let Some(narrow) = narrow
        && needs.contains(Helper::ToWord)
    {
        library.insert(Helper::ToWord, lowering(program, narrow));
    }
    if arithmetic {
        let alloc = allocation(program, config, (word, max), (empty, fail))?;
        if needs.contains(Helper::Allocate) {
            library.insert(Helper::Allocate, alloc);
        }
        // What the allocator would take, in digits: the heap less a header,
        // or, where the heap grows, a quarter of the address space.
        let most = if config.grows {
            max / 4
        } else {
            size64(config.heap_bytes - 3 * word)
        } / size64(word);
        let digits = digits_allocation(program, (alloc, fail), (word, most));
        let trim = trimming(program, word);
        let narrow = narrow.expect("arithmetic reads a small result back as a word");
        let finish = finishing(program, (trim, narrow), release, half);
        let boxed = boxing(program, digits, trim, word);
        let storage = Storage {
            word,
            most,
            half,
            alloc: digits,
            trim,
            finish,
            fail,
            boxed,
            release,
        };
        storage.append(program, needs, compare, &mut library);
        storage.append_bitwise(program, needs, &mut library);
    }
    Ok(library)
}

/// Where immediates end: half a word. A number below it is held as twice
/// itself; any other is an object.
pub(super) const fn half(word_bits: u16) -> u64 {
    1 << (word_bits - 1)
}

/// The immediate holding `n`, which must be below `half`.
fn small(b: &mut Builder<'_>, n: u64) -> ValueId {
    let held = number(b, 2 * n);
    b.convert(A, held)
}

/// The immediate holding a word known to be below `half`.
fn small_word(b: &mut Builder<'_>, n: ValueId) -> ValueId {
    let doubled = b.shift(W, Direction::Up, n, 1);
    b.convert(A, doubled)
}

/// One where `value` is an immediate, nought where it names an object:
/// where its lowest bit is clear, which only a handle's is not.
fn is_small(b: &mut Builder<'_>, value: ValueId) -> ValueId {
    let held = b.convert(W, value);
    let bit = b.convert(Class::fixed(1), held);
    let zero = number(b, 0);
    eq(b, bit, zero)
}

/// One where `value` names an object, nought where it is an immediate: its
/// lowest bit, which a branch reads as it stands.
fn is_object(b: &mut Builder<'_>, value: ValueId) -> ValueId {
    let held = b.convert(W, value);
    b.convert(Class::fixed(1), held)
}

/// Nought where both `a` and `c` are immediates, and not where either names
/// an object: what a branch to their fast case asks.
fn either_object(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    let named_a = is_object(b, a);
    let named_c = is_object(b, c);
    let named_a = b.convert(W, named_a);
    add(b, named_a, named_c)
}

/// The object a handle names: its address, which is one less.
fn object(b: &mut Builder<'_>, handle: ValueId) -> ValueId {
    let held = b.convert(W, handle);
    let one = number(b, 1);
    let at = sub(b, held, one);
    b.convert(A, at)
}

/// The handle naming the object at `address`: one more.
fn handle(b: &mut Builder<'_>, address: ValueId) -> ValueId {
    let held = b.convert(W, address);
    let one = number(b, 1);
    let named = add(b, held, one);
    b.convert(A, named)
}

/// The number an immediate holds.
fn unwrapped(b: &mut Builder<'_>, value: ValueId) -> ValueId {
    let held = b.convert(W, value);
    b.shift(W, Direction::Down, held, 1)
}

/// A routine calling `count` with a natural where it is an object, and
/// doing nothing where it is an immediate, which holds no claim.
fn unless_small(program: &mut Program, name: &str, count: FunctionId) -> FunctionId {
    let f = declare(program, name, &[A], &[]);
    program.define(f, |b, args| {
        let value = args[0];
        let named = is_object(b, value);
        b.if_(
            named,
            &[],
            |b| {
                let at = object(b, value);
                b.call(count, &[at]);
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.ret(&[]);
    });
    f
}

fn claims(program: &mut Program, max: u64) -> (FunctionId, FunctionId, FunctionId) {
    let exit = program.external("exit!", &[W], super::Returns::Never);
    let fail = program.declare_never("nat.fail", &[]);
    program.define(fail, |b, _| {
        let status = number(b, 2);
        b.call(exit, &[status]);
    });
    let retain = declare(program, "nat.retain", &[A], &[A]);
    let release = declare(program, "nat.release", &[A], &[]);
    counting(program, retain, release, fail, max);
    (retain, release, fail)
}

#[derive(Clone, Copy)]
struct Storage {
    word: usize,
    /// The most digits one object is asked for: past this, a request fails
    /// before its size is worked out.
    most: u64,
    half: u64,
    /// Allocates an object for digits, in the lower half of the address
    /// space where an object has to be.
    alloc: FunctionId,
    trim: FunctionId,
    finish: FunctionId,
    fail: FunctionId,
    /// An object holding the number an immediate holds, for a routine that
    /// reads digits.
    boxed: FunctionId,
    release: FunctionId,
}

impl Storage {
    fn append(self, p: &mut Program, needs: Needs, compare: Option<FunctionId>, lib: &mut Library) {
        if needs.contains(Helper::FromWord) {
            lib.insert(Helper::FromWord, promotion(p, self));
        }
        let divides = [Helper::Div, Helper::Mod, Helper::DivWord, Helper::ModWord]
            .into_iter()
            .any(|h| needs.contains(h));
        let divisions = divides.then(|| Divisions::append(p, self));
        for (helper, result) in [
            (Helper::DivWord, DivisionResult::Quotient),
            (Helper::ModWord, DivisionResult::Remainder),
        ] {
            if needs.contains(helper) {
                let divisions = divisions.expect("a division has its short division");
                lib.insert(
                    helper,
                    Self::by_word(p, divisions.short, result, lib.retain),
                );
            }
        }
        if needs.contains(Helper::Mul) {
            let objects = multiplication(p, self);
            lib.insert(Helper::Mul, self.product(p, objects));
        }
        if [Helper::Add, Helper::Sub, Helper::Div, Helper::Mod]
            .into_iter()
            .any(|h| needs.contains(h))
        {
            let digit = digit_reader(p, self.word);
            if needs.contains(Helper::Add) {
                let objects = addition(p, self, digit);
                lib.insert(Helper::Add, self.sum(p, objects));
            }
            if [Helper::Sub, Helper::Div, Helper::Mod]
                .into_iter()
                .any(|h| needs.contains(h))
            {
                let compare = compare.expect("subtraction and division compare digits");
                self.append_subdivision(p, needs, lib, (digit, compare), divisions);
            }
        }
    }

    fn append_bitwise(self, p: &mut Program, needs: Needs, lib: &mut Library) {
        let bitwise = [
            (Helper::And, Binary::And, "and"),
            (Helper::Or, Binary::Or, "or"),
            (Helper::Xor, Binary::Xor, "xor"),
        ];
        if !bitwise.iter().any(|&(helper, ..)| needs.contains(helper)) {
            return;
        }
        let digit = digit_reader(p, self.word);
        for (helper, op, name) in bitwise {
            if needs.contains(helper) {
                let objects = bitwise_digits(p, self, digit, (op, name));
                lib.insert(helper, self.bitwise(p, objects, (op, name)));
            }
        }
    }

    fn append_subdivision(
        self,
        p: &mut Program,
        needs: Needs,
        lib: &mut Library,
        (digit, compare): (FunctionId, FunctionId),
        divisions: Option<Divisions>,
    ) {
        let subtract = subtracting(p, digit, self.trim, self.word);
        if needs.contains(Helper::Sub) {
            let objects = monus(p, self, compare, subtract);
            lib.insert(Helper::Sub, self.difference(p, objects));
        }
        if needs.contains(Helper::Div) || needs.contains(Helper::Mod) {
            let divisions = divisions.expect("a division has its short division");
            let divmod = division(p, self, (compare, lib.retain), divisions);
            if needs.contains(Helper::Div) {
                lib.insert(
                    Helper::Div,
                    self.quotient(p, divmod, DivisionResult::Quotient),
                );
            }
            if needs.contains(Helper::Mod) {
                lib.insert(
                    Helper::Mod,
                    self.quotient(p, divmod, DivisionResult::Remainder),
                );
            }
        }
    }
}

/// The entries arithmetic calls: each answers what it can from immediates
/// alone, and hands anything else to the routine reading digits, with each
/// immediate in an object of its own for as long as that takes.
impl Storage {
    fn sum(self, p: &mut Program, objects: FunctionId) -> FunctionId {
        let half = self.half;
        let f = declare(p, "nat.add", &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            both_small(b, a, c, |b, x, y| {
                // Each is below half a word, so their sum is below a word.
                let sum = add(b, x, y);
                let top = number(b, half);
                let fits = lt(b, sum, top);
                b.if_(
                    fits,
                    &[],
                    |b| {
                        let held = small_word(b, sum);
                        b.ret(&[held]);
                    },
                    |b| b.yield_(&[]),
                );
                b.yield_(&[]);
            });
            let out = self.through_digits(b, objects, a, c, &[]);
            b.ret(&[out]);
        });
        f
    }

    /// A bitwise operation: of two immediates, the immediate of their
    /// numbers', which is below half a word as both are.
    fn bitwise(
        self,
        p: &mut Program,
        objects: FunctionId,
        (op, name): (Binary, &str),
    ) -> FunctionId {
        let f = declare(p, &format!("nat.{name}"), &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            both_small(b, a, c, |b, x, y| {
                let answer = b.binary(op, x, y);
                let held = small_word(b, answer);
                b.ret(&[held]);
            });
            let out = self.through_digits(b, objects, a, c, &[]);
            b.ret(&[out]);
        });
        f
    }

    fn difference(self, p: &mut Program, objects: FunctionId) -> FunctionId {
        let f = declare(p, "nat.sub", &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            let small_a = is_small(b, a);
            b.if_(
                small_a,
                &[],
                |b| {
                    both_small(b, a, c, |b, x, y| {
                        let rest = b.binary(Binary::Monus, x, y);
                        let held = small_word(b, rest);
                        b.ret(&[held]);
                    });
                    // An object is more than any immediate.
                    let z = small(b, 0);
                    b.ret(&[z]);
                },
                |b| b.yield_(&[]),
            );
            let out = self.through_digits(b, objects, a, c, &[]);
            b.ret(&[out]);
        });
        f
    }

    fn product(self, p: &mut Program, objects: FunctionId) -> FunctionId {
        let half = self.half;
        // Two numbers each below this multiply to one below half a word.
        let root = 1u64 << (half.trailing_zeros() / 2);
        let f = declare(p, "nat.mul", &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            both_small(b, a, c, |b, x, y| {
                let bound = number(b, root);
                let low_x = lt(b, x, bound);
                let low_y = lt(b, y, bound);
                let both = b.binary(Binary::Mul, low_x, low_y);
                b.if_(
                    both,
                    &[],
                    |b| {
                        let product = b.binary(Binary::Mul, x, y);
                        let held = small_word(b, product);
                        b.ret(&[held]);
                    },
                    |b| b.yield_(&[]),
                );
                b.yield_(&[]);
            });
            let out = self.through_digits(b, objects, a, c, &[]);
            b.ret(&[out]);
        });
        f
    }

    fn quotient(self, p: &mut Program, divmod: FunctionId, result: DivisionResult) -> FunctionId {
        let (name, mode) = match result {
            DivisionResult::Quotient => ("nat.div", 0),
            DivisionResult::Remainder => ("nat.mod", 1),
        };
        let f = declare(p, name, &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            // Where the divisor is more than the dividend, the quotient is
            // nought and the remainder the dividend: an immediate divided by
            // an object, or anything by nought.
            let whole = |b: &mut Builder<'_>| {
                let out = match result {
                    DivisionResult::Quotient => small(b, 0),
                    DivisionResult::Remainder => a,
                };
                b.ret(&[out]);
            };
            let small_a = is_small(b, a);
            b.if_(
                small_a,
                &[],
                |b| {
                    both_small(b, a, c, |b, x, y| {
                        let nil = number(b, 0);
                        let by_nought = eq(b, y, nil);
                        b.if_(by_nought, &[], |b| whole(b), |b| b.yield_(&[]));
                        let op = match result {
                            DivisionResult::Quotient => Binary::Div,
                            DivisionResult::Remainder => Binary::Mod,
                        };
                        let out = b.binary(op, x, y);
                        let held = small_word(b, out);
                        b.ret(&[held]);
                    });
                    whole(b);
                },
                |b| b.yield_(&[]),
            );
            let mode = number(b, mode);
            let out = self.through_digits(b, divmod, a, c, &[mode]);
            b.ret(&[out]);
        });
        f
    }

    /// A quotient or remainder by `d`, a word: by nought as every division
    /// by nought answers, an immediate by the word's own division, and an
    /// object by short division. No long division is reached, so a program
    /// dividing only by words carries none.
    fn by_word(
        p: &mut Program,
        short: FunctionId,
        result: DivisionResult,
        retain: FunctionId,
    ) -> FunctionId {
        let (name, mode, op) = match result {
            DivisionResult::Quotient => ("nat.div_word", 0, Binary::Div),
            DivisionResult::Remainder => ("nat.mod_word", 1, Binary::Mod),
        };
        let f = declare(p, name, &[A, W], &[A]);
        p.define(f, |b, args| {
            let (a, d) = (args[0], args[1]);
            let zero = number(b, 0);
            let by_nought = eq(b, d, zero);
            let small_a = is_small(b, a);
            b.if_(
                by_nought,
                &[],
                |b| {
                    let out = by_nought_answer(b, (a, small_a), result, retain);
                    b.ret(&[out]);
                },
                |b| b.yield_(&[]),
            );
            b.if_(
                small_a,
                &[],
                |b| {
                    let x = unwrapped(b, a);
                    let out = b.binary(op, x, d);
                    let held = small_word(b, out);
                    b.ret(&[held]);
                },
                |b| b.yield_(&[]),
            );
            let mode = number(b, mode);
            let at = object(b, a);
            let out = b.call_one(short, &[at, d, mode]);
            b.ret(&[out]);
        });
        f
    }

    /// Call a routine reading digits with `a` and `c` as objects, then
    /// `rest`, boxing whichever is an immediate and releasing that box
    /// afterwards.
    fn through_digits(
        self,
        b: &mut Builder<'_>,
        objects: FunctionId,
        a: ValueId,
        c: ValueId,
        rest: &[ValueId],
    ) -> ValueId {
        let (boxed, release) = (self.boxed, self.release);
        let held = [a, c].map(|value| {
            let named = is_object(b, value);
            let object = b.if_(
                named,
                &[A],
                |b| {
                    let at = object(b, value);
                    b.yield_(&[at]);
                },
                |b| {
                    let n = unwrapped(b, value);
                    let object = b.call_one(boxed, &[n]);
                    b.yield_(&[object]);
                },
            )[0];
            (named, object)
        });
        let mut args = vec![held[0].1, held[1].1];
        args.extend_from_slice(rest);
        let out = b.call_one(objects, &args);
        for (named, object) in held {
            b.if_(
                named,
                &[],
                |b| b.yield_(&[]),
                |b| {
                    b.call(release, &[object]);
                    b.yield_(&[]);
                },
            );
        }
        out
    }
}

/// What dividing `a` by nought answers: nought, or `a` itself, which is
/// owned where it is answered, as the `a` handed in is not.
fn by_nought_answer(
    b: &mut Builder<'_>,
    (a, small_a): (ValueId, ValueId),
    result: DivisionResult,
    retain: FunctionId,
) -> ValueId {
    match result {
        DivisionResult::Quotient => small(b, 0),
        DivisionResult::Remainder => {
            b.if_(
                small_a,
                &[],
                |b| b.yield_(&[]),
                |b| {
                    let at = object(b, a);
                    b.call(retain, &[at]);
                    b.yield_(&[]);
                },
            );
            a
        }
    }
}

/// Run `then` with the numbers `a` and `c` hold where both are immediates.
/// It ends its arm itself: answering the routine, or yielding to go on.
fn both_small(
    b: &mut Builder<'_>,
    a: ValueId,
    c: ValueId,
    then: impl FnOnce(&mut Builder<'_>, ValueId, ValueId),
) {
    let objects = either_object(b, a, c);
    b.if_(
        objects,
        &[],
        |b| b.yield_(&[]),
        |b| {
            let x = unwrapped(b, a);
            let y = unwrapped(b, c);
            then(b, x, y);
        },
    );
}

/// The order of two naturals, as the routine reading digits answers it:
/// nought for less, one for equal, two for greater. Immediates are ordered
/// as the words holding them are, and an object is more than any of them.
#[expect(
    clippy::too_many_lines,
    reason = "four cases of immediate and object, each answering an order"
)]
fn comparing(p: &mut Program, objects: FunctionId) -> FunctionId {
    let f = declare(p, "nat.compare", &[A, A], &[W]);
    p.define(f, |b, args| {
        let (a, c) = (args[0], args[1]);
        let small_a = is_small(b, a);
        let small_c = is_small(b, c);
        b.if_(
            small_a,
            &[],
            |b| {
                b.if_(
                    small_c,
                    &[],
                    |b| {
                        let x = b.convert(W, a);
                        let y = b.convert(W, c);
                        let less = lt(b, x, y);
                        let same = eq(b, x, y);
                        // Less is nought, equal one and greater two:
                        // one, less one where less, plus one where not
                        // equal either.
                        let one = number(b, 1);
                        let apart = b.binary(Binary::Sub, one, same);
                        let up = add(b, one, apart);
                        let order = b.binary(Binary::Sub, up, less);
                        let order = b.binary(Binary::Sub, order, less);
                        b.ret(&[order]);
                    },
                    |b| {
                        let less = number(b, 0);
                        b.ret(&[less]);
                    },
                );
            },
            |b| b.yield_(&[]),
        );
        b.if_(
            small_c,
            &[],
            |b| {
                let greater = number(b, 2);
                b.ret(&[greater]);
            },
            |b| b.yield_(&[]),
        );
        let named = [a, c].map(|value| object(b, value));
        let order = b.call_one(objects, &named);
        b.ret(&[order]);
    });
    f
}

/// A natural's low word: an immediate's number, or an object's low digits.
fn lowering(p: &mut Program, objects: FunctionId) -> FunctionId {
    let f = declare(p, "nat.to_word", &[A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let small_a = is_small(b, a);
        b.if_(
            small_a,
            &[],
            |b| {
                let n = unwrapped(b, a);
                b.ret(&[n]);
            },
            |b| b.yield_(&[]),
        );
        let a = object(b, a);
        let out = b.call_one(objects, &[a]);
        b.ret(&[out]);
    });
    f
}

#[expect(
    clippy::too_many_lines,
    reason = "two symmetric generated reference-count routines"
)]
fn counting(p: &mut Program, retain: FunctionId, release: FunctionId, fail: FunctionId, max: u64) {
    p.define(retain, |b, args| {
        let a = args[0];
        let refs = live_count(b, a, fail);
        let immortal = number(b, max);
        let static_ = eq(b, refs, immortal);
        b.if_(
            static_,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let limit = number(b, max - 1);
                let full = eq(b, refs, limit);
                b.if_(
                    full,
                    &[],
                    |b| {
                        b.call(fail, &[]);
                    },
                    |b| b.yield_(&[]),
                );
                let one = number(b, 1);
                let next = add(b, refs, one);
                b.store(Width::Word, a, Offset::Words(1), next);
                b.yield_(&[]);
            },
        );
        b.ret(&[a]);
    });
    p.define(release, |b, args| {
        let a = args[0];
        let refs = live_count(b, a, fail);
        let immortal = number(b, max);
        let static_ = eq(b, refs, immortal);
        b.if_(
            static_,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let one = number(b, 1);
                let next = sub(b, refs, one);
                b.store(Width::Word, a, Offset::Words(1), next);
                b.yield_(&[]);
            },
        );
        b.ret(&[]);
    });
}

fn live_count(b: &mut Builder<'_>, object: ValueId, fail: FunctionId) -> ValueId {
    let refs = b.load(Width::Word, object, Offset::Words(1));
    let zero = number(b, 0);
    let freed = eq(b, refs, zero);
    b.if_(
        freed,
        &[],
        |b| {
            b.call(fail, &[]);
        },
        |b| b.yield_(&[]),
    );
    refs
}

// The request checks and first-fit scan stay together; nested work is
// generated separately to bound the narrow target's frame pressure.
#[expect(clippy::too_many_lines)]
fn allocator(
    p: &mut Program,
    config: Config,
    word: usize,
    zero: DataId,
    fail: FunctionId,
) -> Result<FunctionId, String> {
    let padding = (word - p.globals().len() % word) % word;
    if p.globals()
        .len()
        .checked_add(padding)
        .and_then(|n| n.checked_add(config.heap_bytes))
        .is_none_or(|n| u32::try_from(n).is_err())
    {
        return Err("natural heap exceeds the globals pool".to_owned());
    }
    if padding != 0 {
        p.global(&vec![0; padding]);
    }
    let mut bytes = vec![0; config.heap_bytes];
    header(&mut bytes, 0, size64(config.heap_bytes), word);
    let heap = p.global(&bytes);
    let coalesce = coalescing(p);
    let claim = claiming(p, word);
    let allocate = declare(p, "nat.allocate", &[W], &[A]);
    p.define(allocate, |b, args| {
        let cap = args[0];
        let nil = number(b, 0);
        let empty = eq(b, cap, nil);
        b.if_(
            empty,
            &[],
            |b| {
                let z = b.address_of(zero);
                b.ret(&[z]);
            },
            |b| b.yield_(&[]),
        );
        let limit = number(b, size64(config.heap_bytes - 3 * word));
        let huge = lt(b, limit, cap);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        // The aligned pool fits a word, so even the rounding addition fits.
        let overhead = number(b, size64(4 * word - 1));
        let size = add(b, cap, overhead);
        let unit = number(b, size64(word));
        let units = b.binary(Binary::Div, size, unit);
        let wanted = b.binary(Binary::Mul, units, unit);
        let base = b.address_of(heap);
        let pool = number(b, size64(config.heap_bytes));
        let result = b.loop_(&[nil], &[A], |b, state| {
            let offset = state[0];
            let end = eq(b, offset, pool);
            b.if_(
                end,
                &[],
                |b| {
                    b.call(fail, &[]);
                },
                |b| b.yield_(&[]),
            );
            let at = address(b, base, offset);
            let size = b.load(Width::Word, at, Offset::Words(0));
            let refs = b.load(Width::Word, at, Offset::Words(1));
            let free = eq(b, refs, nil);
            b.if_(
                free,
                &[],
                |b| {
                    let merged = b.call_one(coalesce, &[base, offset, pool]);
                    b.store(Width::Word, at, Offset::Words(0), merged);
                    let small = lt(b, merged, wanted);
                    b.if_(
                        small,
                        &[],
                        |b| {
                            let next = add(b, offset, merged);
                            b.continue_(&[next]);
                        },
                        |b| {
                            b.call(claim, &[at, wanted, cap]);
                            b.break_(&[at]);
                        },
                    );
                },
                |b| {
                    let next = add(b, offset, size);
                    b.continue_(&[next]);
                },
            );
        })[0];
        b.ret(&[result]);
    });
    Ok(allocate)
}

/// The allocator the heap's configuration asks for.
fn allocation(
    program: &mut Program,
    config: Config,
    (word, max): (usize, u64),
    (zero, fail): (DataId, FunctionId),
) -> Result<FunctionId, String> {
    if config.grows {
        Ok(growing(program, config, (word, max), zero, fail))
    } else {
        allocator(program, config, word, zero, fail)
    }
}

/// Words at the start of every arena: the next arena, and where its blocks
/// end. A next of nought is the first arena, the one in the globals.
const ARENA_WORDS: usize = 2;

/// The allocator of a heap that grows: a ring of arenas, searched first-fit
/// from where the last allocation ended. The first is in the globals and
/// holds no blocks, so the image holds none of the heap: every other comes
/// from the target's `grow`, the first of them `heap_bytes` large, which the
/// first allocation asks for. Where no arena has room, a new one at least as
/// large as the heap so far is asked for, so the heap doubles and a program
/// asks the target a number of times logarithmic in what it holds; where
/// the target has not that much, it is asked for no more than is wanted.
///
/// Where the search starts is kept in the globals with the number of
/// arenas and the heap's size. Every allocation moves it, so a search that
/// coalesced blocks around it never starts inside one.
#[expect(
    clippy::too_many_lines,
    reason = "the search and the growth share the state they keep"
)]
fn growing(
    p: &mut Program,
    config: Config,
    (word, max): (usize, u64),
    zero: DataId,
    fail: FunctionId,
) -> FunctionId {
    let padding = (word - p.globals().len() % word) % word;
    if padding != 0 {
        p.global(&vec![0; padding]);
    }
    let start = ARENA_WORDS * word;
    // The first arena: its header, and no blocks, since its blocks end
    // where they begin.
    let mut bytes = vec![0; start];
    header(&mut bytes, 1, size64(start), word);
    let heap = p.global(&bytes);
    // Where the search starts, as an arena (nought for the first) and an
    // offset in it; how many arenas there are; how large the heap is
    // counted as, which is what the first arena asked for is; and how many
    // arenas a search has begun, kept here rather than going round with it
    // so that a search carries two values, as the narrowest target does.
    let mut state = vec![0; 5 * word];
    header(&mut state, 1, size64(start), word);
    header(&mut state, 2, 1, word);
    header(&mut state, 3, size64(config.heap_bytes), word);
    let kept_at = p.global(&state);
    let grow = p.external("grow", &[W], super::Returns::Values(&[A]));
    let coalesce = coalescing(p);
    let claim = claiming(p, word);
    let allocate = declare(p, "nat.allocate", &[W], &[A]);
    p.define(allocate, |b, args| {
        let cap = args[0];
        let nil = number(b, 0);
        let empty = eq(b, cap, nil);
        b.if_(
            empty,
            &[],
            |b| {
                let z = b.address_of(zero);
                b.ret(&[z]);
            },
            |b| b.yield_(&[]),
        );
        // Far below what could wrap: no request that large is met.
        let limit = number(b, max / 4);
        let huge = lt(b, limit, cap);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let overhead = number(b, size64(4 * word - 1));
        let size = add(b, cap, overhead);
        let unit = number(b, size64(word));
        let units = b.binary(Binary::Div, size, unit);
        let wanted = b.binary(Binary::Mul, units, unit);
        let first = b.address_of(heap);
        let kept = b.address_of(kept_at);
        // An arena named by a word, where nought is the first.
        let arena_at = |b: &mut Builder<'_>, named: ValueId| {
            let nil = number(b, 0);
            let is_first = eq(b, named, nil);
            b.if_(
                is_first,
                &[A],
                |b| {
                    let first = b.address_of(heap);
                    b.yield_(&[first]);
                },
                |b| {
                    let at = b.convert(A, named);
                    b.yield_(&[at]);
                },
            )[0]
        };
        let rover = b.load(Width::Word, kept, Offset::Words(0));
        let arena = arena_at(b, rover);
        let offset = b.load(Width::Word, kept, Offset::Words(1));
        let arenas = b.load(Width::Word, kept, Offset::Words(2));
        b.store(Width::Word, kept, Offset::Words(4), nil);
        let found = b.loop_(&[arena, offset], &[A, W], |b, state| {
            let (arena, offset) = (state[0], state[1]);
            let end = b.load(Width::Word, arena, Offset::Words(1));
            let at_end = eq(b, offset, end);
            b.if_(
                at_end,
                &[],
                |b| {
                    // On to the next arena, having begun as many as there
                    // are after the one the search began part way through.
                    let kept = b.address_of(kept_at);
                    let starts = b.load(Width::Word, kept, Offset::Words(4));
                    let one = number(b, 1);
                    let more = add(b, starts, one);
                    b.store(Width::Word, kept, Offset::Words(4), more);
                    let done = lt(b, arenas, more);
                    b.if_(
                        done,
                        &[],
                        |b| {
                            let nil = number(b, 0);
                            let first = b.address_of(heap);
                            b.break_(&[first, nil]);
                        },
                        |b| b.yield_(&[]),
                    );
                    let next = b.load(Width::Word, arena, Offset::Words(0));
                    let next = arena_at(b, next);
                    let start = number(b, size64(start));
                    b.continue_(&[next, start]);
                },
                |b| b.yield_(&[]),
            );
            let at = address(b, arena, offset);
            let size = b.load(Width::Word, at, Offset::Words(0));
            let refs = b.load(Width::Word, at, Offset::Words(1));
            let nil = number(b, 0);
            let free = eq(b, refs, nil);
            b.if_(
                free,
                &[],
                |b| {
                    let merged = b.call_one(coalesce, &[arena, offset, end]);
                    b.store(Width::Word, at, Offset::Words(0), merged);
                    let small = lt(b, merged, wanted);
                    b.if_(
                        small,
                        &[],
                        |b| {
                            let next = add(b, offset, merged);
                            b.continue_(&[arena, next]);
                        },
                        |b| {
                            b.call(claim, &[at, wanted, cap]);
                            let taken = b.load(Width::Word, at, Offset::Words(0));
                            let after = add(b, offset, taken);
                            let named = b.convert(W, arena);
                            let kept = b.address_of(kept_at);
                            b.store(Width::Word, kept, Offset::Words(0), named);
                            b.store(Width::Word, kept, Offset::Words(1), after);
                            let one = number(b, 1);
                            b.break_(&[at, one]);
                        },
                    );
                },
                |b| {
                    let next = add(b, offset, size);
                    b.continue_(&[arena, next]);
                },
            );
        });
        let (block, met) = (found[0], found[1]);
        let one = number(b, 1);
        let met = eq(b, met, one);
        b.if_(met, &[], |b| b.ret(&[block]), |b| b.yield_(&[]));
        // Nothing had room: a new arena, at least as large as the heap.
        let total = b.load(Width::Word, kept, Offset::Words(3));
        let header_bytes = number(b, size64(start));
        let least = add(b, wanted, header_bytes);
        let smaller = lt(b, least, total);
        let chunk = b.if_(
            smaller,
            &[W],
            |b| b.yield_(&[total]),
            |b| b.yield_(&[least]),
        )[0];
        // A target that has no more answers an address the chunk would run
        // past the end of the address space from. Refused as much as the
        // heap so far, it is asked for as much as is wanted.
        let refused = |b: &mut Builder<'_>, page: ValueId, chunk: ValueId| {
            let top = number(b, max);
            let room = sub(b, top, chunk);
            let from = b.convert(W, page);
            lt(b, room, from)
        };
        let page = b.call_one(grow, &[chunk]);
        let first_refused = refused(b, page, chunk);
        let got = b.if_(
            first_refused,
            &[A, W],
            |b| {
                let page = b.call_one(grow, &[least]);
                b.yield_(&[page, least]);
            },
            |b| b.yield_(&[page, chunk]),
        );
        let (page, chunk) = (got[0], got[1]);
        let refused = refused(b, page, chunk);
        b.if_(
            refused,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let from = b.convert(W, page);
        let after_first = b.load(Width::Word, first, Offset::Words(0));
        let grown = add(b, total, chunk);
        b.store(Width::Word, kept, Offset::Words(3), grown);
        // Where the target hands out memory in one run, what it grants
        // begins where the latest arena ends, and that arena is made longer
        // rather than a new one begun: blocks either side of where they
        // met are then one run, which a later search joins.
        let latest = b.convert(A, after_first);
        let any = lt(b, nil, after_first);
        let extends = b.if_(
            any,
            &[W],
            |b| {
                let end = b.load(Width::Word, latest, Offset::Words(1));
                let ends_at = add(b, after_first, end);
                let joins = eq(b, ends_at, from);
                b.yield_(&[joins]);
            },
            |b| b.yield_(&[nil]),
        )[0];
        b.if_(
            extends,
            &[],
            |b| {
                let end = b.load(Width::Word, latest, Offset::Words(1));
                let longer = add(b, end, chunk);
                b.store(Width::Word, latest, Offset::Words(1), longer);
                let nil = number(b, 0);
                b.store(Width::Word, page, Offset::Words(0), chunk);
                b.store(Width::Word, page, Offset::Words(1), nil);
                b.call(claim, &[page, wanted, cap]);
                let taken = b.load(Width::Word, page, Offset::Words(0));
                let after = add(b, end, taken);
                let kept = b.address_of(kept_at);
                b.store(Width::Word, kept, Offset::Words(0), after_first);
                b.store(Width::Word, kept, Offset::Words(1), after);
                b.ret(&[page]);
            },
            |b| b.yield_(&[]),
        );
        b.store(Width::Word, page, Offset::Words(0), after_first);
        b.store(Width::Word, first, Offset::Words(0), from);
        b.store(Width::Word, page, Offset::Words(1), chunk);
        let at = address(b, page, header_bytes);
        let blocks = sub(b, chunk, header_bytes);
        let nil = number(b, 0);
        b.store(Width::Word, at, Offset::Words(0), blocks);
        b.store(Width::Word, at, Offset::Words(1), nil);
        let one = number(b, 1);
        let arenas = add(b, arenas, one);
        b.store(Width::Word, kept, Offset::Words(2), arenas);
        b.call(claim, &[at, wanted, cap]);
        let taken = b.load(Width::Word, at, Offset::Words(0));
        let after = add(b, header_bytes, taken);
        b.store(Width::Word, kept, Offset::Words(0), from);
        b.store(Width::Word, kept, Offset::Words(1), after);
        b.ret(&[at]);
    });
    allocate
}

fn coalescing(p: &mut Program) -> FunctionId {
    let f = declare(p, "nat.coalesce", &[A, W, W], &[W]);
    p.define(f, |b, args| {
        let base = args[0];
        let offset = args[1];
        let pool = args[2];
        let at = address(b, base, offset);
        let size = b.load(Width::Word, at, Offset::Words(0));
        let nil = number(b, 0);
        let merged = b.loop_(&[size], &[W], |b, state| {
            let size = state[0];
            let next = add(b, offset, size);
            let end = eq(b, next, pool);
            b.if_(end, &[], |b| b.break_(&[size]), |b| b.yield_(&[]));
            let after = address(b, base, next);
            let refs = b.load(Width::Word, after, Offset::Words(1));
            let free = eq(b, refs, nil);
            b.if_(
                free,
                &[],
                |b| {
                    let more = b.load(Width::Word, after, Offset::Words(0));
                    let total = add(b, size, more);
                    b.continue_(&[total]);
                },
                |b| b.break_(&[size]),
            );
        })[0];
        b.ret(&[merged]);
    });
    f
}

fn claiming(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.claim", &[A, W, W], &[]);
    p.define(f, |b, args| {
        let at = args[0];
        let wanted = args[1];
        let cap = args[2];
        let merged = b.load(Width::Word, at, Offset::Words(0));
        let rest = sub(b, merged, wanted);
        let minimum = number(b, size64(4 * word));
        let tiny = lt(b, rest, minimum);
        let nil = number(b, 0);
        let one = number(b, 1);
        b.if_(
            tiny,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let tail = address(b, at, wanted);
                b.store(Width::Word, tail, Offset::Words(0), rest);
                b.store(Width::Word, tail, Offset::Words(1), nil);
                b.store(Width::Word, tail, Offset::Words(2), nil);
                b.store(Width::Word, at, Offset::Words(0), wanted);
                b.yield_(&[]);
            },
        );
        b.store(Width::Word, at, Offset::Words(1), one);
        set_length(b, at, cap);
        b.ret(&[]);
    });
    f
}

/// Write nought to the first `len` digits of an object, for a routine that
/// reads its output's digits before it has written them all.
fn clear(b: &mut Builder<'_>, out: ValueId, len: ValueId, word: usize) {
    let nil = number(b, 0);
    let one = number(b, 1);
    b.loop_(&[nil], &[], |b, state| {
        let i = state[0];
        let done = eq(b, i, len);
        b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
        write_digit(b, out, i, nil, word);
        let next = add(b, i, one);
        b.continue_(&[next]);
    });
}

fn digit_reader(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.digit", &[A, W], &[W]);
    p.define(f, |b, args| {
        let len = length(b, args[0]);
        let inside = lt(b, args[1], len);
        let value = b.if_(
            inside,
            &[W],
            |b| {
                let digit = read_digit(b, args[0], args[1], word);
                b.yield_(&[digit]);
            },
            |b| {
                let zero = number(b, 0);
                b.yield_(&[zero]);
            },
        )[0];
        b.ret(&[value]);
    });
    f
}

fn trimming(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.trim", &[A], &[]);
    p.define(f, |b, args| {
        let a = args[0];
        let len = length(b, a);
        let zero = number(b, 0);
        let one = number(b, 1);
        let n = b.loop_(&[len], &[W], |b, state| {
            let n = state[0];
            let empty = eq(b, n, zero);
            b.if_(empty, &[], |b| b.break_(&[n]), |b| b.yield_(&[]));
            let last = sub(b, n, one);
            let digit = read_digit(b, a, last, word);
            let empty = eq(b, digit, zero);
            b.if_(empty, &[], |b| b.continue_(&[last]), |b| b.break_(&[n]));
        })[0];
        set_length(b, a, n);
        b.ret(&[]);
    });
    f
}

/// Trim an object a routine has written, and answer the value it holds:
/// the object itself, or the immediate its number is where it is small.
fn finishing(
    p: &mut Program,
    (trim, narrow): (FunctionId, FunctionId),
    release: FunctionId,
    half: u64,
) -> FunctionId {
    let f = declare(p, "nat.finish", &[A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        b.call(trim, &[a]);
        let len = length(b, a);
        // Two digits is more than half a word holds.
        let one = number(b, 1);
        let wide = lt(b, one, len);
        b.if_(
            wide,
            &[],
            |b| {
                let named = handle(b, a);
                b.ret(&[named]);
            },
            |b| b.yield_(&[]),
        );
        let value = b.call_one(narrow, &[a]);
        let top = number(b, half);
        let fits = lt(b, value, top);
        b.if_(
            fits,
            &[],
            |b| {
                b.call(release, &[a]);
                let held = small_word(b, value);
                b.ret(&[held]);
            },
            |b| b.yield_(&[]),
        );
        let named = handle(b, a);
        b.ret(&[named]);
    });
    f
}

/// Allocate an object for `count` digits. Its address is even, as every
/// block's is, so it is never taken for an immediate.
fn digits_allocation(
    p: &mut Program,
    (alloc, fail): (FunctionId, FunctionId),
    (word, most): (usize, u64),
) -> FunctionId {
    let f = declare(p, "nat.digits", &[W], &[A]);
    p.define(f, |b, args| {
        let count = args[0];
        let limit = number(b, most);
        let huge = lt(b, limit, count);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let bytes = number(b, size64(word));
        let bytes = b.binary(Binary::Mul, count, bytes);
        let out = b.call_one(alloc, &[bytes]);
        // No request is for none, which would be the shared empty object.
        set_length(b, out, count);
        b.ret(&[out]);
    });
    f
}

/// An object holding a word, trimmed but never read back as an immediate,
/// for a routine that reads digits of a number an immediate holds.
fn boxing(p: &mut Program, digits: FunctionId, trim: FunctionId, word: usize) -> FunctionId {
    let f = declare(p, "nat.box", &[W], &[A]);
    p.define(f, |b, args| {
        let one = number(b, 1);
        let out = b.call_one(digits, &[one]);
        let nil = number(b, 0);
        write_digit(b, out, nil, args[0], word);
        b.call(trim, &[out]);
        b.ret(&[out]);
    });
    f
}

fn comparison(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.compare_digits", &[A, A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let zero = number(b, 0);
        let one = number(b, 1);
        let two = number(b, 2);
        let less = lt(b, la, lc);
        b.if_(less, &[], |b| b.ret(&[zero]), |b| b.yield_(&[]));
        let greater = lt(b, lc, la);
        b.if_(greater, &[], |b| b.ret(&[two]), |b| b.yield_(&[]));
        let order = b.loop_(&[la], &[W], |b, state| {
            let n = state[0];
            let empty = eq(b, n, zero);
            b.if_(empty, &[], |b| b.break_(&[one]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let x = read_digit(b, a, i, word);
            let y = read_digit(b, c, i, word);
            let less = lt(b, x, y);
            b.if_(less, &[], |b| b.break_(&[zero]), |b| b.yield_(&[]));
            let greater = lt(b, y, x);
            b.if_(greater, &[], |b| b.break_(&[two]), |b| b.continue_(&[i]));
        })[0];
        b.ret(&[order]);
    });
    f
}

#[expect(
    clippy::too_many_lines,
    reason = "one generated carry-propagation routine"
)]
fn addition(p: &mut Program, storage: Storage, digit: FunctionId) -> FunctionId {
    let Storage {
        alloc,
        finish,
        fail,
        most,
        word,
        ..
    } = storage;
    let f = declare(p, "nat.add_digits", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let less = lt(b, la, lc);
        let len = b.if_(less, &[W], |b| b.yield_(&[lc]), |b| b.yield_(&[la]))[0];
        let limit = number(b, most);
        let fits = lt(b, len, limit);
        b.if_(
            fits,
            &[],
            |b| b.yield_(&[]),
            |b| {
                b.call(fail, &[]);
            },
        );
        let one = number(b, 1);
        let zero = number(b, 0);
        let cap = add(b, len, one);
        let out = b.call_one(alloc, &[cap]);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let i = state[0];
            let carry = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = b.call_one(digit, &[a, i]);
            let y = b.call_one(digit, &[c, i]);
            let (sum, carry) = add_carry(b, x, y, carry);
            write_digit(b, out, i, sum, word);
            let next = add(b, i, one);
            b.continue_(&[next, carry]);
        })[0];
        write_digit(b, out, len, carry, word);
        let result = b.call_one(finish, &[out]);
        b.ret(&[result]);
    });
    f
}

/// A bitwise operation on two objects, a digit of each at a time: as many
/// digits as the longer has, since a digit past the shorter's last is
/// nought, and trimmed after, since an and or an exclusive or may clear the
/// top ones.
fn bitwise_digits(
    p: &mut Program,
    storage: Storage,
    digit: FunctionId,
    (op, name): (Binary, &str),
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        ..
    } = storage;
    let f = declare(p, &format!("nat.{name}_digits"), &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let less = lt(b, la, lc);
        let len = b.if_(less, &[W], |b| b.yield_(&[lc]), |b| b.yield_(&[la]))[0];
        let one = number(b, 1);
        let zero = number(b, 0);
        // A digit more than the answer needs, nought, as a sum's carry
        // is: an operand may be a nought with no digits, and no request
        // is for none.
        let cap = add(b, len, one);
        let out = b.call_one(alloc, &[cap]);
        b.loop_(&[zero], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = b.call_one(digit, &[a, i]);
            let y = b.call_one(digit, &[c, i]);
            let answer = b.binary(op, x, y);
            write_digit(b, out, i, answer, word);
            let next = add(b, i, one);
            b.continue_(&[next]);
        });
        write_digit(b, out, len, zero, word);
        let result = b.call_one(finish, &[out]);
        b.ret(&[result]);
    });
    f
}

// Mutates a unique scratch object, known >= the borrowed right operand.
fn subtracting(p: &mut Program, digit: FunctionId, trim: FunctionId, word: usize) -> FunctionId {
    let f = declare(p, "nat.subtract_into", &[A, A], &[]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let len = length(b, a);
        let zero = number(b, 0);
        let one = number(b, 1);
        b.loop_(&[zero, zero], &[], |b, state| {
            let i = state[0];
            let borrow = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, a, i, word);
            let y = b.call_one(digit, &[c, i]);
            let (low, borrow) = sub_borrow(b, x, y, borrow);
            write_digit(b, a, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, borrow]);
        });
        b.call(trim, &[a]);
        b.ret(&[]);
    });
    f
}

fn monus(
    p: &mut Program,
    storage: Storage,
    compare: FunctionId,
    subtract: FunctionId,
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        ..
    } = storage;
    let f = declare(p, "nat.sub_digits", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let order = b.call_one(compare, &[a, c]);
        let two = number(b, 2);
        let greater = eq(b, order, two);
        b.if_(
            greater,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let z = small(b, 0);
                b.ret(&[z]);
            },
        );
        let len = length(b, a);
        let out = b.call_one(alloc, &[len]);
        let zero = number(b, 0);
        let one = number(b, 1);
        b.loop_(&[zero], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, a, i, word);
            write_digit(b, out, i, x, word);
            let next = add(b, i, one);
            b.continue_(&[next]);
        });
        b.call(subtract, &[out, c]);
        let result = b.call_one(finish, &[out]);
        b.ret(&[result]);
    });
    f
}

fn multiply_row(p: &mut Program, word: usize) -> FunctionId {
    let row = declare(p, "nat.multiply_row", &[A, A, A, W], &[]);
    p.define(row, |b, args| {
        let a = args[0];
        let c = args[1];
        let out = args[2];
        let i = args[3];
        let x = read_digit(b, a, i, word);
        let len = length(b, c);
        let zero = number(b, 0);
        let one = number(b, 1);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let j = state[0];
            let carry = state[1];
            let done = eq(b, j, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let y = read_digit(b, c, j, word);
            let at = add(b, i, j);
            let acc = read_digit(b, out, at, word);
            // (B-1)(B-1) + (B-1) + (B-1) is B*B - 1: two digits, so the
            // high digit and what adding carried is one digit again.
            let (low, high) = mul_wide(b, x, y, word_bits(word));
            let (sum, carried) = add_carry(b, low, acc, carry);
            write_digit(b, out, at, sum, word);
            let next = add(b, j, one);
            let carry = add(b, high, carried);
            b.continue_(&[next, carry]);
        })[0];
        let at = add(b, i, len);
        write_digit(b, out, at, carry, word);
        b.ret(&[]);
    });
    row
}

#[expect(
    clippy::too_many_lines,
    reason = "checks and generated outer product loop"
)]
fn multiplication(p: &mut Program, storage: Storage) -> FunctionId {
    let Storage {
        alloc,
        finish,
        fail,
        most,
        word,
        ..
    } = storage;
    let row = multiply_row(p, word);
    let f = declare(p, "nat.mul_digits", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let nil = number(b, 0);
        let one = number(b, 1);
        for len in [la, lc] {
            let empty = eq(b, len, nil);
            b.if_(
                empty,
                &[],
                |b| {
                    let z = small(b, 0);
                    b.ret(&[z]);
                },
                |b| b.yield_(&[]),
            );
        }
        // Check each component before addition, including large static inputs.
        let limit = number(b, most);
        let huge = lt(b, limit, la);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let room = sub(b, limit, la);
        let huge = lt(b, room, lc);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let cap = add(b, la, lc);
        let out = b.call_one(alloc, &[cap]);
        // Each row adds into what the rows before it wrote.
        clear(b, out, cap, word);
        b.loop_(&[nil], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, la);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            b.call(row, &[a, c, out, i]);
            let next = add(b, i, one);
            b.continue_(&[next]);
        });
        let result = b.call_one(finish, &[out]);
        b.ret(&[result]);
    });
    f
}

/// The quotient of the two digits `high:low` by `divisor`, whose top bit
/// is set and which is more than `high`, so that the quotient is a digit:
/// Hacker's Delight's `divlu`, a half digit at a time, so that nothing it
/// divides or multiplies is wider than a word.
fn dividing_word(p: &mut Program, word: usize) -> FunctionId {
    let bits = u16::try_from(word * 4).expect("half a word's bits fit u16");
    let f = declare(p, "nat.divide_word", &[W, W, W], &[W]);
    p.define(f, |b, args| {
        let (high, low, divisor) = (args[0], args[1], args[2]);
        let base = number(b, 1 << bits);
        let upper = b.shift(W, Direction::Down, divisor, bits);
        let lower = b.binary(Binary::Mod, divisor, base);
        let first = b.shift(W, Direction::Down, low, bits);
        let second = b.binary(Binary::Mod, low, base);
        let halves = (upper, lower);
        let q1 = half_quotient(b, (high, first), halves, bits);
        // What is left is less than the divisor, so the word it wraps to
        // is exactly it.
        let lifted = b.shift(W, Direction::Up, high, bits);
        let lifted = add(b, lifted, first);
        let taken = b.binary(Binary::Mul, q1, divisor);
        let rest = sub(b, lifted, taken);
        let q0 = half_quotient(b, (rest, second), halves, bits);
        let q = b.shift(W, Direction::Up, q1, bits);
        let q = add(b, q, q0);
        b.ret(&[q]);
    });
    f
}

/// One half digit of `divlu`'s quotient: `high` and the next half digit
/// `next`, divided by the divisor's halves. The estimate from the upper
/// half alone is too big by two at most, and is brought down while it is
/// at least a half digit's base or its product with the lower half passes
/// what is left.
fn half_quotient(
    b: &mut Builder<'_>,
    (high, next): (ValueId, ValueId),
    (upper, lower): (ValueId, ValueId),
    bits: u16,
) -> ValueId {
    let base = number(b, 1 << bits);
    let guess = b.binary(Binary::Div, high, upper);
    let product = b.binary(Binary::Mul, guess, upper);
    let rest = sub(b, high, product);
    b.loop_(&[guess, rest], &[W], |b, state| {
        let (q, r) = (state[0], state[1]);
        let most = number(b, (1 << bits) - 1);
        let wide = lt(b, most, q);
        let over = b.if_(
            wide,
            &[W],
            |b| {
                let yes = number(b, 1);
                b.yield_(&[yes]);
            },
            |b| {
                // `r` is below the base here, so this is a word.
                let product = b.binary(Binary::Mul, q, lower);
                let lifted = b.shift(W, Direction::Up, r, bits);
                let lifted = add(b, lifted, next);
                let over = lt(b, lifted, product);
                b.yield_(&[over]);
            },
        )[0];
        let one = number(b, 1);
        let fine = lt(b, over, one);
        b.if_(fine, &[], |b| b.break_(&[q]), |b| b.yield_(&[]));
        let q = sub(b, q, one);
        let r = add(b, r, upper);
        let small = lt(b, r, base);
        b.if_(small, &[], |b| b.continue_(&[q, r]), |b| b.break_(&[q]));
    })[0]
}

/// The power of two taking `top`, a digit that is not nought, to one whose
/// top bit is set: what both operands of a division are scaled by.
fn normalizing(p: &mut Program, half: u64) -> FunctionId {
    let f = declare(p, "nat.normal", &[W], &[W]);
    p.define(f, |b, args| {
        let one = number(b, 1);
        let two = number(b, 2);
        let pow = b.loop_(&[one, args[0]], &[W], |b, state| {
            let (pow, x) = (state[0], state[1]);
            let below = number(b, half - 1);
            let set = lt(b, below, x);
            b.if_(set, &[], |b| b.break_(&[pow]), |b| b.yield_(&[]));
            let pow = b.binary(Binary::Mul, pow, two);
            let x = b.binary(Binary::Mul, x, two);
            b.continue_(&[pow, x]);
        })[0];
        b.ret(&[pow]);
    });
    f
}

/// Write `from`'s digits times `pow`, a power of two, into `to`: what
/// carries out of the last. A digit times a power of two is its bits moved
/// up, so the carry in fills bits the product left nought.
fn scaling(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.scale", &[A, A, W], &[W]);
    p.define(f, |b, args| {
        let (from, to, pow) = (args[0], args[1], args[2]);
        let len = length(b, from);
        let zero = number(b, 0);
        let one = number(b, 1);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let (i, carry) = (state[0], state[1]);
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = read_digit(b, from, i, word);
            let (low, high) = mul_wide(b, x, pow, word_bits(word));
            let digit = add(b, low, carry);
            write_digit(b, to, i, digit, word);
            let next = add(b, i, one);
            b.continue_(&[next, high]);
        })[0];
        b.ret(&[carry]);
    });
    f
}

/// The first `len` digits of `r`, divided by `pow`, a power of two, in
/// place: each digit's bits moved down, and the next one's low bits moved
/// in above them. `r` has a digit past those.
fn unscaling(p: &mut Program, half: u64, word: usize) -> FunctionId {
    let f = declare(p, "nat.unscale", &[A, W, W], &[]);
    p.define(f, |b, args| {
        let (r, len, pow) = (args[0], args[1], args[2]);
        let worth = worth(b, half, pow);
        let zero = number(b, 0);
        let one = number(b, 1);
        b.loop_(&[zero], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, r, i, word);
            let next = add(b, i, one);
            let y = read_digit(b, r, next, word);
            let moved = b.binary(Binary::Div, x, pow);
            let rest = b.binary(Binary::Mul, y, worth);
            let digit = add(b, moved, rest);
            write_digit(b, r, i, digit, word);
            b.continue_(&[next]);
        });
        b.ret(&[]);
    });
    f
}

/// Knuth's estimate of the quotient digit at `j`: the top two digits there
/// of the scaled remainder `u`, divided by the scaled divisor `v`'s top
/// digit, then brought down while its product with `v`'s next digit passes
/// what the three top digits of `u` leave. It is then at most one too big.
fn estimating(p: &mut Program, divide: FunctionId, word: usize) -> FunctionId {
    let f = declare(p, "nat.estimate", &[A, A, W], &[W]);
    p.define(f, |b, args| {
        let (u, v, j) = (args[0], args[1], args[2]);
        let n = length(b, v);
        let one = number(b, 1);
        let at = add(b, j, n);
        let u2 = read_digit(b, u, at, word);
        let at = sub(b, at, one);
        let u1 = read_digit(b, u, at, word);
        let top = sub(b, n, one);
        let v1 = read_digit(b, v, top, word);
        let [q, r, over] = first_estimate(b, divide, (u2, u1, v1), word);
        // A remainder past a digit, or no next digit, settles it.
        let two = number(b, 2);
        let short = lt(b, n, two);
        let settled = add(b, over, short);
        let zero = number(b, 0);
        let open = eq(b, settled, zero);
        b.if_(open, &[], |b| b.yield_(&[]), |b| b.ret(&[q]));
        let next = sub(b, top, one);
        let v2 = read_digit(b, v, next, word);
        let at = sub(b, at, one);
        let u0 = read_digit(b, u, at, word);
        let q = corrected(b, [q, r], (v1, v2, u0), word);
        b.ret(&[q]);
    });
    f
}

/// The estimate from the top two digits `u2:u1` of what is left and the
/// top digit `v1` of the divisor, the remainder it leaves, and one where
/// that remainder is past a digit. The top digit of what is left is at most
/// the divisor's; where it is the divisor's, the quotient digit is the
/// largest there is.
fn first_estimate(
    b: &mut Builder<'_>,
    divide: FunctionId,
    (u2, u1, v1): (ValueId, ValueId, ValueId),
    word: usize,
) -> [ValueId; 3] {
    let below = lt(b, u2, v1);
    // Two values cross the edge, which is all the narrowest target carries.
    let start = b.if_(
        below,
        &[W, W],
        |b| {
            let q = b.call_one(divide, &[u2, u1, v1]);
            let taken = b.binary(Binary::Mul, q, v1);
            let r = sub(b, u1, taken);
            b.yield_(&[q, r]);
        },
        |b| {
            let q = number(b, u64::MAX >> (64 - 8 * word));
            let r = add(b, u1, v1);
            b.yield_(&[q, r]);
        },
    );
    let (q, r) = (start[0], start[1]);
    // Only the largest estimate's remainder can pass a digit: `u1 + v1`
    // wrapping, which leaves less than `u1`.
    let wrapped = lt(b, r, u1);
    let one = number(b, 1);
    let largest = sub(b, one, below);
    let over = b.binary(Binary::Mul, wrapped, largest);
    [q, r, over]
}

/// The estimate, and `r` it leaves, as `start` holds them, brought down while its product with the
/// divisor's next digit `v2` passes `r` and the next digit `u0` of what is
/// left, or until `r` passes a digit. Twice at most.
fn corrected(
    b: &mut Builder<'_>,
    start: [ValueId; 2],
    (v1, v2, u0): (ValueId, ValueId, ValueId),
    word: usize,
) -> ValueId {
    b.loop_(&start, &[W], |b, state| {
        let (q, r) = (state[0], state[1]);
        let (low, high) = mul_wide(b, q, v2, word_bits(word));
        let past = lt(b, r, high);
        let level = eq(b, high, r);
        let low_past = lt(b, u0, low);
        let level_past = b.binary(Binary::Mul, level, low_past);
        let over = add(b, past, level_past);
        let one = number(b, 1);
        let fine = lt(b, over, one);
        b.if_(fine, &[], |b| b.break_(&[q]), |b| b.yield_(&[]));
        let q = sub(b, q, one);
        let grown = add(b, r, v1);
        let wrapped = lt(b, grown, r);
        b.if_(
            wrapped,
            &[],
            |b| b.break_(&[q]),
            |b| b.continue_(&[q, grown]),
        );
    })[0]
}

/// Take `q` times `v` from the digits of `u` from `j`, as many as `v` has:
/// what is still to be taken from the digit after them.
fn multiplying_out(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.multiply_out", &[A, A, W, W], &[W]);
    p.define(f, |b, args| {
        let (u, v, j, q) = (args[0], args[1], args[2], args[3]);
        let n = length(b, v);
        let zero = number(b, 0);
        let one = number(b, 1);
        let owed = b.loop_(&[zero, zero], &[W], |b, state| {
            let (i, owed) = (state[0], state[1]);
            let done = eq(b, i, n);
            b.if_(done, &[], |b| b.break_(&[owed]), |b| b.yield_(&[]));
            let y = read_digit(b, v, i, word);
            let (low, high) = mul_wide(b, q, y, word_bits(word));
            let at = add(b, i, j);
            let x = read_digit(b, u, at, word);
            let (digit, borrowed) = sub_borrow(b, x, low, owed);
            write_digit(b, u, at, digit, word);
            let next = add(b, i, one);
            let owed = add(b, high, borrowed);
            b.continue_(&[next, owed]);
        })[0];
        b.ret(&[owed]);
    });
    f
}

/// Add `v` back to the digits of `u` from `j`, where a quotient digit took
/// one `v` too many: what carries out of the last.
fn adding_back(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.add_back", &[A, A, W], &[W]);
    p.define(f, |b, args| {
        let (u, v, j) = (args[0], args[1], args[2]);
        let n = length(b, v);
        let zero = number(b, 0);
        let one = number(b, 1);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let (i, carry) = (state[0], state[1]);
            let done = eq(b, i, n);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let at = add(b, i, j);
            let x = read_digit(b, u, at, word);
            let y = read_digit(b, v, i, word);
            let (sum, carry) = add_carry(b, x, y, carry);
            write_digit(b, u, at, sum, word);
            let next = add(b, i, one);
            b.continue_(&[next, carry]);
        })[0];
        b.ret(&[carry]);
    });
    f
}

/// The routines one quotient digit of a long division calls.
#[derive(Clone, Copy)]
struct Steps {
    estimate: FunctionId,
    multiply_out: FunctionId,
    add_back: FunctionId,
}

/// The quotient digit at `j` of dividing the scaled `u` by the scaled `v`,
/// taking that many `v` from `u`, as Knuth's algorithm D does.
fn quotient_digit(
    b: &mut Builder<'_>,
    steps: Steps,
    (u, v, j): (ValueId, ValueId, ValueId),
    word: usize,
) -> ValueId {
    let q = b.call_one(steps.estimate, &[u, v, j]);
    let owed = b.call_one(steps.multiply_out, &[u, v, j, q]);
    let n = length(b, v);
    let top = add(b, j, n);
    let x = read_digit(b, u, top, word);
    let rest = sub(b, x, owed);
    write_digit(b, u, top, rest, word);
    // Taking too much leaves the top digit short; the estimate was one too
    // big, and one `v` goes back.
    let short = lt(b, x, owed);
    b.if_(
        short,
        &[W],
        |b| {
            let carry = b.call_one(steps.add_back, &[u, v, j]);
            let x = read_digit(b, u, top, word);
            let x = add(b, x, carry);
            write_digit(b, u, top, x, word);
            let one = number(b, 1);
            let q = sub(b, q, one);
            b.yield_(&[q]);
        },
        |b| b.yield_(&[q]),
    )[0]
}

/// What every division shares: dividing two digits by one, the power of
/// two that sets a digit's top bit, and short division by one digit.
#[derive(Clone, Copy)]
struct Divisions {
    two_by_one: FunctionId,
    normal: FunctionId,
    short: FunctionId,
}

impl Divisions {
    fn append(p: &mut Program, storage: Storage) -> Self {
        let two_by_one = dividing_word(p, storage.word);
        let normal = normalizing(p, storage.half);
        Self {
            two_by_one,
            normal,
            short: short_division(p, storage, (normal, two_by_one)),
        }
    }
}

/// Division by one digit, `d`, a digit of the quotient at a time from the
/// top: the dividend is scaled as it is read, each digit from itself and
/// the one below, so nothing but the quotient is allocated, and nothing at
/// all for a remainder. This is what writing a number in decimal asks.
fn short_division(
    p: &mut Program,
    storage: Storage,
    (normal, divide): (FunctionId, FunctionId),
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        half,
        ..
    } = storage;
    let from_word = promotion(p, storage);
    let f = declare(p, "nat.divide_short", &[A, W, W], &[A]);
    p.define(f, |b, args| {
        let (a, d, remainder) = (args[0], args[1], args[2]);
        nought_if_empty(b, a);
        let pow = b.call_one(normal, &[d]);
        let q = quotient_room(b, alloc, (a, remainder));
        let short = Shortened {
            a,
            q,
            remainder,
            pow,
            worth: worth(b, half, pow),
            divisor: b.binary(Binary::Mul, d, pow),
        };
        let r = short_digits(b, short, divide, word);
        let out = b.if_(
            remainder,
            &[A],
            |b| {
                // What is left, scaled back: a word, held as a natural.
                let r = b.binary(Binary::Div, r, pow);
                let out = b.call_one(from_word, &[r]);
                b.yield_(&[out]);
            },
            |b| {
                let out = b.call_one(finish, &[q]);
                b.yield_(&[out]);
            },
        )[0];
        b.ret(&[out]);
    });
    f
}

/// Answer nought where `a` is an object with no digits, which is nought,
/// and so is all it divides to.
fn nought_if_empty(b: &mut Builder<'_>, a: ValueId) {
    let len = length(b, a);
    let zero = number(b, 0);
    let empty = eq(b, len, zero);
    b.if_(
        empty,
        &[],
        |b| {
            let none = small(b, 0);
            b.ret(&[none]);
        },
        |b| b.yield_(&[]),
    );
}

/// Room for the quotient of dividing `a`, as many digits as it has, where
/// more than the `remainder` is wanted; otherwise an immediate nothing
/// writes to.
fn quotient_room(
    b: &mut Builder<'_>,
    alloc: FunctionId,
    (a, remainder): (ValueId, ValueId),
) -> ValueId {
    b.if_(
        remainder,
        &[A],
        |b| {
            let none = small(b, 0);
            b.yield_(&[none]);
        },
        |b| {
            let len = length(b, a);
            let q = b.call_one(alloc, &[len]);
            b.yield_(&[q]);
        },
    )[0]
}

/// What a short division's loop reads and writes: the dividend `a`, the quotient
/// `q` it writes unless it wants only the `remainder`, the power `pow` the
/// digit was scaled by, what a digit is `worth` in the next one up, and the
/// scaled `divisor`.
#[derive(Clone, Copy)]
struct Shortened {
    a: ValueId,
    q: ValueId,
    remainder: ValueId,
    pow: ValueId,
    worth: ValueId,
    divisor: ValueId,
}

/// A short division's digits, from the top: what is left of the scaled
/// dividend at the end.
fn short_digits(b: &mut Builder<'_>, short: Shortened, divide: FunctionId, word: usize) -> ValueId {
    let Shortened {
        a,
        q,
        remainder,
        pow,
        worth,
        divisor,
    } = short;
    let len = length(b, a);
    let zero = number(b, 0);
    let one = number(b, 1);
    let last = sub(b, len, one);
    let x = read_digit(b, a, last, word);
    let first = b.binary(Binary::Div, x, worth);
    b.loop_(&[len, first], &[W], |b, state| {
        let (n, r) = (state[0], state[1]);
        let done = eq(b, n, zero);
        b.if_(done, &[], |b| b.break_(&[r]), |b| b.yield_(&[]));
        let i = sub(b, n, one);
        let digit = scaled_digit(b, (a, i), (pow, worth), word);
        let quotient = b.call_one(divide, &[r, digit, divisor]);
        let taken = b.binary(Binary::Mul, quotient, divisor);
        let r = sub(b, digit, taken);
        b.if_(
            remainder,
            &[],
            |b| b.yield_(&[]),
            |b| {
                write_digit(b, q, i, quotient, word);
                b.yield_(&[]);
            },
        );
        b.continue_(&[i, r]);
    })[0]
}

/// Digit `i` of `a` scaled by `pow`: its own bits moved up, and the top
/// bits of the digit below moved in, which dividing that by `worth` gives.
fn scaled_digit(
    b: &mut Builder<'_>,
    (a, i): (ValueId, ValueId),
    (pow, worth): (ValueId, ValueId),
    word: usize,
) -> ValueId {
    let x = read_digit(b, a, i, word);
    let moved = b.binary(Binary::Mul, x, pow);
    let zero = number(b, 0);
    let bottom = eq(b, i, zero);
    let below = b.if_(
        bottom,
        &[W],
        |b| b.yield_(&[zero]),
        |b| {
            let one = number(b, 1);
            let lower = sub(b, i, one);
            let y = read_digit(b, a, lower, word);
            let up = b.binary(Binary::Div, y, worth);
            b.yield_(&[up]);
        },
    )[0];
    add(b, moved, below)
}

/// What a digit is worth in the one below it once both are scaled by
/// `pow`, a power of two: the base over `pow`. Where `pow` is one that is
/// the base, which wraps to nought, and a quotient by nought is nought, so
/// nothing moves between digits, as nothing should.
fn worth(b: &mut Builder<'_>, half: u64, pow: ValueId) -> ValueId {
    let top = number(b, half);
    let two = number(b, 2);
    let worth = b.binary(Binary::Div, top, pow);
    b.binary(Binary::Mul, worth, two)
}

/// Long division a digit at a time. Both operands are scaled by the power
/// of two setting the divisor's top bit, which is what makes each quotient
/// digit's estimate close; the remainder is scaled back.
#[expect(
    clippy::too_many_lines,
    reason = "one generated div/mod routine and its scratch lifetimes"
)]
fn division(
    p: &mut Program,
    storage: Storage,
    (compare, retain): (FunctionId, FunctionId),
    divisions: Divisions,
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        half,
        release,
        ..
    } = storage;
    let Divisions {
        two_by_one,
        normal,
        short,
    } = divisions;
    let scale = scaling(p, word);
    let unscale = unscaling(p, half, word);
    let steps = Steps {
        estimate: estimating(p, two_by_one, word),
        multiply_out: multiplying_out(p, word),
        add_back: adding_back(p, word),
    };
    let f = declare(p, "nat.divmod", &[A, A, W], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let remainder = args[2];
        let la = length(b, a);
        let lc = length(b, c);
        let nil = number(b, 0);
        let one = number(b, 1);
        let empty = eq(b, lc, nil);
        let order = b.call_one(compare, &[a, c]);
        let less = eq(b, order, nil);
        // Both trivial paths borrow `a` and must create an owned result.
        for trivial in [empty, less] {
            b.if_(
                trivial,
                &[],
                |b| {
                    let answer = b.if_(
                        remainder,
                        &[A],
                        |b| {
                            let kept = b.call_one(retain, &[a]);
                            let kept = handle(b, kept);
                            b.yield_(&[kept]);
                        },
                        |b| {
                            let z = small(b, 0);
                            b.yield_(&[z]);
                        },
                    )[0];
                    b.ret(&[answer]);
                },
                |b| b.yield_(&[]),
            );
        }
        let last = sub(b, lc, one);
        let top = read_digit(b, c, last, word);
        let single = eq(b, lc, one);
        b.if_(
            single,
            &[],
            |b| {
                let out = b.call_one(short, &[a, top, remainder]);
                b.ret(&[out]);
            },
            |b| b.yield_(&[]),
        );
        let pow = b.call_one(normal, &[top]);
        let v = b.call_one(alloc, &[lc]);
        b.call(scale, &[c, v, pow]);
        // `la+1` cannot overflow: a valid object also has its header.
        let cap = add(b, la, one);
        let u = b.call_one(alloc, &[cap]);
        let carry = b.call_one(scale, &[a, u, pow]);
        write_digit(b, u, la, carry, word);
        let count = sub(b, la, lc);
        let count = add(b, count, one);
        let q = b.call_one(alloc, &[count]);
        b.loop_(&[count], &[], |b, state| {
            let n = state[0];
            let done = eq(b, n, nil);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let j = sub(b, n, one);
            let digit = quotient_digit(b, steps, (u, v, j), word);
            write_digit(b, q, j, digit, word);
            b.continue_(&[j]);
        });
        b.call(release, &[v]);
        let out = b.if_(
            remainder,
            &[A],
            |b| {
                b.call(release, &[q]);
                b.call(unscale, &[u, lc, pow]);
                set_length(b, u, lc);
                let out = b.call_one(finish, &[u]);
                b.yield_(&[out]);
            },
            |b| {
                b.call(release, &[u]);
                let out = b.call_one(finish, &[q]);
                b.yield_(&[out]);
            },
        )[0];
        b.ret(&[out]);
    });
    f
}

#[derive(Clone, Copy)]
enum DivisionResult {
    Quotient,
    Remainder,
}

/// A number a word holds, as a natural: an immediate where it is small,
/// and an object where it is not.
fn promotion(p: &mut Program, storage: Storage) -> FunctionId {
    let Storage { half, boxed, .. } = storage;
    let f = declare(p, "nat.from_word", &[W], &[A]);
    p.define(f, |b, args| {
        let value = args[0];
        let top = number(b, half);
        let fits = lt(b, value, top);
        b.if_(
            fits,
            &[],
            |b| {
                let held = small_word(b, value);
                b.ret(&[held]);
            },
            |b| b.yield_(&[]),
        );
        let out = b.call_one(boxed, &[value]);
        let out = handle(b, out);
        b.ret(&[out]);
    });
    f
}

fn narrowing(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.to_word_digits", &[A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let len = length(b, a);
        let zero = number(b, 0);
        let empty = eq(b, len, zero);
        let out = b.if_(
            empty,
            &[W],
            |b| b.yield_(&[zero]),
            |b| {
                let low = read_digit(b, a, zero, word);
                b.yield_(&[low]);
            },
        )[0];
        b.ret(&[out]);
    });
    f
}
