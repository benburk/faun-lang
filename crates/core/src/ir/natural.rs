//! Shared machine-IR natural arithmetic on base-256 digits.
//!
//! A natural is held in a word. One below half a word is an immediate: the
//! word is the number plus half a word, so its top bit is set, it is no
//! object, and it holds no claim. Anything larger is an object, whose
//! address every target places below half the address space. Every natural
//! is held the one way its size says, so an immediate is always the smaller
//! of an immediate and an object. Most numbers a program counts with are
//! small, so most arithmetic allocates nothing: each routine answers two
//! immediates itself where the answer is one, and legalization writes that
//! case where it calls one. Otherwise an immediate operand is boxed for as
//! long as the digit routine reading it takes, and a result small enough is
//! answered as an immediate.
//!
//! Inputs are borrowed; every natural result owns a claim, which for an
//! immediate is nothing. The caller must release it. Objects have three
//! target-word headers: total block bytes, reference count, and normalized
//! digit count. Digits are little endian.
//! Static objects have an all-ones count. Mortal objects live in a private,
//! reusable, coalescing heap that starts in the globals. Where the target's
//! `grow` has more to give, a full heap asks it for an arena at least as large
//! as the heap so far; otherwise, and where it has no more, exhaustion exits
//! with status two. A block comes back with its digits unwritten: every
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

use super::{
    Binary, Builder, Class, DataId, FunctionId, Offset, Program, Relation, ValueId, Width,
};

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub word_bits: u16,
    /// The heap every program starts with, in its globals.
    pub heap_bytes: usize,
    /// Whether the heap asks the target for more when it is full, rather
    /// than exiting. A target whose `grow` has nothing to bound it says no.
    pub grows: bool,
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
    Compare,
    FromWord,
    ToWord,
}

impl Helper {
    pub(super) const ALL: [Self; 9] = [
        Self::Allocate,
        Self::Add,
        Self::Sub,
        Self::Mul,
        Self::Div,
        Self::Mod,
        Self::Compare,
        Self::FromWord,
        Self::ToWord,
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
    /// Where immediates begin, as [`half`] says.
    pub half: u64,
    helpers: [Option<FunctionId>; Helper::ALL.len()],
}

impl Library {
    /// The value a natural known before the program runs is held as, where
    /// it is small enough to be an immediate.
    pub(super) fn small(&self, b: &mut Builder<'_>, n: u64) -> Option<ValueId> {
        (n < self.half).then(|| small(b, self.half, n))
    }

    /// Take another claim to a natural, where it is an object.
    pub(super) fn retain_value(&self, b: &mut Builder<'_>, value: ValueId) -> ValueId {
        self.unless_small(b, value, self.retain);
        value
    }

    /// Give up a claim to a natural, where it is an object.
    pub(super) fn release_value(&self, b: &mut Builder<'_>, value: ValueId) {
        self.unless_small(b, value, self.release);
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
        let half = self.half;
        let helper = match op {
            Inline::Add => self.require(Helper::Add),
            Inline::Monus => self.require(Helper::Sub),
            Inline::Compare => self.require(Helper::Compare),
        };
        let result = match op {
            Inline::Add | Inline::Monus => A,
            Inline::Compare => W,
        };
        let small_a = is_small(b, half, a);
        let small_c = is_small(b, half, c);
        let both = b.binary(Binary::Mul, small_a, small_c);
        let called = |b: &mut Builder<'_>| {
            let out = b.call_one(helper, &[a, c]);
            b.yield_(&[out]);
        };
        b.if_(
            both,
            &[result],
            |b| {
                // Immediates are ordered as the words holding them are, and
                // differ by what those words differ by.
                let x = b.convert(W, a);
                let y = b.convert(W, c);
                match op {
                    Inline::Add => {
                        // `x` holds its number past half a word; adding
                        // `c`'s number to it holds the sum the same way,
                        // unless the sum reaches half a word, which is
                        // exactly where adding goes past the word's top.
                        let top = number(b, half);
                        let over = sub(b, y, top);
                        let sum = add(b, x, over);
                        let outside = lt(b, sum, x);
                        let out = b.if_(outside, &[A], called, |b| {
                            let held = b.convert(A, sum);
                            b.yield_(&[held]);
                        })[0];
                        b.yield_(&[out]);
                    }
                    Inline::Monus => {
                        let rest = b.binary(Binary::Monus, x, y);
                        let held = small_word(b, half, rest);
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
            },
            called,
        )[0]
    }

    fn unless_small(&self, b: &mut Builder<'_>, value: ValueId, count: FunctionId) {
        let small = is_small(b, self.half, value);
        b.if_(
            small,
            &[],
            |b| b.yield_(&[]),
            |b| {
                b.call(count, &[value]);
                b.yield_(&[]);
            },
        );
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
    let size = digits
        .len()
        .checked_add(4 * word - 1)
        .map(|n| n / word * word)
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
    header(&mut bytes, 2, size64(digits.len()), word);
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
    let header = number(b, size64(3 * word));
    let offset = add(b, i, header);
    address(b, a, offset)
}

fn read_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, word: usize) -> ValueId {
    let at = digit_address(b, a, i, word);
    b.load(Width::Byte, at, Offset::Bytes(0))
}

fn write_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, v: ValueId, word: usize) {
    let at = digit_address(b, a, i, word);
    b.store(Width::Byte, at, Offset::Bytes(0), v);
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
        library.insert(Helper::Compare, comparing(program, half, compare));
    }
    if let Some(narrow) = narrow
        && needs.contains(Helper::ToWord)
    {
        library.insert(Helper::ToWord, lowering(program, half, narrow));
    }
    if arithmetic {
        let alloc = allocation(program, config, (word, max), (empty, fail))?;
        if needs.contains(Helper::Allocate) {
            library.insert(Helper::Allocate, alloc);
        }
        let digits = digits_allocation(program, alloc, fail, half);
        let trim = trimming(program, word);
        let narrow = narrow.expect("arithmetic reads a small result back as a word");
        let finish = finishing(program, (trim, narrow), release, (half, word));
        let boxed = boxing(program, digits, trim, word);
        let storage = Storage {
            config,
            word,
            half,
            alloc: digits,
            trim,
            finish,
            fail,
            boxed,
            release,
        };
        storage.append(program, needs, compare, &mut library);
    }
    Ok(library)
}

/// Where immediates begin: the upper half of a word. A number below it is
/// held as itself plus this; an object is held as its address, which every
/// target places in the lower half.
pub(super) const fn half(word_bits: u16) -> u64 {
    1 << (word_bits - 1)
}

/// The immediate holding `n`, which must be below `half`.
fn small(b: &mut Builder<'_>, half: u64, n: u64) -> ValueId {
    let held = number(b, n + half);
    b.convert(A, held)
}

/// The immediate holding a word known to be below `half`.
fn small_word(b: &mut Builder<'_>, half: u64, n: ValueId) -> ValueId {
    let top = number(b, half);
    let held = add(b, n, top);
    b.convert(A, held)
}

/// One where `value` is an immediate, nought where it is an object.
fn is_small(b: &mut Builder<'_>, half: u64, value: ValueId) -> ValueId {
    let held = b.convert(W, value);
    let below = number(b, half - 1);
    lt(b, below, held)
}

/// The number an immediate holds.
fn unwrapped(b: &mut Builder<'_>, half: u64, value: ValueId) -> ValueId {
    let held = b.convert(W, value);
    let top = number(b, half);
    sub(b, held, top)
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
    config: Config,
    word: usize,
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
                self.append_subdivision(p, needs, lib, (digit, compare));
            }
        }
    }

    fn append_subdivision(
        self,
        p: &mut Program,
        needs: Needs,
        lib: &mut Library,
        (digit, compare): (FunctionId, FunctionId),
    ) {
        let subtract = subtracting(p, digit, self.trim, self.word);
        if needs.contains(Helper::Sub) {
            let objects = monus(p, self, compare, subtract);
            lib.insert(Helper::Sub, self.difference(p, objects));
        }
        if needs.contains(Helper::Div) || needs.contains(Helper::Mod) {
            let divmod = division(p, self, compare, subtract, lib.retain);
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
            both_small(b, half, a, c, |b, x, y| {
                // Each is below half a word, so their sum is below a word.
                let sum = add(b, x, y);
                let top = number(b, half);
                let fits = lt(b, sum, top);
                b.if_(
                    fits,
                    &[],
                    |b| {
                        let held = small_word(b, half, sum);
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

    fn difference(self, p: &mut Program, objects: FunctionId) -> FunctionId {
        let half = self.half;
        let f = declare(p, "nat.sub", &[A, A], &[A]);
        p.define(f, |b, args| {
            let (a, c) = (args[0], args[1]);
            let small_a = is_small(b, half, a);
            b.if_(
                small_a,
                &[],
                |b| {
                    both_small(b, half, a, c, |b, x, y| {
                        let rest = b.binary(Binary::Monus, x, y);
                        let held = small_word(b, half, rest);
                        b.ret(&[held]);
                    });
                    // An object is more than any immediate.
                    let z = small(b, half, 0);
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
            both_small(b, half, a, c, |b, x, y| {
                let bound = number(b, root);
                let low_x = lt(b, x, bound);
                let low_y = lt(b, y, bound);
                let both = b.binary(Binary::Mul, low_x, low_y);
                b.if_(
                    both,
                    &[],
                    |b| {
                        let product = b.binary(Binary::Mul, x, y);
                        let held = small_word(b, half, product);
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

    #[expect(
        clippy::too_many_lines,
        reason = "the immediate cases of both division results beside the boxed fallback"
    )]
    fn quotient(self, p: &mut Program, divmod: FunctionId, result: DivisionResult) -> FunctionId {
        let half = self.half;
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
                    DivisionResult::Quotient => small(b, half, 0),
                    DivisionResult::Remainder => a,
                };
                b.ret(&[out]);
            };
            let small_a = is_small(b, half, a);
            b.if_(
                small_a,
                &[],
                |b| {
                    both_small(b, half, a, c, |b, x, y| {
                        let nil = number(b, 0);
                        let by_nought = eq(b, y, nil);
                        b.if_(by_nought, &[], |b| whole(b), |b| b.yield_(&[]));
                        let op = match result {
                            DivisionResult::Quotient => Binary::Div,
                            DivisionResult::Remainder => Binary::Mod,
                        };
                        let out = b.binary(op, x, y);
                        let held = small_word(b, half, out);
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
        let (half, boxed, release) = (self.half, self.boxed, self.release);
        let held = [a, c].map(|value| {
            let small = is_small(b, half, value);
            let object = b.if_(
                small,
                &[A],
                |b| {
                    let n = unwrapped(b, half, value);
                    let object = b.call_one(boxed, &[n]);
                    b.yield_(&[object]);
                },
                |b| b.yield_(&[value]),
            )[0];
            (small, object)
        });
        let mut args = vec![held[0].1, held[1].1];
        args.extend_from_slice(rest);
        let out = b.call_one(objects, &args);
        for (small, object) in held {
            b.if_(
                small,
                &[],
                |b| {
                    b.call(release, &[object]);
                    b.yield_(&[]);
                },
                |b| b.yield_(&[]),
            );
        }
        out
    }
}

/// Run `then` with the numbers `a` and `c` hold where both are immediates.
/// It ends its arm itself: answering the routine, or yielding to go on.
fn both_small(
    b: &mut Builder<'_>,
    half: u64,
    a: ValueId,
    c: ValueId,
    then: impl FnOnce(&mut Builder<'_>, ValueId, ValueId),
) {
    let small_a = is_small(b, half, a);
    let small_c = is_small(b, half, c);
    let both = b.binary(Binary::Mul, small_a, small_c);
    b.if_(
        both,
        &[],
        |b| {
            let x = unwrapped(b, half, a);
            let y = unwrapped(b, half, c);
            then(b, x, y);
        },
        |b| b.yield_(&[]),
    );
}

/// The order of two naturals, as the routine reading digits answers it:
/// nought for less, one for equal, two for greater. Immediates are ordered
/// as the words holding them are, and an object is more than any of them.
#[expect(
    clippy::too_many_lines,
    reason = "four cases of immediate and object, each answering an order"
)]
fn comparing(p: &mut Program, half: u64, objects: FunctionId) -> FunctionId {
    let f = declare(p, "nat.compare", &[A, A], &[W]);
    p.define(f, |b, args| {
        let (a, c) = (args[0], args[1]);
        let small_a = is_small(b, half, a);
        let small_c = is_small(b, half, c);
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
        let order = b.call_one(objects, &[a, c]);
        b.ret(&[order]);
    });
    f
}

/// A natural's low word: an immediate's number, or an object's low digits.
fn lowering(p: &mut Program, half: u64, objects: FunctionId) -> FunctionId {
    let f = declare(p, "nat.to_word", &[A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let small_a = is_small(b, half, a);
        b.if_(
            small_a,
            &[],
            |b| {
                let n = unwrapped(b, half, a);
                b.ret(&[n]);
            },
            |b| b.yield_(&[]),
        );
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
        growing(program, config, (word, max), zero, fail)
    } else {
        allocator(program, config, word, zero, fail)
    }
}

/// Words at the start of every arena: the next arena, and where its blocks
/// end. A next of nought is the first arena, the one in the globals.
const ARENA_WORDS: usize = 2;

/// The allocator of a heap that grows: a ring of arenas, the first in the
/// globals and each other from the target's `grow`, searched first-fit from
/// where the last allocation ended. Where no arena has room, a new one at
/// least as large as the heap so far is asked for, so the heap doubles and
/// a program asks the target a number of times logarithmic in what it
/// holds.
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
) -> Result<FunctionId, String> {
    let padding = (word - p.globals().len() % word) % word;
    if p.globals()
        .len()
        .checked_add(padding)
        .and_then(|n| n.checked_add(config.heap_bytes + 4 * word))
        .is_none_or(|n| u32::try_from(n).is_err())
    {
        return Err("natural heap exceeds the globals pool".to_owned());
    }
    if padding != 0 {
        p.global(&vec![0; padding]);
    }
    let start = ARENA_WORDS * word;
    let mut bytes = vec![0; config.heap_bytes];
    header(&mut bytes, 1, size64(config.heap_bytes), word);
    header(
        &mut bytes,
        ARENA_WORDS,
        size64(config.heap_bytes - start),
        word,
    );
    let heap = p.global(&bytes);
    // Where the search starts, as an arena (nought for the first) and an
    // offset in it; how many arenas there are; how large the heap is.
    let mut state = vec![0; 4 * word];
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
        let found = b.loop_(&[arena, offset, nil], &[A, W], |b, state| {
            let (arena, offset, starts) = (state[0], state[1], state[2]);
            let end = b.load(Width::Word, arena, Offset::Words(1));
            let at_end = eq(b, offset, end);
            b.if_(
                at_end,
                &[],
                |b| {
                    // On to the next arena, having begun as many as there
                    // are after the one the search began part way through.
                    let one = number(b, 1);
                    let more = add(b, starts, one);
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
                    b.continue_(&[next, start, more]);
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
                            b.continue_(&[arena, next, starts]);
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
                    b.continue_(&[arena, next, starts]);
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
        let page = b.call_one(grow, &[chunk]);
        // A target that has no more answers an address the chunk would run
        // past the end of the address space from.
        let top = number(b, max);
        let room = sub(b, top, chunk);
        let from = b.convert(W, page);
        let refused = lt(b, room, from);
        b.if_(
            refused,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        let after_first = b.load(Width::Word, first, Offset::Words(0));
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
        let grown = add(b, total, chunk);
        b.store(Width::Word, kept, Offset::Words(3), grown);
        b.call(claim, &[at, wanted, cap]);
        let taken = b.load(Width::Word, at, Offset::Words(0));
        let after = add(b, header_bytes, taken);
        b.store(Width::Word, kept, Offset::Words(0), from);
        b.store(Width::Word, kept, Offset::Words(1), after);
        b.ret(&[at]);
    });
    Ok(allocate)
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
    (half, word): (u64, usize),
) -> FunctionId {
    let f = declare(p, "nat.finish", &[A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        b.call(trim, &[a]);
        let len = length(b, a);
        // More digits than a word has is more than half a word holds.
        let most = number(b, size64(word));
        let wide = lt(b, most, len);
        b.if_(wide, &[], |b| b.ret(&[a]), |b| b.yield_(&[]));
        let value = b.call_one(narrow, &[a]);
        let top = number(b, half);
        let fits = lt(b, value, top);
        b.if_(
            fits,
            &[],
            |b| {
                b.call(release, &[a]);
                let held = small_word(b, half, value);
                b.ret(&[held]);
            },
            |b| b.yield_(&[]),
        );
        b.ret(&[a]);
    });
    f
}

/// Allocate an object for `cap` digits, which has to lie where no
/// immediate does. Every target places its heap far below that; one that
/// did not would have a natural it could not tell from a number.
fn digits_allocation(
    p: &mut Program,
    alloc: FunctionId,
    fail: FunctionId,
    half: u64,
) -> FunctionId {
    let f = declare(p, "nat.digits", &[W], &[A]);
    p.define(f, |b, args| {
        let out = b.call_one(alloc, &[args[0]]);
        let high = is_small(b, half, out);
        b.if_(
            high,
            &[],
            |b| {
                b.call(fail, &[]);
            },
            |b| b.yield_(&[]),
        );
        b.ret(&[out]);
    });
    f
}

/// An object holding a word, trimmed but never read back as an immediate,
/// for a routine that reads digits of a number an immediate holds.
fn boxing(p: &mut Program, digits: FunctionId, trim: FunctionId, word: usize) -> FunctionId {
    let f = declare(p, "nat.box", &[W], &[A]);
    p.define(f, |b, args| {
        let value = args[0];
        let cap = number(b, size64(word));
        let out = b.call_one(digits, &[cap]);
        let nil = number(b, 0);
        let radix = number(b, 256);
        let one = number(b, 1);
        b.loop_(&[nil, value], &[], |b, state| {
            let i = state[0];
            let n = state[1];
            let done = eq(b, i, cap);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let low = b.binary(Binary::Mod, n, radix);
            let high = b.binary(Binary::Div, n, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high]);
        });
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
        config,
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
        let limit = number(b, size64(config.heap_bytes - 3 * word));
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
        let radix = number(b, 256);
        let cap = add(b, len, one);
        let out = b.call_one(alloc, &[cap]);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let i = state[0];
            let carry = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = b.call_one(digit, &[a, i]);
            let y = b.call_one(digit, &[c, i]);
            let sum = add(b, x, y);
            let sum = add(b, sum, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high]);
        })[0];
        write_digit(b, out, len, carry, word);
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
        let radix = number(b, 256);
        b.loop_(&[zero, zero], &[], |b, state| {
            let i = state[0];
            let borrow = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, a, i, word);
            let y = b.call_one(digit, &[c, i]);
            let y = add(b, y, borrow);
            let borrow = lt(b, x, y);
            let low = b.if_(
                borrow,
                &[W],
                |b| {
                    let wide = add(b, x, radix);
                    let low = sub(b, wide, y);
                    b.yield_(&[low]);
                },
                |b| {
                    let low = sub(b, x, y);
                    b.yield_(&[low]);
                },
            )[0];
            write_digit(b, a, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, borrow]);
        });
        b.call(trim, &[a]);
        b.ret(&[]);
    });
    f
}

#[expect(
    clippy::too_many_lines,
    reason = "one generated monus routine and its scratch lifetimes"
)]
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
        half,
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
                let z = small(b, half, 0);
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
        let radix = number(b, 256);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let j = state[0];
            let carry = state[1];
            let done = eq(b, j, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let y = read_digit(b, c, j, word);
            let at = add(b, i, j);
            let acc = read_digit(b, out, at, word);
            // 255*255 + 255 + 255 = 65535, even on a 16-bit target.
            let product = b.binary(Binary::Mul, x, y);
            let sum = add(b, product, acc);
            let sum = add(b, sum, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, at, low, word);
            let next = add(b, j, one);
            b.continue_(&[next, high]);
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
        config,
        word,
        half,
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
                    let z = small(b, half, 0);
                    b.ret(&[z]);
                },
                |b| b.yield_(&[]),
            );
        }
        // Check each component before addition, including large static inputs.
        let limit = number(b, size64(config.heap_bytes - 3 * word));
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

// r <- 2*r+bit, in a unique remainder with one spare digit.
fn shifting(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.shift_in", &[A, W], &[]);
    p.define(f, |b, args| {
        let out = args[0];
        let bit = args[1];
        let len = length(b, out);
        let zero = number(b, 0);
        let one = number(b, 1);
        let two = number(b, 2);
        let radix = number(b, 256);
        let carry = b.loop_(&[zero, bit], &[W], |b, state| {
            let i = state[0];
            let carry = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = read_digit(b, out, i, word);
            let doubled = b.binary(Binary::Mul, x, two);
            let sum = add(b, doubled, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high]);
        })[0];
        let empty = eq(b, carry, zero);
        b.if_(
            empty,
            &[],
            |b| b.yield_(&[]),
            |b| {
                write_digit(b, out, len, carry, word);
                let next = add(b, len, one);
                set_length(b, out, next);
                b.yield_(&[]);
            },
        );
        b.ret(&[]);
    });
    f
}

fn divide_digit(
    p: &mut Program,
    compare: FunctionId,
    subtract: FunctionId,
    word: usize,
) -> FunctionId {
    let shift = shifting(p, word);
    // This one-byte quotient step keeps the division's outer loop small.
    let step = declare(p, "nat.divide_digit", &[A, A, W], &[W]);
    p.define(step, |b, args| {
        let r = args[0];
        let divisor = args[1];
        let digit = args[2];
        let zero = number(b, 0);
        let two = number(b, 2);
        let top = number(b, 128);
        let answer = b.loop_(&[top, zero], &[W], |b, state| {
            let mask = state[0];
            let quotient = state[1];
            let done = eq(b, mask, zero);
            b.if_(done, &[], |b| b.break_(&[quotient]), |b| b.yield_(&[]));
            let part = b.binary(Binary::Div, digit, mask);
            let bit = b.binary(Binary::Mod, part, two);
            b.call(shift, &[r, bit]);
            let order = b.call_one(compare, &[r, divisor]);
            let less = eq(b, order, zero);
            let quotient = b.if_(
                less,
                &[W],
                |b| b.yield_(&[quotient]),
                |b| {
                    b.call(subtract, &[r, divisor]);
                    let next = add(b, quotient, mask);
                    b.yield_(&[next]);
                },
            )[0];
            let next = b.binary(Binary::Div, mask, two);
            b.continue_(&[next, quotient]);
        })[0];
        b.ret(&[answer]);
    });
    step
}

#[expect(
    clippy::too_many_lines,
    reason = "one generated div/mod routine and its scratch lifetimes"
)]
fn division(
    p: &mut Program,
    storage: Storage,
    compare: FunctionId,
    subtract: FunctionId,
    retain: FunctionId,
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        half,
        release,
        ..
    } = storage;
    let step = divide_digit(p, compare, subtract, word);
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
                            b.yield_(&[kept]);
                        },
                        |b| {
                            let z = small(b, half, 0);
                            b.yield_(&[z]);
                        },
                    )[0];
                    b.ret(&[answer]);
                },
                |b| b.yield_(&[]),
            );
        }
        // lc+1 cannot overflow: a valid object also has its three-word header.
        let cap = add(b, lc, one);
        let r = b.call_one(alloc, &[cap]);
        set_length(b, r, nil);
        let q = b.call_one(alloc, &[la]);
        b.loop_(&[la], &[], |b, state| {
            let n = state[0];
            let done = eq(b, n, nil);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let digit = read_digit(b, a, i, word);
            let quotient = b.call_one(step, &[r, c, digit]);
            write_digit(b, q, i, quotient, word);
            b.continue_(&[i]);
        });
        let out = b.if_(
            remainder,
            &[A],
            |b| {
                b.call(release, &[q]);
                let out = b.call_one(finish, &[r]);
                b.yield_(&[out]);
            },
            |b| {
                b.call(release, &[r]);
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
                let held = small_word(b, half, value);
                b.ret(&[held]);
            },
            |b| b.yield_(&[]),
        );
        let out = b.call_one(boxed, &[value]);
        b.ret(&[out]);
    });
    f
}

fn narrowing(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.to_word_digits", &[A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let len = length(b, a);
        let max = number(b, size64(word));
        let less = lt(b, len, max);
        let count = b.if_(less, &[W], |b| b.yield_(&[len]), |b| b.yield_(&[max]))[0];
        let zero = number(b, 0);
        let one = number(b, 1);
        let radix = number(b, 256);
        let out = b.loop_(&[count, zero], &[W], |b, state| {
            let n = state[0];
            let value = state[1];
            let done = eq(b, n, zero);
            b.if_(done, &[], |b| b.break_(&[value]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let digit = read_digit(b, a, i, word);
            let high = b.binary(Binary::Mul, value, radix);
            let value = add(b, high, digit);
            b.continue_(&[i, value]);
        })[0];
        b.ret(&[out]);
    });
    f
}
