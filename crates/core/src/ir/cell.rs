//! Runtime support for immutable algebraic cells.
//!
//! A cell shares the natural runtime's allocation header and heap: total
//! bytes and reference count, then its constructor tag where a natural keeps
//! its digit count. The next word is the address of its fields' descriptor,
//! or nought where no field holds a claim, and the fields follow, laid out
//! as [`super::packing`] says. The generic release reads the descriptor, so
//! it walks only the fields holding a claim and needs no code per shape.
//! Scalars need no action; naturals, cells and sequence buffers release
//! through their respective helpers.

use super::natural::{Helper, Library as NaturalLibrary};
use super::{Binary, Builder, Class, FunctionId, Offset, Program, Relation, ValueId, Width};

pub(super) const SCALAR: u64 = 0;
pub(super) const NATURAL: u64 = 1;
pub(super) const CELL: u64 = 2;
pub(super) const BUFFER: u64 = 3;

/// The word holding a cell's tag.
pub(super) const TAG: i32 = 2;
/// The word holding the address of a cell's descriptor.
pub(super) const DESCRIPTOR: i32 = 3;
/// The word a cell's fields begin at.
pub(super) const FIELDS: i32 = 4;

/// The kind a value of `class` is stored as, in a cell field or a buffer.
pub(super) const fn kind(class: Class) -> u64 {
    match class {
        Class::Natural => NATURAL,
        Class::Cell => CELL,
        Class::Buffer => BUFFER,
        _ => SCALAR,
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Library {
    pub retain: FunctionId,
    pub release: FunctionId,
    pub allocate: FunctionId,
}

const A: Class = Class::Address;
const W: Class = Class::Word;

/// What takes and gives up a claim of each kind, for walking what an object
/// holds.
#[derive(Clone, Copy)]
pub(super) struct Claims {
    pub word_bits: u16,
    pub retain: FunctionId,
    pub naturals: FunctionId,
    /// Where immediate naturals begin, which hold no claim.
    pub half: u64,
    pub cells: FunctionId,
    /// Only a program holding sequences has buffers to release.
    pub buffers: Option<FunctionId>,
}

impl Claims {
    /// Give up a claim of `kind`, known before the program runs.
    pub(super) fn release(self, b: &mut Builder<'_>, kind: u64, value: ValueId) {
        let function = match kind {
            NATURAL => {
                let small = self.small(b, value);
                b.if_(
                    small,
                    &[],
                    |b| b.yield_(&[]),
                    |b| {
                        let value = b.convert(A, value);
                        b.call(self.naturals, &[value]);
                        b.yield_(&[]);
                    },
                );
                return;
            }
            CELL => self.cells,
            BUFFER => self
                .buffers
                .expect("a buffer is released only where there are any"),
            _ => return,
        };
        let value = b.convert(A, value);
        b.call(function, &[value]);
    }

    /// Give up a claim of a kind read while the program runs, which a
    /// descriptor lists and so is never a scalar's.
    pub(super) fn release_by_kind(self, b: &mut Builder<'_>, kind: ValueId, value: ValueId) {
        let kinds: &[u64] = if self.buffers.is_some() {
            &[NATURAL, CELL, BUFFER]
        } else {
            &[NATURAL, CELL]
        };
        self.choose(b, kind, value, kinds);
    }

    fn choose(self, b: &mut Builder<'_>, kind: ValueId, value: ValueId, kinds: &[u64]) {
        let Some((&wanted, rest)) = kinds.split_first() else {
            return;
        };
        if rest.is_empty() {
            self.release(b, wanted, value);
            return;
        }
        let expected = number(b, wanted);
        let this = b.compare(Relation::Equal, kind, expected);
        b.if_(
            this,
            &[],
            |b| {
                self.release(b, wanted, value);
                b.yield_(&[]);
            },
            |b| {
                self.choose(b, kind, value, rest);
                b.yield_(&[]);
            },
        );
    }

    /// Take another claim to what a leaf of `kind` holds, known or read
    /// while the program runs: none for an immediate natural.
    pub(super) fn claim(self, b: &mut Builder<'_>, kind: ValueId, value: ValueId) {
        let natural = number(b, NATURAL);
        let is_natural = b.compare(Relation::Equal, kind, natural);
        let small = self.small(b, value);
        let immediate = b.binary(Binary::Mul, is_natural, small);
        b.if_(
            immediate,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let held = b.convert(A, value);
                b.call(self.retain, &[held]);
                b.yield_(&[]);
            },
        );
    }

    /// One where a word holds an immediate natural rather than an object.
    fn small(self, b: &mut Builder<'_>, value: ValueId) -> ValueId {
        let below = number(b, self.half - 1);
        b.compare(Relation::Less, below, value)
    }

    /// Do `each` for every claim the descriptor at `descriptor` lists, of
    /// the object or element whose leaves begin at `at`: with the claim's
    /// kind and what the leaf holds.
    pub(super) fn each(
        self,
        b: &mut Builder<'_>,
        (descriptor, at): (ValueId, ValueId),
        each: &mut dyn FnMut(&mut Builder<'_>, ValueId, ValueId),
    ) {
        let bytes = u64::from(self.word_bits / 8);
        let count = b.load(Width::Word, descriptor, Offset::Words(0));
        let zero = number(b, 0);
        b.loop_(&[zero], &[], |b, state| {
            let claim = state[0];
            let done = b.compare(Relation::Equal, claim, count);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let two = number(b, 2);
            let pair = b.binary(Binary::Mul, claim, two);
            let entry = offset(b, descriptor, pair, bytes);
            let leaf = b.load(Width::Word, entry, Offset::Words(1));
            let kind = b.load(Width::Word, entry, Offset::Words(2));
            let place = byte_offset(b, at, leaf);
            let value = b.load(Width::Word, place, Offset::Words(0));
            each(b, kind, value);
            let one = number(b, 1);
            let next = b.binary(Binary::Add, claim, one);
            b.continue_(&[next]);
        });
    }
}

/// Append the cell routines. `buffers` releases a sequence buffer held in a
/// field, and may be declared but not yet defined.
pub(super) fn append(
    program: &mut Program,
    naturals: &NaturalLibrary,
    buffers: Option<FunctionId>,
    word_bits: u16,
) -> Library {
    let release = program.declare("cell.release", &[A], &[]);
    let library = Library {
        retain: naturals.retain,
        release,
        allocate: naturals.require(Helper::Allocate),
    };
    let claims = Claims {
        word_bits,
        retain: naturals.retain,
        naturals: naturals.release,
        half: naturals.half,
        cells: release,
        buffers,
    };
    define_release(program, library, naturals.release, claims);
    library
}

pub(super) fn number(b: &mut Builder<'_>, value: u64) -> ValueId {
    b.constant(W, value)
}

/// The address `words` words past `object`, the count worked out while the
/// program runs.
pub(super) fn offset(b: &mut Builder<'_>, object: ValueId, words: ValueId, bytes: u64) -> ValueId {
    let bytes = number(b, bytes);
    let distance = b.binary(Binary::Mul, words, bytes);
    byte_offset(b, object, distance)
}

/// The address `bytes` bytes past `object`.
pub(super) fn byte_offset(b: &mut Builder<'_>, object: ValueId, bytes: ValueId) -> ValueId {
    let base = b.convert(W, object);
    let address = b.binary(Binary::Add, base, bytes);
    b.convert(A, address)
}

/// Where the last claim goes, every field the descriptor lists gives up
/// what it holds, then the block goes.
fn define_release(program: &mut Program, library: Library, block: FunctionId, claims: Claims) {
    let bytes = u64::from(claims.word_bits / 8);
    program.define(library.release, |b, args| {
        let object = args[0];
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let one = number(b, 1);
        let last = b.compare(Relation::Equal, refs, one);
        b.if_(
            last,
            &[],
            |b| {
                let descriptor = b.load(Width::Word, object, Offset::Words(DESCRIPTOR));
                let zero = number(b, 0);
                let none = b.compare(Relation::Equal, descriptor, zero);
                b.if_(
                    none,
                    &[],
                    |b| b.yield_(&[]),
                    |b| {
                        let descriptor = b.convert(A, descriptor);
                        let fields = number(b, bytes * u64::from(FIELDS.unsigned_abs()));
                        let fields = byte_offset(b, object, fields);
                        claims.each(b, (descriptor, fields), &mut |b, kind, value| {
                            claims.release_by_kind(b, kind, value);
                        });
                        b.yield_(&[]);
                    },
                );
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.call(block, &[object]);
        b.ret(&[]);
    });
}
