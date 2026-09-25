//! Runtime support for sequence buffers.
//!
//! A sequence is a buffer and a length, and holds the buffer's last `len`
//! elements: every sequence sharing a buffer is a suffix of it, since a
//! sequence only ever grows at its front and a tail is one element shorter.
//! A buffer shares the natural runtime's allocation header, then:
//!
//! - word 2: its capacity, in elements;
//! - word 3: the lowest element it holds claims for, which is everything
//!   from there to the end;
//! - word 4: its stride, the words each element takes, one per leaf;
//! - one word per leaf saying what kind of value it is, as cells say;
//! - the elements, `capacity` of them, `stride` words each.
//!
//! Pushing onto a buffer nothing else holds writes into the free element in
//! front of the sequence, releasing whatever an earlier, longer sequence
//! left there. Otherwise, or where there is no room, the sequence is copied
//! into a new buffer with as much room in front as it has elements, and at
//! least [`MINIMUM_CAPACITY`], so a run of pushes copies each element a
//! bounded number of times. Where an element's leaves are all scalars, the
//! push writes the first case itself and calls for the second, a copy of
//! scalars is a copy of words, and a release walks no elements.

use std::collections::BTreeMap;

use super::cell::{self, Library as CellLibrary};
use super::natural::{Helper, Library as NaturalLibrary};
use super::{Binary, Builder, Class, FunctionId, Offset, Program, Relation, ValueId, Width};

const A: Class = Class::Address;
const W: Class = Class::Word;

/// The first word after the header that holds a kind.
const KINDS: u64 = 5;

/// The fewest elements a buffer grows to, so that one begun empty is not
/// copied at two elements, then four, then eight.
const MINIMUM_CAPACITY: u64 = 8;

/// The generated routines: one release, and one reservation per element
/// layout, by the kinds of its leaves.
pub(super) struct Library {
    pub release: FunctionId,
    reserve: BTreeMap<Vec<u64>, FunctionId>,
}

impl Library {
    /// The routine making room for one element of this layout.
    ///
    /// # Panics
    /// If the layout was not declared when the library was appended.
    pub(super) fn reserve(&self, kinds: &[u64]) -> FunctionId {
        self.reserve[kinds]
    }

    /// Make room for one element of `kinds` in front of the last `len`
    /// elements of `buffer`, whose claim this takes, as the reservation
    /// routine does: answering a buffer nothing else holds with that slot
    /// free.
    ///
    /// Where every leaf is a scalar, the common case is written here rather
    /// than called: a buffer nothing else holds with room in front is
    /// written in place, and the slot needs only counting as held, since a
    /// scalar left there by a longer sequence holds no claim to give up.
    /// Anything else is the routine's.
    pub(super) fn room(
        &self,
        b: &mut Builder<'_>,
        kinds: &[u64],
        buffer: ValueId,
        len: ValueId,
    ) -> ValueId {
        let reserve = self.reserve(kinds);
        if kinds.iter().any(|&kind| kind != cell::SCALAR) {
            return b.call_one(reserve, &[buffer, len]);
        }
        let refs = b.load(Width::Word, buffer, Offset::Words(1));
        let capacity = b.load(Width::Word, buffer, Offset::Words(2));
        let one = number(b, 1);
        let alone = b.compare(Relation::Equal, refs, one);
        let room = b.compare(Relation::Less, len, capacity);
        let both = b.binary(Binary::Mul, alone, room);
        b.if_(
            both,
            &[A],
            |b| {
                let before = b.binary(Binary::Sub, capacity, len);
                let slot = b.binary(Binary::Sub, before, one);
                let low = b.load(Width::Word, buffer, Offset::Words(3));
                let fresh = b.compare(Relation::Less, slot, low);
                b.if_(
                    fresh,
                    &[],
                    |b| {
                        b.store(Width::Word, buffer, Offset::Words(3), slot);
                        b.yield_(&[]);
                    },
                    |b| b.yield_(&[]),
                );
                b.yield_(&[buffer]);
            },
            |b| {
                let room = b.call_one(reserve, &[buffer, len]);
                b.yield_(&[room]);
            },
        )[0]
    }
}

/// Declare the release routine, so cells and buffers can release one
/// another before either is defined.
pub(super) fn declare(program: &mut Program) -> FunctionId {
    program.declare("seq.release", &[A], &[])
}

/// Define the release routine and one reservation per layout.
pub(super) fn append(
    program: &mut Program,
    release: FunctionId,
    naturals: &NaturalLibrary,
    cells: CellLibrary,
    layouts: impl IntoIterator<Item = Vec<u64>>,
    word_bits: u16,
) -> Library {
    let word = Word {
        bytes: u64::from(word_bits / 8),
        naturals: naturals.release,
        half: naturals.half,
        cells: cells.release,
        buffers: release,
    };
    define_release(program, word);
    let allocate = naturals.require(Helper::Allocate);
    let reserve = layouts
        .into_iter()
        .map(|kinds| {
            let name = format!(
                "seq.reserve.{}",
                kinds.iter().map(u64::to_string).collect::<String>()
            );
            let id = program.declare(&name, &[A, W], &[A]);
            define_reserve(program, id, &kinds, word, (naturals.retain, allocate));
            (kinds, id)
        })
        .collect();
    Library { release, reserve }
}

/// What every routine here needs: the word's width in bytes and the
/// releases for each kind of managed value.
#[derive(Clone, Copy)]
struct Word {
    bytes: u64,
    naturals: FunctionId,
    /// Where immediate naturals begin, which hold no claim.
    half: u64,
    cells: FunctionId,
    buffers: FunctionId,
}

impl Word {
    /// Release a value of `kind`, where it carries a claim.
    fn release(self, b: &mut Builder<'_>, kind: u64, value: ValueId) {
        let function = match kind {
            cell::NATURAL => self.naturals,
            cell::CELL => self.cells,
            cell::BUFFER => self.buffers,
            _ => return,
        };
        if kind == cell::NATURAL {
            let small = self.small(b, value);
            b.if_(
                small,
                &[],
                |b| b.yield_(&[]),
                |b| {
                    let value = b.convert(A, value);
                    b.call(function, &[value]);
                    b.yield_(&[]);
                },
            );
            return;
        }
        let value = b.convert(A, value);
        b.call(function, &[value]);
    }

    /// One where a word holds an immediate natural rather than an object.
    fn small(self, b: &mut Builder<'_>, value: ValueId) -> ValueId {
        let below = number(b, self.half - 1);
        b.compare(Relation::Less, below, value)
    }
}

fn number(b: &mut Builder<'_>, value: u64) -> ValueId {
    b.constant(W, value)
}

/// A count of leaves or elements, as a word holds it.
pub(super) fn count(n: usize) -> u64 {
    u64::try_from(n).expect("a count fits 64 bits")
}

/// The address of word `index` of `object`, where the index is worked out
/// while the program runs.
fn word_at(b: &mut Builder<'_>, object: ValueId, index: ValueId, bytes: u64) -> ValueId {
    let bytes = number(b, bytes);
    let offset = b.binary(Binary::Mul, index, bytes);
    let base = b.convert(W, object);
    let address = b.binary(Binary::Add, base, offset);
    b.convert(A, address)
}

/// The word holding leaf 0 of element `element` of a buffer with `stride`.
pub(super) fn element_word(b: &mut Builder<'_>, stride: ValueId, element: ValueId) -> ValueId {
    let kinds = number(b, KINDS);
    let first = b.binary(Binary::Add, kinds, stride);
    let skipped = b.binary(Binary::Mul, element, stride);
    b.binary(Binary::Add, first, skipped)
}

/// Load word `index`, worked out while the program runs.
pub(super) fn load_word(
    b: &mut Builder<'_>,
    object: ValueId,
    index: ValueId,
    word_bits: u16,
) -> ValueId {
    let address = word_at(b, object, index, u64::from(word_bits / 8));
    b.load(Width::Word, address, Offset::Words(0))
}

/// Store `value` at word `index`, worked out while the program runs.
pub(super) fn store_word(
    b: &mut Builder<'_>,
    object: ValueId,
    index: ValueId,
    value: ValueId,
    word_bits: u16,
) {
    let address = word_at(b, object, index, u64::from(word_bits / 8));
    b.store(Width::Word, address, Offset::Words(0), value);
}

/// Allocate a buffer with room for `capacity` elements of `kinds`, holding
/// none of them yet. `allocate` takes the bytes after the header's third word.
pub(super) fn allocate(
    b: &mut Builder<'_>,
    allocate: FunctionId,
    kinds: &[u64],
    capacity: ValueId,
    word_bytes: u64,
) -> ValueId {
    let stride = number(b, count(kinds.len()));
    let slots = b.binary(Binary::Mul, capacity, stride);
    let fixed = number(b, 2 + count(kinds.len()));
    let words = b.binary(Binary::Add, slots, fixed);
    let bytes = number(b, word_bytes);
    let bytes = b.binary(Binary::Mul, words, bytes);
    let object = b.call_one(allocate, &[bytes]);
    b.store(Width::Word, object, Offset::Words(2), capacity);
    b.store(Width::Word, object, Offset::Words(3), capacity);
    b.store(Width::Word, object, Offset::Words(4), stride);
    for (at, &kind) in kinds.iter().enumerate() {
        let kind = number(b, kind);
        let at = i32::try_from(KINDS + count(at)).expect("a small layout");
        b.store(Width::Word, object, Offset::Words(at), kind);
    }
    object
}

/// Release a buffer: where this is the last claim, every element it holds
/// claims for, then the block.
#[expect(
    clippy::too_many_lines,
    reason = "the generated release routine keeps its walk and object layout together"
)]
fn define_release(program: &mut Program, word: Word) {
    let word_bits = u16::try_from(word.bytes * 8).expect("a word width");
    program.define(word.buffers, |b, args| {
        let object = args[0];
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let one = number(b, 1);
        let last = b.compare(Relation::Equal, refs, one);
        b.if_(
            last,
            &[],
            |b| {
                let capacity = b.load(Width::Word, object, Offset::Words(2));
                let low = b.load(Width::Word, object, Offset::Words(3));
                let stride = b.load(Width::Word, object, Offset::Words(4));
                let first = b.binary(Binary::Mul, low, stride);
                let end = b.binary(Binary::Mul, capacity, stride);
                let kinds = number(b, KINDS);
                let slots = b.binary(Binary::Add, kinds, stride);
                // A buffer of scalars holds no claims, and its elements are
                // not worth a walk to find that out one at a time.
                let holds = holds_claims(b, object, stride, word_bits);
                b.if_(
                    holds,
                    &[],
                    |b| {
                        b.loop_(&[first], &[], |b, state| {
                            let at = state[0];
                            let done = b.compare(Relation::Equal, at, end);
                            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                            let leaf = b.binary(Binary::Mod, at, stride);
                            let kind_word = b.binary(Binary::Add, kinds, leaf);
                            let kind = load_word(b, object, kind_word, word_bits);
                            let slot = b.binary(Binary::Add, slots, at);
                            let value = load_word(b, object, slot, word_bits);
                            release_by_kind(b, word, kind, value);
                            let one = number(b, 1);
                            let next = b.binary(Binary::Add, at, one);
                            b.continue_(&[next]);
                        });
                        b.yield_(&[]);
                    },
                    |b| b.yield_(&[]),
                );
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.call(word.naturals, &[object]);
        b.ret(&[]);
    });
}

/// Whether any leaf of a buffer's elements is of a kind holding a claim:
/// one where it is, nought where every leaf is a scalar.
fn holds_claims(b: &mut Builder<'_>, object: ValueId, stride: ValueId, word_bits: u16) -> ValueId {
    let zero = number(b, 0);
    b.loop_(&[zero], &[W], |b, state| {
        let leaf = state[0];
        let done = b.compare(Relation::Equal, leaf, stride);
        b.if_(done, &[], |b| b.break_(&[zero]), |b| b.yield_(&[]));
        let kinds = number(b, KINDS);
        let at = b.binary(Binary::Add, kinds, leaf);
        let kind = load_word(b, object, at, word_bits);
        let scalar = number(b, cell::SCALAR);
        let plain = b.compare(Relation::Equal, kind, scalar);
        let one = number(b, 1);
        let next = b.binary(Binary::Add, leaf, one);
        b.if_(plain, &[], |b| b.continue_(&[next]), |b| b.break_(&[one]));
    })[0]
}

/// Release `value` by a kind read while the program runs.
fn release_by_kind(b: &mut Builder<'_>, word: Word, kind: ValueId, value: ValueId) {
    choose_release(
        b,
        word,
        kind,
        value,
        &[cell::NATURAL, cell::CELL, cell::BUFFER],
    );
}

/// Ask whether `kind` is the first of `kinds`, releasing as that if so and
/// asking about the rest otherwise.
fn choose_release(b: &mut Builder<'_>, word: Word, kind: ValueId, value: ValueId, kinds: &[u64]) {
    let Some((&wanted, rest)) = kinds.split_first() else {
        return;
    };
    let expected = number(b, wanted);
    let this = b.compare(Relation::Equal, kind, expected);
    b.if_(
        this,
        &[],
        |b| {
            word.release(b, wanted, value);
            b.yield_(&[]);
        },
        |b| {
            choose_release(b, word, kind, value, rest);
            b.yield_(&[]);
        },
    );
}

/// Make room for one element of `kinds` in front of the last `len` elements
/// of a buffer whose claim this takes, answering a buffer nothing else holds
/// whose element at `capacity - len - 1` holds no claim.
#[expect(
    clippy::too_many_lines,
    reason = "the in-place and copying paths share one routine's layout"
)]
fn define_reserve(
    program: &mut Program,
    id: FunctionId,
    kinds: &[u64],
    word: Word,
    (retain, allocate_block): (FunctionId, FunctionId),
) {
    let word_bits = u16::try_from(word.bytes * 8).expect("a word width");
    program.define(id, |b, args| {
        let (object, len) = (args[0], args[1]);
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let capacity = b.load(Width::Word, object, Offset::Words(2));
        let one = number(b, 1);
        let alone = b.compare(Relation::Equal, refs, one);
        let room = b.compare(Relation::Less, len, capacity);
        let both = b.binary(Binary::Mul, alone, room);
        let answer = b.if_(
            both,
            &[A],
            |b| {
                // Nothing else can see this buffer, so the element in front
                // of the sequence is ours: free it of whatever a longer
                // sequence left there, or count it as held from now on.
                let before = b.binary(Binary::Sub, capacity, len);
                let slot = b.binary(Binary::Sub, before, one);
                let low = b.load(Width::Word, object, Offset::Words(3));
                let fresh = b.compare(Relation::Less, slot, low);
                let stride = number(b, count(kinds.len()));
                b.if_(
                    fresh,
                    &[],
                    |b| {
                        b.store(Width::Word, object, Offset::Words(3), slot);
                        b.yield_(&[]);
                    },
                    |b| {
                        let first = element_word(b, stride, slot);
                        for (leaf, &kind) in kinds.iter().enumerate() {
                            if !matches!(kind, cell::NATURAL | cell::CELL | cell::BUFFER) {
                                continue;
                            }
                            let leaf = number(b, count(leaf));
                            let at = b.binary(Binary::Add, first, leaf);
                            let value = load_word(b, object, at, word_bits);
                            word.release(b, kind, value);
                        }
                        b.yield_(&[]);
                    },
                );
                b.yield_(&[object]);
            },
            |b| {
                // Shared or full: copy the sequence to the end of a buffer
                // with as much room again in front, holding a claim to each
                // element it copies, then give up this one.
                let grown = b.binary(Binary::Add, len, one);
                let two = number(b, 2);
                let doubled = b.binary(Binary::Mul, grown, two);
                // A buffer only just begun grows a few times before it
                // holds anything worth copying; begin it with some room.
                let least = number(b, MINIMUM_CAPACITY);
                let small = b.compare(Relation::Less, doubled, least);
                let fresh_capacity = b.if_(
                    small,
                    &[W],
                    |b| b.yield_(&[least]),
                    |b| b.yield_(&[doubled]),
                )[0];
                let fresh = allocate(b, allocate_block, kinds, fresh_capacity, word.bytes);
                let slot = b.binary(Binary::Sub, fresh_capacity, grown);
                b.store(Width::Word, fresh, Offset::Words(3), slot);
                let stride = number(b, count(kinds.len()));
                let from_element = b.binary(Binary::Sub, capacity, len);
                let from = element_word(b, stride, from_element);
                let to_element = b.binary(Binary::Sub, fresh_capacity, len);
                let to = element_word(b, stride, to_element);
                let words = b.binary(Binary::Mul, len, stride);
                let zero = number(b, 0);
                // Scalars hold no claims: copying them is copying words.
                if kinds.iter().all(|&kind| kind == cell::SCALAR) {
                    b.loop_(&[zero], &[], |b, state| {
                        let at = state[0];
                        let done = b.compare(Relation::Equal, at, words);
                        b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                        let source = b.binary(Binary::Add, from, at);
                        let value = load_word(b, object, source, word_bits);
                        let target = b.binary(Binary::Add, to, at);
                        store_word(b, fresh, target, value, word_bits);
                        let next = b.binary(Binary::Add, at, one);
                        b.continue_(&[next]);
                    });
                    b.call(word.buffers, &[object]);
                    b.yield_(&[fresh]);
                    return;
                }
                b.loop_(&[zero], &[], |b, state| {
                    let at = state[0];
                    let done = b.compare(Relation::Equal, at, words);
                    b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                    let source = b.binary(Binary::Add, from, at);
                    let value = load_word(b, object, source, word_bits);
                    let leaf = b.binary(Binary::Mod, at, stride);
                    let kinds_start = number(b, KINDS);
                    let kind_word = b.binary(Binary::Add, kinds_start, leaf);
                    let kind = load_word(b, fresh, kind_word, word_bits);
                    let scalar = number(b, cell::SCALAR);
                    let plain = b.compare(Relation::Equal, kind, scalar);
                    // An immediate natural holds no claim to take.
                    let natural = number(b, cell::NATURAL);
                    let is_natural = b.compare(Relation::Equal, kind, natural);
                    let small = word.small(b, value);
                    let immediate = b.binary(Binary::Mul, is_natural, small);
                    let plain = b.binary(Binary::Add, plain, immediate);
                    b.if_(
                        plain,
                        &[],
                        |b| b.yield_(&[]),
                        |b| {
                            let held = b.convert(A, value);
                            b.call(retain, &[held]);
                            b.yield_(&[]);
                        },
                    );
                    let target = b.binary(Binary::Add, to, at);
                    store_word(b, fresh, target, value, word_bits);
                    let next = b.binary(Binary::Add, at, one);
                    b.continue_(&[next]);
                });
                b.call(word.buffers, &[object]);
                b.yield_(&[fresh]);
            },
        );
        b.ret(&answer);
    });
}
