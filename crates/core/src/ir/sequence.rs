//! Runtime support for sequence buffers.
//!
//! A sequence is a buffer, where in it the sequence starts, and how many
//! elements it has: the `len` elements from element `start`, in order. The
//! tail of a sequence is the same buffer from one element on, and any run of
//! one is the same buffer from somewhere else, so taking one apart copies
//! nothing. A buffer shares the natural runtime's allocation header, then:
//!
//! - word 2: its capacity, in elements;
//! - words 3 and 4: the first element it holds claims for, and one past the
//!   last, which every sequence of it lies between;
//! - word 5: its stride, the bytes from one element to the next;
//! - word 6: the address of its elements' descriptor, or nought where no
//!   leaf of an element holds a claim;
//! - the elements, `capacity` of them, each laid out as
//!   [`super::packing`] says, one stride apart.
//!
//! So a sequence of bytes is a run of bytes, in order, and one of any other
//! element is the run of them Rust would lay out, which a copy moves as
//! bytes. A buffer known before the program runs -- an empty one of each
//! element layout, and each known string -- is laid out in the image with
//! the all-ones count of a static object, so nothing writes it or frees it,
//! and nothing is built to make one.
//!
//! An element of a sequence, in a buffer nothing else holds, is the
//! sequence's to write over, giving up what it held; in a shared buffer the
//! sequence is copied first, as a push copies it.
//!
//! An element before a sequence's first, in a buffer nothing else holds, is
//! the sequence's to write: a push writes it in place, giving up whatever
//! claims a longer sequence left there. Otherwise, or where there is no room
//! in front, the sequence is copied to the end of a new buffer with as much
//! room again in front, and at least [`MINIMUM_CAPACITY`], so a run of
//! pushes copies each element a bounded number of times. Putting a
//! sequence's elements before another's makes room for all of them at once,
//! the same way, then copies them. A copy takes another claim to what each
//! element it copies holds, and a release gives them up, each walking the
//! descriptor, so a buffer of scalars walks nothing.
//!
//! Every routine answers one value and takes four at most, so that a machine
//! with a small frame holds each. Where a sequence starts after one grows is
//! worked out by its caller: before where it started, where the buffer is
//! the one it was handed, and otherwise as far from the new buffer's end as
//! the sequence is long, since a grown sequence ends its buffer.

use std::collections::BTreeMap;

use super::cell::{self, Claims, byte_offset, number};
use super::natural::{Helper, Library as NaturalLibrary};
use super::packing::Packed;
use super::{
    Binary, Builder, Class, DataId, FunctionId, Offset, Program, Relation, ValueId, Width,
};

const A: Class = Class::Address;
const W: Class = Class::Word;

const CAPACITY: i32 = 2;
const LOW: i32 = 3;
const HIGH: i32 = 4;
const STRIDE: i32 = 5;
const DESCRIPTOR: i32 = 6;
/// The word the elements begin at.
const ELEMENTS: u64 = 7;

/// The fewest elements a buffer grows to, so that one begun empty is not
/// copied at two elements, then four, then eight.
const MINIMUM_CAPACITY: u64 = 8;

/// What distinguishes one element layout from another to the runtime: its
/// stride and where its claims lie.
type Key = (u64, Vec<(u64, u64)>);

/// How a program grows or writes sequences of one layout, each asking for
/// a routine of its own, made only where the program does it that way.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Growth {
    /// One element before a sequence.
    Push,
    /// Another's elements, last first, before a sequence.
    Prepend,
    /// Another's elements after a sequence.
    Extend,
    /// One element of a sequence written over.
    Replace,
}

/// The generated routines: one release, one per way a layout is grown, and
/// the copies growing by another sequence's elements calls.
pub(super) struct Library {
    pub release: FunctionId,
    routines: BTreeMap<(Growth, Key), FunctionId>,
    copies: Option<Copies>,
    word_bits: u16,
}

/// Copying a run of elements, in order and last first.
#[derive(Clone, Copy)]
struct Copies {
    copy: FunctionId,
    copy_reversed: FunctionId,
}

/// Where a grown buffer puts the sequence it copies: at its end, with room
/// before for what is put in front, or at its start, with room after for
/// what follows.
#[derive(Clone, Copy)]
enum Placed {
    AtEnd,
    AtStart,
}

fn key(element: &Packed) -> Key {
    (element.size, element.managed().collect())
}

impl Library {
    /// Room for one element of `element` before the sequence of `len` from
    /// `start` of `buffer`, whose claim this takes: a buffer nothing else
    /// holds, and the element it is to be written at, where the longer
    /// sequence starts.
    ///
    /// Where no leaf holds a claim, the common case is written here rather
    /// than called: a buffer nothing else holds with room in front is
    /// written in place, and a scalar left there by a longer sequence holds
    /// no claim to give up. Anything else is the routine's.
    ///
    /// # Panics
    /// If the layout was not declared when the library was appended.
    pub(super) fn room(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        (buffer, start, len): (ValueId, ValueId, ValueId),
    ) -> [ValueId; 2] {
        let reserve = self.routines[&(Growth::Push, key(element))];
        let one = number(b, 1);
        if element.managed().next().is_some() {
            let room = b.call_one(reserve, &[buffer, start, len]);
            let front = started(b, (buffer, room), (start, len), one);
            return [room, front];
        }
        // Where the buffer is written in place, the sequence starts one
        // before; where the routine is called, this could not be, so it
        // grew, and the sequence ends the new buffer.
        let refs = b.load(Width::Word, buffer, Offset::Words(1));
        let alone = b.compare(Relation::Equal, refs, one);
        let zero = number(b, 0);
        let before = b.compare(Relation::Less, zero, start);
        let both = b.binary(Binary::Mul, alone, before);
        let answer = b.if_(
            both,
            &[A, W],
            |b| {
                let front = b.binary(Binary::Sub, start, one);
                b.yield_(&[buffer, front]);
            },
            |b| {
                let room = b.call_one(reserve, &[buffer, start, len]);
                let capacity = b.load(Width::Word, room, Offset::Words(CAPACITY));
                let longer = b.binary(Binary::Add, len, one);
                let front = b.binary(Binary::Sub, capacity, longer);
                b.yield_(&[room, front]);
            },
        );
        [answer[0], answer[1]]
    }

    /// The sequence of `len` from `start` of `buffer`, whose claim this
    /// takes, with its element `index`, below `len`, free to write: a
    /// buffer nothing else holds, where the sequence starts in it, and where
    /// the element lies. What the element held is given up.
    ///
    /// Where no leaf holds a claim, a buffer nothing else holds is written
    /// here rather than called for, as [`Library::room`] does.
    ///
    /// # Panics
    /// If the layout was not said to be written over.
    pub(super) fn replace(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        (buffer, start, len): (ValueId, ValueId, ValueId),
        index: ValueId,
    ) -> [ValueId; 3] {
        let own = self.routines[&(Growth::Replace, key(element))];
        let owned = if element.managed().next().is_some() {
            b.call_one(own, &[buffer, start, len, index])
        } else {
            let refs = b.load(Width::Word, buffer, Offset::Words(1));
            let one = number(b, 1);
            let alone = b.compare(Relation::Equal, refs, one);
            b.if_(
                alone,
                &[A],
                |b| b.yield_(&[buffer]),
                |b| {
                    let fresh = b.call_one(own, &[buffer, start, len, index]);
                    b.yield_(&[fresh]);
                },
            )[0]
        };
        let zero = number(b, 0);
        let front = started(b, (buffer, owned), (start, len), zero);
        let at = b.binary(Binary::Add, front, index);
        let written = self.element(b, owned, element.size, at);
        [owned, front, written]
    }

    /// The `count` elements from `from_start` of `from`, last first, put
    /// before the sequence of `len` from `start` of `buffer`, whose claim
    /// this takes: the buffer and where the joined sequence starts.
    ///
    /// # Panics
    /// If the layout was not said to be prepended to.
    pub(super) fn prepend(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        (buffer, start, len): (ValueId, ValueId, ValueId),
        (from, from_start, count): (ValueId, ValueId, ValueId),
    ) -> [ValueId; 2] {
        let routine = self.routines[&(Growth::Prepend, key(element))];
        let copies = self.copies.expect("growing by a sequence copies one");
        let room = b.call_one(routine, &[buffer, start, len, count]);
        let front = started(b, (buffer, room), (start, len), count);
        let into = self.element(b, room, element.size, front);
        let one = number(b, 1);
        let past = b.binary(Binary::Add, from_start, count);
        let last = b.binary(Binary::Sub, past, one);
        let last = self.element(b, from, element.size, last);
        b.call(copies.copy_reversed, &[last, into, count, room]);
        [room, front]
    }

    /// The sequence `first` followed by `then`, each a buffer, a start and
    /// a length, whose buffers' claims this takes: the other where one is
    /// empty, the first written after where its buffer has room and nothing
    /// else holds it, and otherwise both copied to the start of a buffer
    /// with room after. The buffer and where the joined sequence starts.
    ///
    /// # Panics
    /// If the layout was not said to be extended.
    pub(super) fn extend(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        (first, first_start, first_len): (ValueId, ValueId, ValueId),
        (then, then_start, then_len): (ValueId, ValueId, ValueId),
    ) -> [ValueId; 2] {
        let zero = number(b, 0);
        let no_first = b.compare(Relation::Equal, first_len, zero);
        let joined = b.if_(
            no_first,
            &[A, W],
            |b| {
                b.call(self.release, &[first]);
                b.yield_(&[then, then_start]);
            },
            |b| {
                let no_then = b.compare(Relation::Equal, then_len, zero);
                let joined = b.if_(
                    no_then,
                    &[A, W],
                    |b| {
                        b.call(self.release, &[then]);
                        b.yield_(&[first, first_start]);
                    },
                    |b| {
                        let joined = self.joined(
                            b,
                            element,
                            (first, first_start, first_len),
                            (then, then_start, then_len),
                        );
                        b.yield_(&joined);
                    },
                );
                b.yield_(&joined);
            },
        );
        [joined[0], joined[1]]
    }

    /// Two sequences neither of which is empty, joined as
    /// [`Library::extend`] joins them.
    fn joined(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        (first, first_start, first_len): (ValueId, ValueId, ValueId),
        (then, then_start, then_len): (ValueId, ValueId, ValueId),
    ) -> [ValueId; 2] {
        let after = self.routines[&(Growth::Extend, key(element))];
        let copies = self.copies.expect("growing by a sequence copies one");
        let room = b.call_one(after, &[first, first_start, first_len, then_len]);
        let was = b.convert(W, first);
        let is = b.convert(W, room);
        let same = b.compare(Relation::Equal, was, is);
        let start = b.if_(
            same,
            &[W],
            |b| b.yield_(&[first_start]),
            |b| {
                let zero = number(b, 0);
                b.yield_(&[zero]);
            },
        )[0];
        let end = b.binary(Binary::Add, start, first_len);
        let into = self.element(b, room, element.size, end);
        let from = self.element(b, then, element.size, then_start);
        b.call(copies.copy, &[from, into, then_len, room]);
        b.call(self.release, &[then]);
        [room, start]
    }

    /// Where element `index` of `buffer` begins, its stride known.
    pub(super) fn element(
        &self,
        b: &mut Builder<'_>,
        buffer: ValueId,
        stride: u64,
        index: ValueId,
    ) -> ValueId {
        let stride = number(b, stride);
        element_at(b, buffer, (stride, index), self.word_bits)
    }
}

/// Where a sequence of `len` from `start` starts once `added` elements are
/// put before it and its buffer has become `room`: `added` before, in the
/// buffer it was, and otherwise as far from the new one's end as it is now
/// long, which is where growing leaves it.
fn started(
    b: &mut Builder<'_>,
    (buffer, room): (ValueId, ValueId),
    (start, len): (ValueId, ValueId),
    added: ValueId,
) -> ValueId {
    let was = b.convert(W, buffer);
    let is = b.convert(W, room);
    let same = b.compare(Relation::Equal, was, is);
    b.if_(
        same,
        &[W],
        |b| {
            let front = b.binary(Binary::Sub, start, added);
            b.yield_(&[front]);
        },
        |b| {
            let capacity = b.load(Width::Word, room, Offset::Words(CAPACITY));
            let longer = b.binary(Binary::Add, len, added);
            let front = b.binary(Binary::Sub, capacity, longer);
            b.yield_(&[front]);
        },
    )[0]
}

/// Declare the release routine, so cells and buffers can release one
/// another before either is defined.
pub(super) fn declare(program: &mut Program) -> FunctionId {
    program.declare("seq.release", &[A], &[])
}

/// Define the release routine and one reservation per element layout.
pub(super) fn append(
    program: &mut Program,
    release: FunctionId,
    naturals: &NaturalLibrary,
    cells: cell::Library,
    wanted: impl IntoIterator<Item = (Growth, Packed, Option<DataId>)>,
    word_bits: u16,
) -> Library {
    let runtime = Runtime {
        claims: Claims {
            word_bits,
            retain: naturals.retain,
            naturals: naturals.release,
            cells: cells.release,
            buffers: Some(release),
        },
        release,
        block: naturals.release,
        allocate: naturals.require(Helper::Allocate),
        moving: define_move(program, word_bits),
    };
    define_release(program, runtime);
    let mut routines = BTreeMap::new();
    for (growth, element, descriptor) in wanted {
        let key = (growth, key(&element));
        if routines.contains_key(&key) {
            continue;
        }
        let id = define_growth(
            program,
            growth,
            (&element, descriptor),
            (runtime, routines.len()),
        );
        routines.insert(key, id);
    }
    let copies = routines
        .keys()
        .any(|(growth, _)| matches!(growth, Growth::Prepend | Growth::Extend))
        .then(|| define_copies(program, runtime));
    Library {
        release,
        routines,
        copies,
        word_bits,
    }
}

/// The routine growing sequences of one layout one way, the `n`th made.
fn define_growth(
    program: &mut Program,
    growth: Growth,
    layout: (&Packed, Option<DataId>),
    (runtime, n): (Runtime, usize),
) -> FunctionId {
    match growth {
        Growth::Push => {
            let id = program.declare(&format!("seq.reserve.{n}"), &[A, W, W], &[A]);
            define_reserve(program, id, layout, runtime);
            id
        }
        Growth::Prepend => {
            let id = program.declare(&format!("seq.room.{n}"), &[A, W, W, W], &[A]);
            define_room(program, id, layout, runtime);
            id
        }
        Growth::Extend => {
            let id = program.declare(&format!("seq.after.{n}"), &[A, W, W, W], &[A]);
            define_after(program, id, layout, runtime);
            id
        }
        Growth::Replace => {
            let id = program.declare(&format!("seq.own.{n}"), &[A, W, W, W], &[A]);
            define_own(program, id, layout, runtime);
            id
        }
    }
}

/// What every routine here calls on.
#[derive(Clone, Copy)]
struct Runtime {
    claims: Claims,
    /// Releases a buffer.
    release: FunctionId,
    /// Gives up the block an object lies in.
    block: FunctionId,
    allocate: FunctionId,
    /// `seq.move(source, dest, bytes)`.
    moving: FunctionId,
}

impl Runtime {
    const fn word_bits(self) -> u16 {
        self.claims.word_bits
    }

    /// Give up the claims elements `from` up to `to` of `object` hold, as
    /// `descriptor` lists them, where it lists any.
    fn release_elements(
        self,
        b: &mut Builder<'_>,
        (object, descriptor): (ValueId, ValueId),
        (from, to): (ValueId, ValueId),
    ) {
        let zero = number(b, 0);
        let none = b.compare(Relation::Equal, descriptor, zero);
        b.if_(
            none,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let descriptor = b.convert(A, descriptor);
                let stride = b.load(Width::Word, object, Offset::Words(STRIDE));
                b.loop_(&[from], &[], |b, state| {
                    let at = state[0];
                    let more = b.compare(Relation::Less, at, to);
                    b.if_(more, &[], |b| b.yield_(&[]), |b| b.break_(&[]));
                    let element = element_at(b, object, (stride, at), self.word_bits());
                    self.claims
                        .each(b, (descriptor, element), &mut |b, kind, value| {
                            self.claims.release_by_kind(b, kind, value);
                        });
                    let one = number(b, 1);
                    let next = b.binary(Binary::Add, at, one);
                    b.continue_(&[next]);
                });
                b.yield_(&[]);
            },
        );
    }

    /// Count elements `from` up to `to` of `object` as holding claims from
    /// now on, giving up what any of them held before.
    fn claim_slots(self, b: &mut Builder<'_>, object: ValueId, (from, to): (ValueId, ValueId)) {
        let low = b.load(Width::Word, object, Offset::Words(LOW));
        let high = b.load(Width::Word, object, Offset::Words(HIGH));
        let descriptor = b.load(Width::Word, object, Offset::Words(DESCRIPTOR));
        let stale_from = greater(b, low, from);
        let stale_to = lesser(b, high, to);
        self.release_elements(b, (object, descriptor), (stale_from, stale_to));
        let low = lesser(b, low, from);
        let high = greater(b, high, to);
        b.store(Width::Word, object, Offset::Words(LOW), low);
        b.store(Width::Word, object, Offset::Words(HIGH), high);
    }

    /// A buffer of `layout` with room for `total` elements and as many
    /// again, and at least [`MINIMUM_CAPACITY`], holding the `len` elements
    /// from `start` of `object` where `placed` says, with claims to what
    /// they hold; the `total` less `len` beside them are counted as holding
    /// claims and free to write. `object` is given up.
    fn grown(
        self,
        b: &mut Builder<'_>,
        (object, start, len): (ValueId, ValueId, ValueId),
        (total, (stride, descriptor)): (ValueId, (ValueId, ValueId)),
        placed: Placed,
    ) -> ValueId {
        let two = number(b, 2);
        let doubled = b.binary(Binary::Mul, total, two);
        let least = number(b, MINIMUM_CAPACITY);
        let capacity = greater(b, doubled, least);
        let word_bytes = u64::from(self.word_bits() / 8);
        let fresh = allocate(b, self.allocate, (stride, descriptor), capacity, word_bytes);
        let (first, at) = match placed {
            Placed::AtEnd => {
                let first = b.binary(Binary::Sub, capacity, total);
                (first, b.binary(Binary::Sub, capacity, len))
            }
            Placed::AtStart => {
                let zero = number(b, 0);
                (zero, zero)
            }
        };
        let high = b.binary(Binary::Add, first, total);
        b.store(Width::Word, fresh, Offset::Words(LOW), first);
        b.store(Width::Word, fresh, Offset::Words(HIGH), high);
        let from = element_at(b, object, (stride, start), self.word_bits());
        let to = element_at(b, fresh, (stride, at), self.word_bits());
        let bytes = b.binary(Binary::Mul, len, stride);
        b.call(self.moving, &[from, to, bytes]);
        claim_run(b, self, (to, len), (stride, descriptor));
        b.call(self.release, &[object]);
        fresh
    }
}

/// The greater of two words.
fn greater(b: &mut Builder<'_>, left: ValueId, right: ValueId) -> ValueId {
    let less = b.compare(Relation::Less, left, right);
    b.if_(less, &[W], |b| b.yield_(&[right]), |b| b.yield_(&[left]))[0]
}

/// The lesser of two words.
fn lesser(b: &mut Builder<'_>, left: ValueId, right: ValueId) -> ValueId {
    let less = b.compare(Relation::Less, left, right);
    b.if_(less, &[W], |b| b.yield_(&[left]), |b| b.yield_(&[right]))[0]
}

/// Where element `index` of `object` begins, its elements `stride` apart.
fn element_at(
    b: &mut Builder<'_>,
    object: ValueId,
    (stride, index): (ValueId, ValueId),
    word_bits: u16,
) -> ValueId {
    let header = number(b, ELEMENTS * u64::from(word_bits / 8));
    let skipped = b.binary(Binary::Mul, index, stride);
    let bytes = b.binary(Binary::Add, header, skipped);
    byte_offset(b, object, bytes)
}

/// Allocate a buffer with room for `capacity` elements one `stride` apart,
/// described by `descriptor`, holding none of them yet and claims for none.
/// `allocate` takes the bytes after the header's third word.
pub(super) fn allocate(
    b: &mut Builder<'_>,
    allocate: FunctionId,
    (stride, descriptor): (ValueId, ValueId),
    capacity: ValueId,
    word_bytes: u64,
) -> ValueId {
    let elements = b.binary(Binary::Mul, capacity, stride);
    let fixed = number(b, (ELEMENTS - 3) * word_bytes);
    let bytes = b.binary(Binary::Add, elements, fixed);
    let object = b.call_one(allocate, &[bytes]);
    let none = number(b, 0);
    b.store(Width::Word, object, Offset::Words(CAPACITY), capacity);
    b.store(Width::Word, object, Offset::Words(LOW), capacity);
    b.store(Width::Word, object, Offset::Words(HIGH), none);
    b.store(Width::Word, object, Offset::Words(STRIDE), stride);
    b.store(Width::Word, object, Offset::Words(DESCRIPTOR), descriptor);
    object
}

/// `seq.move(source, dest, bytes)`: copy a run of bytes, a word at a time
/// while a word is left and a byte at a time after.
fn define_move(program: &mut Program, word_bits: u16) -> FunctionId {
    let word = u64::from(word_bits / 8);
    let id = program.declare("seq.move", &[A, A, W], &[]);
    program.define(id, |b, args| {
        let (source, dest, bytes) = (args[0], args[1], args[2]);
        let zero = number(b, 0);
        let whole = number(b, word);
        let tail = b.binary(Binary::Mod, bytes, whole);
        let words = b.binary(Binary::Sub, bytes, tail);
        let copy = |b: &mut Builder<'_>, (from, to): (ValueId, ValueId), width, step| {
            b.loop_(&[from], &[], |b, state| {
                let at = state[0];
                let done = b.compare(Relation::Equal, at, to);
                b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                let read = byte_offset(b, source, at);
                let value = b.load(width, read, Offset::Words(0));
                let write = byte_offset(b, dest, at);
                b.store(width, write, Offset::Words(0), value);
                let step = number(b, step);
                let next = b.binary(Binary::Add, at, step);
                b.continue_(&[next]);
            });
        };
        copy(b, (zero, words), Width::Word, word);
        copy(b, (words, bytes), Width::Byte, 1);
        b.ret(&[]);
    });
    id
}

/// Release a buffer: where this is the last claim, every element it holds
/// claims for, then the block.
fn define_release(program: &mut Program, runtime: Runtime) {
    program.define(runtime.release, |b, args| {
        let object = args[0];
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let one = number(b, 1);
        let last = b.compare(Relation::Equal, refs, one);
        b.if_(
            last,
            &[],
            |b| {
                let low = b.load(Width::Word, object, Offset::Words(LOW));
                let high = b.load(Width::Word, object, Offset::Words(HIGH));
                let descriptor = b.load(Width::Word, object, Offset::Words(DESCRIPTOR));
                runtime.release_elements(b, (object, descriptor), (low, high));
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.call(runtime.block, &[object]);
        b.ret(&[]);
    });
}

/// `seq.reserve.n(object, start, len)`: room for one element of `element`
/// before the sequence of `len` from `start` of a buffer whose claim this
/// takes, answering a buffer nothing else holds whose element before where
/// the sequence then starts holds no claim.
fn define_reserve(
    program: &mut Program,
    id: FunctionId,
    (element, descriptor): (&Packed, Option<DataId>),
    runtime: Runtime,
) {
    program.define(id, |b, args| {
        let (object, start, len) = (args[0], args[1], args[2]);
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let one = number(b, 1);
        let alone = b.compare(Relation::Equal, refs, one);
        let zero = number(b, 0);
        let before = b.compare(Relation::Less, zero, start);
        let both = b.binary(Binary::Mul, alone, before);
        let answer = b.if_(
            both,
            &[A],
            |b| {
                // Nothing else can see this buffer, so the element in front
                // of the sequence is ours: free it of whatever a longer
                // sequence left there, and count it as held from now on.
                if descriptor.is_some() {
                    let slot = b.binary(Binary::Sub, start, one);
                    runtime.claim_slots(b, object, (slot, start));
                }
                b.yield_(&[object]);
            },
            |b| {
                // Shared, or with no room in front: copy the sequence to the
                // end of a buffer with as much room again in front.
                let layout = static_layout(b, element, descriptor);
                let total = b.binary(Binary::Add, len, one);
                let fresh = runtime.grown(b, (object, start, len), (total, layout), Placed::AtEnd);
                b.yield_(&[fresh]);
            },
        );
        b.ret(&answer);
    });
}

/// A layout's stride and descriptor, known before the program runs, as the
/// words a buffer's header holds them in.
fn static_layout(
    b: &mut Builder<'_>,
    element: &Packed,
    descriptor: Option<DataId>,
) -> (ValueId, ValueId) {
    let stride = number(b, element.size);
    let described = match descriptor {
        Some(data) => {
            let at = b.address_of(data);
            b.convert(W, at)
        }
        None => number(b, 0),
    };
    (stride, described)
}

/// Define the copies growing by another sequence's elements calls.
fn define_copies(program: &mut Program, runtime: Runtime) -> Copies {
    let copy = program.declare("seq.copy", &[A, A, W, A], &[]);
    define_copy(program, copy, runtime);
    let copy_reversed = program.declare("seq.copy_reversed", &[A, A, W, A], &[]);
    define_copy_reversed(program, copy_reversed, runtime);
    Copies {
        copy,
        copy_reversed,
    }
}

/// `seq.room.n(target, start, len, count)`: a buffer nothing else holds with
/// room for `count` elements of `element` before the sequence of `len` from
/// `start` of `target`, whose claim this takes, and those elements counted
/// as holding claims and free to write.
///
/// One nothing else holds with that room is written in place, giving up
/// whatever claims a longer sequence left there. Otherwise its elements are
/// copied to the end of one with as much room again, and at least
/// [`MINIMUM_CAPACITY`], as a push would.
fn define_room(
    program: &mut Program,
    id: FunctionId,
    (element, descriptor): (&Packed, Option<DataId>),
    runtime: Runtime,
) {
    program.define(id, |b, args| {
        let (target, start, len, count) = (args[0], args[1], args[2], args[3]);
        let one = number(b, 1);
        let refs = b.load(Width::Word, target, Offset::Words(1));
        let alone = b.compare(Relation::Equal, refs, one);
        let short = b.compare(Relation::Less, start, count);
        let room = b.binary(Binary::Sub, one, short);
        let both = b.binary(Binary::Mul, alone, room);
        b.if_(
            both,
            &[],
            |b| {
                let first = b.binary(Binary::Sub, start, count);
                runtime.claim_slots(b, target, (first, start));
                b.ret(&[target]);
            },
            |b| b.yield_(&[]),
        );
        let layout = static_layout(b, element, descriptor);
        let total = b.binary(Binary::Add, len, count);
        let fresh = runtime.grown(b, (target, start, len), (total, layout), Placed::AtEnd);
        b.ret(&[fresh]);
    });
}

/// `seq.after.n(object, start, len, count)`: a buffer nothing else holds
/// with room for `count` elements of `element` after the sequence of `len`
/// from `start` of `object`, whose claim this takes, and those elements
/// counted as holding claims and free to write.
///
/// One nothing else holds with that room is written in place, giving up
/// whatever claims a longer sequence left there. Otherwise its elements are
/// copied to the start of one with as much room again after, and at least
/// [`MINIMUM_CAPACITY`], so a run of appends copies each element a bounded
/// number of times.
fn define_after(
    program: &mut Program,
    id: FunctionId,
    (element, descriptor): (&Packed, Option<DataId>),
    runtime: Runtime,
) {
    program.define(id, |b, args| {
        let (object, start, len, count) = (args[0], args[1], args[2], args[3]);
        let one = number(b, 1);
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let alone = b.compare(Relation::Equal, refs, one);
        let capacity = b.load(Width::Word, object, Offset::Words(CAPACITY));
        let end = b.binary(Binary::Add, start, len);
        let past = b.binary(Binary::Add, end, count);
        let short = b.compare(Relation::Less, capacity, past);
        let room = b.binary(Binary::Sub, one, short);
        let both = b.binary(Binary::Mul, alone, room);
        b.if_(
            both,
            &[],
            |b| {
                runtime.claim_slots(b, object, (end, past));
                b.ret(&[object]);
            },
            |b| b.yield_(&[]),
        );
        let layout = static_layout(b, element, descriptor);
        let total = b.binary(Binary::Add, len, count);
        let fresh = runtime.grown(b, (object, start, len), (total, layout), Placed::AtStart);
        b.ret(&[fresh]);
    });
}

/// `seq.own.n(object, start, len, index)`: a buffer nothing else holds
/// holding the sequence of `len` from `start` of `object`, whose claim this
/// takes, with what its element `index` holds given up, free to write.
///
/// One nothing else holds is the answer. Otherwise its elements are copied
/// to the end of one with as much room again in front, and at least
/// [`MINIMUM_CAPACITY`], as a push would, each claimed again, and the
/// copy's element `index` gives up what it was just claimed for.
fn define_own(
    program: &mut Program,
    id: FunctionId,
    (element, descriptor): (&Packed, Option<DataId>),
    runtime: Runtime,
) {
    program.define(id, |b, args| {
        let (object, start, len, index) = (args[0], args[1], args[2], args[3]);
        let one = number(b, 1);
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let alone = b.compare(Relation::Equal, refs, one);
        let (owned, first) = {
            let answer = b.if_(
                alone,
                &[A, W],
                |b| b.yield_(&[object, start]),
                |b| {
                    let layout = static_layout(b, element, descriptor);
                    let fresh =
                        runtime.grown(b, (object, start, len), (len, layout), Placed::AtEnd);
                    let capacity = b.load(Width::Word, fresh, Offset::Words(CAPACITY));
                    let first = b.binary(Binary::Sub, capacity, len);
                    b.yield_(&[fresh, first]);
                },
            );
            (answer[0], answer[1])
        };
        if descriptor.is_some() {
            let described = b.load(Width::Word, owned, Offset::Words(DESCRIPTOR));
            let at = b.binary(Binary::Add, first, index);
            let past = b.binary(Binary::Add, at, one);
            runtime.release_elements(b, (owned, described), (at, past));
        }
        b.ret(&[owned]);
    });
}

/// `seq.copy(source, dest, count, like)`: copy `count` elements of `like`'s
/// layout, taking another claim to what each holds. A layout of scalars is
/// a copy of bytes and nothing else.
fn define_copy(program: &mut Program, id: FunctionId, runtime: Runtime) {
    program.define(id, |b, args| {
        let (source, dest, count, like) = (args[0], args[1], args[2], args[3]);
        let stride = b.load(Width::Word, like, Offset::Words(STRIDE));
        let described = b.load(Width::Word, like, Offset::Words(DESCRIPTOR));
        let bytes = b.binary(Binary::Mul, count, stride);
        b.call(runtime.moving, &[source, dest, bytes]);
        claim_run(b, runtime, (dest, count), (stride, described));
        b.ret(&[]);
    });
}

/// `seq.copy_reversed(last, dest, count, like)`: copy `count` elements
/// ending with the one at `last`, last first, taking another claim to what
/// each holds.
fn define_copy_reversed(program: &mut Program, id: FunctionId, runtime: Runtime) {
    program.define(id, |b, args| {
        let (last, dest, count, like) = (args[0], args[1], args[2], args[3]);
        let stride = b.load(Width::Word, like, Offset::Words(STRIDE));
        let described = b.load(Width::Word, like, Offset::Words(DESCRIPTOR));
        let zero = number(b, 0);
        b.loop_(&[zero], &[], |b, state| {
            let at = state[0];
            let done = b.compare(Relation::Equal, at, count);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let distance = b.binary(Binary::Mul, at, stride);
            let read = b.convert(W, last);
            let read = b.binary(Binary::Sub, read, distance);
            let read = b.convert(A, read);
            let write = byte_offset(b, dest, distance);
            b.call(runtime.moving, &[read, write, stride]);
            let one = number(b, 1);
            let next = b.binary(Binary::Add, at, one);
            b.continue_(&[next]);
        });
        claim_run(b, runtime, (dest, count), (stride, described));
        b.ret(&[]);
    });
}

/// Take another claim to what each of `count` elements from `dest` holds,
/// as `described` lists, where it lists anything.
fn claim_run(
    b: &mut Builder<'_>,
    runtime: Runtime,
    (dest, count): (ValueId, ValueId),
    (stride, described): (ValueId, ValueId),
) {
    let zero = number(b, 0);
    let none = b.compare(Relation::Equal, described, zero);
    b.if_(
        none,
        &[],
        |b| b.yield_(&[]),
        |b| {
            let descriptor = b.convert(A, described);
            b.loop_(&[zero], &[], |b, state| {
                let at = state[0];
                let done = b.compare(Relation::Equal, at, count);
                b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                let distance = b.binary(Binary::Mul, at, stride);
                let element = byte_offset(b, dest, distance);
                runtime
                    .claims
                    .each(b, (descriptor, element), &mut |b, kind, value| {
                        runtime.claims.claim(b, kind, value);
                    });
                let one = number(b, 1);
                let next = b.binary(Binary::Add, at, one);
                b.continue_(&[next]);
            });
            b.yield_(&[]);
        },
    );
}
