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
//! - word 4: its stride, the bytes from one element to the next;
//! - word 5: the address of its elements' descriptor, or nought where no
//!   leaf of an element holds a claim;
//! - the elements, `capacity` of them, each laid out as
//!   [`super::packing`] says, one stride apart.
//!
//! So a sequence of bytes is a run of bytes, in order, and one of any other
//! element is the run of them Rust would lay out, which a copy moves as
//! bytes.
//!
//! Pushing onto a buffer nothing else holds writes into the free element in
//! front of the sequence, giving up whatever an earlier, longer sequence
//! left there. Otherwise, or where there is no room, the sequence is copied
//! into a new buffer with as much room in front as it has elements, and at
//! least [`MINIMUM_CAPACITY`], so a run of pushes copies each element a
//! bounded number of times. Putting a sequence's elements before another's
//! makes room for all of them at once, the same way, then copies them. A
//! copy takes another claim to what each element it copies holds, and a
//! release gives them up, each walking the descriptor, so a buffer of
//! scalars walks nothing.

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
const STRIDE: i32 = 4;
const DESCRIPTOR: i32 = 5;
/// The word the elements begin at.
const ELEMENTS: u64 = 6;

/// The fewest elements a buffer grows to, so that one begun empty is not
/// copied at two elements, then four, then eight.
const MINIMUM_CAPACITY: u64 = 8;

/// What distinguishes one element layout from another to the runtime: its
/// stride and where its claims lie.
type Key = (u64, Vec<(u64, u64)>);

/// The generated routines: one release, and one reservation per element
/// layout.
pub(super) struct Library {
    pub release: FunctionId,
    reserve: BTreeMap<Key, FunctionId>,
    /// Putting a sequence's elements before another's, in order and
    /// reversed, where the program does.
    prepend: Option<[FunctionId; 2]>,
    word_bits: u16,
}

fn key(element: &Packed) -> Key {
    (element.size, element.managed().collect())
}

impl Library {
    /// The routine putting a sequence's elements before another's: in
    /// order, or reversed.
    ///
    /// # Panics
    /// If the program was not said to prepend when the library was appended.
    pub(super) fn prepend(&self, reversed: bool) -> FunctionId {
        self.prepend.expect("prepending was requested")[usize::from(reversed)]
    }

    /// Make room for one element of `element` in front of the last `len`
    /// elements of `buffer`, whose claim this takes, as the reservation
    /// routine does: answering a buffer nothing else holds with that slot
    /// free.
    ///
    /// Where no leaf holds a claim, the common case is written here rather
    /// than called: a buffer nothing else holds with room in front is
    /// written in place, and the slot needs only counting as held, since a
    /// scalar left there by a longer sequence holds no claim to give up.
    /// Anything else is the routine's.
    ///
    /// # Panics
    /// If the layout was not declared when the library was appended.
    pub(super) fn room(
        &self,
        b: &mut Builder<'_>,
        element: &Packed,
        buffer: ValueId,
        len: ValueId,
    ) -> ValueId {
        let reserve = self.reserve[&key(element)];
        if element.managed().next().is_some() {
            return b.call_one(reserve, &[buffer, len]);
        }
        let refs = b.load(Width::Word, buffer, Offset::Words(1));
        let capacity = b.load(Width::Word, buffer, Offset::Words(CAPACITY));
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
                let low = b.load(Width::Word, buffer, Offset::Words(LOW));
                let fresh = b.compare(Relation::Less, slot, low);
                b.if_(
                    fresh,
                    &[],
                    |b| {
                        b.store(Width::Word, buffer, Offset::Words(LOW), slot);
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

    /// The capacity of `buffer`, in elements.
    pub(super) fn capacity(b: &mut Builder<'_>, buffer: ValueId) -> ValueId {
        b.load(Width::Word, buffer, Offset::Words(CAPACITY))
    }
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
    elements: impl IntoIterator<Item = (Packed, Option<DataId>)>,
    (word_bits, prepends): (u16, bool),
) -> Library {
    let claims = Claims {
        word_bits,
        retain: naturals.retain,
        naturals: naturals.release,
        half: naturals.half,
        cells: cells.release,
        buffers: Some(release),
    };
    let allocate = naturals.require(Helper::Allocate);
    let moving = define_move(program, word_bits);
    let runtime = Runtime {
        claims,
        release,
        block: naturals.release,
        allocate,
        moving,
    };
    define_release(program, runtime);
    let mut reserve = BTreeMap::new();
    for (element, descriptor) in elements {
        let key = key(&element);
        if reserve.contains_key(&key) {
            continue;
        }
        let name = format!("seq.reserve.{}", reserve.len());
        let id = program.declare(&name, &[A, W], &[A]);
        define_reserve(program, id, (&element, descriptor), runtime);
        reserve.insert(key, id);
    }
    let prepend = prepends.then(|| define_prepending(program, runtime));
    Library {
        release,
        reserve,
        prepend,
        word_bits,
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
    fn word_bytes(self) -> u64 {
        u64::from(self.claims.word_bits / 8)
    }

    /// Give up the claims elements `from` up to `to` of `object` hold, as
    /// `descriptor` lists them, where it lists any.
    fn release_elements(
        self,
        b: &mut Builder<'_>,
        (object, descriptor): (ValueId, ValueId),
        (from, to): (ValueId, ValueId),
    ) {
        self.each_element(
            b,
            (object, descriptor),
            (from, to),
            &mut |b, kind, value| {
                self.claims.release_by_kind(b, kind, value);
            },
        );
    }

    /// Take another claim to what elements `from` up to `to` of `object`
    /// hold, as `descriptor` lists them, where it lists any.
    fn claim_elements(
        self,
        b: &mut Builder<'_>,
        (object, descriptor): (ValueId, ValueId),
        (from, to): (ValueId, ValueId),
    ) {
        self.each_element(
            b,
            (object, descriptor),
            (from, to),
            &mut |b, kind, value| {
                self.claims.claim(b, kind, value);
            },
        );
    }

    fn each_element(
        self,
        b: &mut Builder<'_>,
        (object, descriptor): (ValueId, ValueId),
        (from, to): (ValueId, ValueId),
        each: &mut dyn FnMut(&mut Builder<'_>, ValueId, ValueId),
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
                    let done = b.compare(Relation::Equal, at, to);
                    b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                    let element = element_at(b, object, (stride, at), self.claims.word_bits);
                    self.claims.each(b, (descriptor, element), each);
                    let one = number(b, 1);
                    let next = b.binary(Binary::Add, at, one);
                    b.continue_(&[next]);
                });
                b.yield_(&[]);
            },
        );
    }

    /// A buffer with room for `capacity` elements one `stride` apart,
    /// described by `descriptor`, holding none of them yet.
    fn allocate(
        self,
        b: &mut Builder<'_>,
        (stride, descriptor): (ValueId, ValueId),
        capacity: ValueId,
    ) -> ValueId {
        allocate(
            b,
            self.allocate,
            (stride, descriptor),
            capacity,
            self.word_bytes(),
        )
    }
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
/// described by `descriptor`, holding none of them yet. `allocate` takes
/// the bytes after the header's third word.
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
    b.store(Width::Word, object, Offset::Words(CAPACITY), capacity);
    b.store(Width::Word, object, Offset::Words(LOW), capacity);
    b.store(Width::Word, object, Offset::Words(STRIDE), stride);
    b.store(Width::Word, object, Offset::Words(DESCRIPTOR), descriptor);
    object
}

/// A buffer holding nothing, and room for nothing: whatever is first pushed
/// onto it makes a buffer of its own layout.
pub(super) fn empty(b: &mut Builder<'_>, allocate_block: FunctionId, word_bytes: u64) -> ValueId {
    let none = number(b, 0);
    allocate(b, allocate_block, (none, none), none, word_bytes)
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
                let capacity = b.load(Width::Word, object, Offset::Words(CAPACITY));
                let low = b.load(Width::Word, object, Offset::Words(LOW));
                let descriptor = b.load(Width::Word, object, Offset::Words(DESCRIPTOR));
                runtime.release_elements(b, (object, descriptor), (low, capacity));
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.call(runtime.block, &[object]);
        b.ret(&[]);
    });
}

/// Make room for one element of `element` in front of the last `len`
/// elements of a buffer whose claim this takes, answering a buffer nothing
/// else holds whose element at `capacity - len - 1` holds no claim.
#[expect(
    clippy::too_many_lines,
    reason = "the in-place and copying paths share one routine's layout"
)]
fn define_reserve(
    program: &mut Program,
    id: FunctionId,
    (element, descriptor): (&Packed, Option<DataId>),
    runtime: Runtime,
) {
    let word_bits = runtime.claims.word_bits;
    program.define(id, |b, args| {
        let (object, len) = (args[0], args[1]);
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let capacity = b.load(Width::Word, object, Offset::Words(CAPACITY));
        let one = number(b, 1);
        let alone = b.compare(Relation::Equal, refs, one);
        let room = b.compare(Relation::Less, len, capacity);
        let both = b.binary(Binary::Mul, alone, room);
        let stride = number(b, element.size);
        let answer = b.if_(
            both,
            &[A],
            |b| {
                // Nothing else can see this buffer, so the element in front
                // of the sequence is ours: free it of whatever a longer
                // sequence left there, or count it as held from now on.
                let before = b.binary(Binary::Sub, capacity, len);
                let slot = b.binary(Binary::Sub, before, one);
                let low = b.load(Width::Word, object, Offset::Words(LOW));
                let fresh = b.compare(Relation::Less, slot, low);
                b.if_(
                    fresh,
                    &[],
                    |b| {
                        b.store(Width::Word, object, Offset::Words(LOW), slot);
                        b.yield_(&[]);
                    },
                    |b| {
                        let at = element_at(b, object, (stride, slot), word_bits);
                        for (offset, kind) in element.managed() {
                            let offset = i32::try_from(offset).expect("a small element");
                            let value = b.load(Width::Word, at, Offset::Bytes(offset));
                            runtime.claims.release(b, kind, value);
                        }
                        b.yield_(&[]);
                    },
                );
                b.yield_(&[object]);
            },
            |b| {
                // Shared or full: copy the sequence to the end of a buffer
                // with as much room again in front, holding a claim to what
                // each element it copies holds, then give up this one.
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
                let described = match descriptor {
                    Some(data) => {
                        let at = b.address_of(data);
                        b.convert(W, at)
                    }
                    None => number(b, 0),
                };
                let fresh = runtime.allocate(b, (stride, described), fresh_capacity);
                let slot = b.binary(Binary::Sub, fresh_capacity, grown);
                b.store(Width::Word, fresh, Offset::Words(LOW), slot);
                let from_element = b.binary(Binary::Sub, capacity, len);
                let from = element_at(b, object, (stride, from_element), word_bits);
                let to_element = b.binary(Binary::Sub, fresh_capacity, len);
                let to = element_at(b, fresh, (stride, to_element), word_bits);
                let bytes = b.binary(Binary::Mul, len, stride);
                b.call(runtime.moving, &[from, to, bytes]);
                if descriptor.is_some() {
                    runtime.claim_elements(b, (fresh, described), (to_element, fresh_capacity));
                }
                b.call(runtime.release, &[object]);
                b.yield_(&[fresh]);
            },
        );
        b.ret(&answer);
    });
}

/// The routines putting one sequence's elements before another's.
///
/// Each is small, so that a machine with a small frame holds it: one makes
/// room, two copy a run of elements -- in order, and last first -- and the
/// two entries call them. Every one takes four arguments at most. Each reads
/// the layout from the buffers it is handed rather than being made one per
/// layout.
#[derive(Clone, Copy)]
struct Prepending {
    room: FunctionId,
    copy: FunctionId,
    copy_reversed: FunctionId,
}

/// Define both prepending entries and what they call.
fn define_prepending(program: &mut Program, runtime: Runtime) -> [FunctionId; 2] {
    let copy = program.declare("seq.copy", &[A, A, W, A], &[]);
    define_copy(program, copy, runtime);
    let copy_reversed = program.declare("seq.copy_reversed", &[A, A, W, A], &[]);
    define_copy_reversed(program, copy_reversed, runtime);
    let room = program.declare("seq.room", &[A, W, A, W], &[A]);
    define_room(program, room, (copy, runtime));
    let routines = Prepending {
        room,
        copy,
        copy_reversed,
    };
    [false, true].map(|reversed| {
        let name = if reversed {
            "seq.prepend_reversed"
        } else {
            "seq.prepend"
        };
        let id = program.declare(name, &[A, W, A, W], &[A]);
        define_prepend(program, id, runtime, routines, reversed);
        id
    })
}

/// Put the last `count` elements of `from` before the last `len` of a
/// buffer whose claim this takes, in order or reversed, answering the
/// buffer holding them all.
fn define_prepend(
    program: &mut Program,
    id: FunctionId,
    runtime: Runtime,
    routines: Prepending,
    reversed: bool,
) {
    let word_bits = runtime.claims.word_bits;
    program.define(id, |b, args| {
        let (target, len, from, count) = (args[0], args[1], args[2], args[3]);
        let zero = number(b, 0);
        let nothing = b.compare(Relation::Equal, count, zero);
        b.if_(nothing, &[], |b| b.ret(&[target]), |b| b.yield_(&[]));
        let dest = b.call_one(routines.room, &[target, len, from, count]);
        let stride = b.load(Width::Word, from, Offset::Words(STRIDE));
        let dest_capacity = b.load(Width::Word, dest, Offset::Words(CAPACITY));
        let dest_free = b.binary(Binary::Sub, dest_capacity, len);
        let into = b.binary(Binary::Sub, dest_free, count);
        let into = element_at(b, dest, (stride, into), word_bits);
        let from_capacity = b.load(Width::Word, from, Offset::Words(CAPACITY));
        if reversed {
            let one = number(b, 1);
            let last = b.binary(Binary::Sub, from_capacity, one);
            let last = element_at(b, from, (stride, last), word_bits);
            b.call(routines.copy_reversed, &[last, into, count, from]);
        } else {
            let first = b.binary(Binary::Sub, from_capacity, count);
            let first = element_at(b, from, (stride, first), word_bits);
            b.call(routines.copy, &[first, into, count, from]);
        }
        b.ret(&[dest]);
    });
}

/// `seq.room(target, len, from, count)`: a buffer nothing else holds with
/// room for `count` elements of `from`'s layout before the last `len` of
/// `target`, whose claim this takes.
///
/// The layout is read from `from`, which holds at least one element and so
/// was made with it; `target` may be one begun empty, which says none. One
/// nothing else holds with that room is written in place, giving up
/// whatever claims a longer sequence left there. Otherwise its elements are
/// copied into one with as much room again, and at least
/// [`MINIMUM_CAPACITY`], as a push would.
#[expect(
    clippy::too_many_lines,
    reason = "the in-place and growing paths share the room they make"
)]
fn define_room(program: &mut Program, id: FunctionId, (copy, runtime): (FunctionId, Runtime)) {
    let word_bits = runtime.claims.word_bits;
    program.define(id, |b, args| {
        let (target, len, from, count) = (args[0], args[1], args[2], args[3]);
        let one = number(b, 1);
        let stride = b.load(Width::Word, from, Offset::Words(STRIDE));
        let described = b.load(Width::Word, from, Offset::Words(DESCRIPTOR));
        let refs = b.load(Width::Word, target, Offset::Words(1));
        let capacity = b.load(Width::Word, target, Offset::Words(CAPACITY));
        let alone = b.compare(Relation::Equal, refs, one);
        let free = b.binary(Binary::Sub, capacity, len);
        let short = b.compare(Relation::Less, free, count);
        let room = b.binary(Binary::Sub, one, short);
        let both = b.binary(Binary::Mul, alone, room);
        b.if_(
            both,
            &[],
            |b| {
                let start = b.binary(Binary::Sub, free, count);
                let low = b.load(Width::Word, target, Offset::Words(LOW));
                let below = b.compare(Relation::Less, start, low);
                b.if_(
                    below,
                    &[],
                    |b| {
                        // Nothing below the lowest claimed element holds one.
                        b.store(Width::Word, target, Offset::Words(LOW), start);
                        runtime.release_elements(b, (target, described), (low, free));
                        b.yield_(&[]);
                    },
                    |b| {
                        runtime.release_elements(b, (target, described), (start, free));
                        b.yield_(&[]);
                    },
                );
                b.ret(&[target]);
            },
            |b| b.yield_(&[]),
        );
        let total = b.binary(Binary::Add, len, count);
        let two = number(b, 2);
        let doubled = b.binary(Binary::Mul, total, two);
        let least = number(b, MINIMUM_CAPACITY);
        let small = b.compare(Relation::Less, doubled, least);
        let fresh_capacity = b.if_(
            small,
            &[W],
            |b| b.yield_(&[least]),
            |b| b.yield_(&[doubled]),
        )[0];
        let fresh = runtime.allocate(b, (stride, described), fresh_capacity);
        let slot = b.binary(Binary::Sub, fresh_capacity, total);
        b.store(Width::Word, fresh, Offset::Words(LOW), slot);
        let source = element_at(b, target, (stride, free), word_bits);
        let into = b.binary(Binary::Sub, fresh_capacity, len);
        let into = element_at(b, fresh, (stride, into), word_bits);
        b.call(copy, &[source, into, len, from]);
        b.call(runtime.release, &[target]);
        b.ret(&[fresh]);
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
