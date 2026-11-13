//! Operations, regions, declarations, and their IDs.
//!
//! [`super::Program`] owns the pools these values refer to.

use crate::facts::Facts;
pub use crate::index::Range;
use crate::index::index;

// `Symbol` is a name, held as a run of characters in the program's own
// pool. Most passes compare and copy symbols as integers; renderers read
// function names, and targets read logical-entry parameter names.
// The shared register allocator identifies function slots with this index.
pub use faun_core::ir::FunctionId;
index!(pub ValueId, DataId, RegionId, Symbol, ShapeId);

/// Which of a program's two regions a datum sits in.
///
/// They are kept apart so that a target may map what is only read
/// differently from what is written, and so that a program writing nothing
/// needs no writable region at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    Data,
    Globals,
}

/// Where a datum sits, and how long it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub origin: Origin,
    pub start: u32,
    pub len: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// An immutable algebraic value. Ownership is tracked for this class;
    /// its object address and layout remain private to legalization.
    Cell,
    /// Where a sequence's elements live. A sequence is a buffer, where in
    /// it the sequence starts, and how many elements it has. Ownership is
    /// tracked; layout is legalization's.
    Buffer,
    /// An arbitrary-precision nonnegative integer. Never a wrapping word.
    Natural,
    /// As wide as an address, whatever the target's is.
    Word,
    /// What a number can be, as the tier above worked it out.
    ///
    /// One with no greatest is [`Self::Natural`], and the two say the same
    /// thing: the variants stay apart only while the tiers below read them
    /// apart, and nothing constructs this one without a greatest.
    ///
    /// It is a requirement rather than a modulus: a target may hold one in
    /// anything wide enough, since what it holds above is nought. A value
    /// that can only be nought needs no bits at all; it is still a scalar,
    /// not an erased value.
    ///
    /// So nothing wraps of its own accord. Arithmetic on values that fit
    /// answers a value that fits, because the tier above worked out what
    /// they could be before anything said how wide to hold them, and taking
    /// one modulo a width is what [`Op::Convert`] is for -- a program
    /// asking, rather than a machine deciding.
    ///
    /// Except at sixty-four bits: see [`Self::wraps`].
    Held(Facts),
    Address,
}

impl Class {
    /// A value of no more than this many bits, which is what a width says
    /// when a width is all that is known.
    #[must_use]
    pub const fn fixed(bits: u16) -> Self {
        Self::Held(Facts {
            low: 0,
            high: Some(if bits >= 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            }),
        })
    }

    /// What is known about it, where it is a number worked out here.
    #[must_use]
    pub const fn facts(self) -> Option<Facts> {
        match self {
            Self::Held(facts) => Some(facts),
            Self::Cell | Self::Buffer | Self::Natural | Self::Word | Self::Address => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Binary {
    Add,
    /// Word subtraction; on `Natural`, truncated subtraction (monus).
    /// Lowering uses it for predecessors only on a nonzero branch.
    Sub,
    /// Saturating subtraction: `left - right`, or zero where `right` is the
    /// greater. It needs no guard for its answer to fit, and since that
    /// answer is never more than `left`, its class may be narrower than its
    /// operands', which are only required to be alike, as a comparison's are.
    /// A target works it out at the operands' width, where the borrow is.
    Monus,
    /// Product. A fixed result is a fit requirement, not a modulus, except
    /// at a class that [wraps](Class::wraps).
    Mul,
    /// Unsigned quotient, with `Div(x, 0) = 0`.
    Div,
    /// Unsigned remainder, with `Mod(x, 0) = x`.
    Mod,
    /// A bit wherever both have one.
    And,
    /// A bit wherever either has one.
    Or,
    /// A bit wherever exactly one has one.
    Xor,
    /// `left` times two to the power of `right`: its bits moved up `right`
    /// places. A fit requirement, as a product is.
    ShiftUp,
    /// `left` divided by two to the power of `right`: its bits moved down
    /// `right` places, and nought where that is all of them.
    ShiftDown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relation {
    Equal,
    /// Unsigned, comparing the two bit patterns.
    Less,
    /// True for an unordered pair or when the first IEEE value is less than or equal to the second.
    FloatNotAbove(crate::float::Format),
}

/// Which way a shift moves the bits it keeps.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Direction {
    /// Toward the high bits: a product by two to the power of the distance.
    Up,
    /// Toward the low bits: the unsigned quotient by the same.
    Down,
}

/// How much of memory a load reads or a store writes.
///
/// A load answers the bytes read, zero-extended; a store writes the low
/// bytes of its value. Nothing is wider than a word, so a width wider than
/// the target's word is never asked of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    Byte,
    Bits16,
    Bits32,
    /// As wide as an address, whatever the target's is.
    Word,
}

impl Width {
    /// How many bytes it is, on a target whose word is `word_bits` wide.
    #[must_use]
    pub const fn bytes(self, word_bits: u16) -> u16 {
        match self {
            Self::Byte => 1,
            Self::Bits16 => 2,
            Self::Bits32 => 4,
            Self::Word => word_bits / 8,
        }
    }
}

/// A distance from an address, in units the target scales. `Words` is how a
/// machine with a word narrower than 64 bits keeps its own stride.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Offset {
    Bytes(i32),
    Words(i32),
}

/// The leaves `bytes` apart in a known buffer's elements, each read least
/// significant byte first.
pub(super) fn known_leaves(elements: &[u8], bytes: u8) -> impl Iterator<Item = u64> + '_ {
    elements.chunks(usize::from(bytes.max(1))).map(|leaf| {
        let mut word = [0; 8];
        word[..leaf.len()].copy_from_slice(leaf);
        u64::from_le_bytes(word)
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// A number known before the program runs. What it is held at is the
    /// class of the value it writes, said there and not here as well.
    Constant {
        value: u64,
    },
    /// Unsigned magnitude in little-endian bytes, held in the data pool.
    NaturalConstant(DataId),
    AddressOf(DataId),
    /// Construct one immutable algebraic object. `tag` is meaningful only
    /// within the erased source type. Each field is stored at the class its
    /// `shape` says, which every read of the object reads it back at, so
    /// where each field lies is legalization's to decide from the shape.
    Cell {
        tag: u32,
        fields: Range,
        shape: ShapeId,
    },
    /// Read the constructor tag of a cell.
    CellTag {
        cell: ValueId,
    },
    /// Read one field of an object of `shape`. The result value says the
    /// class it is read as.
    CellField {
        cell: ValueId,
        index: u32,
        shape: ShapeId,
    },
    /// A buffer holding no elements, whose elements are to be of `shape`.
    ///
    /// A sequence is a buffer, where in it the sequence starts, and how many
    /// elements it has: the `len` elements from element `start`, in order.
    /// Sequences share a buffer, each a run of it, so the tail of one is
    /// the same buffer from one element further on.
    BufferEmpty {
        shape: ShapeId,
    },
    /// A buffer known before the program runs, laid out in the image and
    /// never freed. `elements` holds each element's scalar leaves in the
    /// order `shape` names them, each `bytes` bytes, least significant
    /// first. A known string is one of these, a byte a leaf, so however long
    /// it is, it costs its bytes and nothing is copied to build it; a known
    /// table of numbers is too, and nothing builds it each time it is read.
    BufferKnown {
        elements: DataId,
        shape: ShapeId,
        bytes: u8,
    },
    /// The sequence whose elements are `fields`, one value per leaf of a new
    /// first element, followed by the sequence `operands` begins with: a
    /// buffer, a start and a length, then the fields. Answers a buffer and
    /// where in it the longer sequence starts. Takes a claim to the buffer
    /// and to each field, so a buffer nothing else holds with room in front
    /// is written in place.
    BufferPush {
        operands: Range,
        shape: ShapeId,
    },
    /// The sequence `operands` begins with -- a buffer, a start and a
    /// length -- followed by one more element, whose leaves are the rest,
    /// `fields`. Answers a buffer and where in it the longer sequence
    /// starts. Takes a claim to the buffer and to each field, so a buffer
    /// nothing else holds with room after is written in place.
    BufferAppend {
        operands: Range,
        shape: ShapeId,
    },
    /// The sequence `operands` begins with -- a buffer, a start and a
    /// length -- with its element at the index that follows, which must be
    /// below the length, replaced by the one whose leaves are the rest,
    /// `fields`. Answers a buffer and where in it the sequence starts. Takes
    /// a claim to the buffer and to each field, so a buffer nothing else
    /// holds is written where it lies, giving up what the element replaced
    /// held; a shared one is copied first.
    BufferReplace {
        operands: Range,
        shape: ShapeId,
    },
    /// The sequence of the elements of one, last first, followed by those of
    /// another: `operands` are the other's buffer, start and length, then the
    /// one's. Answers a buffer and where in it the joined sequence starts.
    /// Takes a claim to both buffers: where the other is empty and nothing
    /// else holds the one's, it is turned round where it lies; otherwise
    /// the other's, where nothing else holds it and it has room in front,
    /// is written in place, and each element copied out of the one's is
    /// claimed again. Both hold elements of `shape`.
    BufferPrepend {
        operands: Range,
        shape: ShapeId,
    },
    /// The sequence of the elements of one, in order, followed by those of
    /// another: `operands` are the one's buffer, start and length, then the
    /// other's. Answers a buffer and where in it the joined sequence starts.
    /// Takes a claim to both buffers: one empty sequence answers the other,
    /// a first nothing else holds with room after it is written after, and
    /// otherwise both are copied, the joined sequence first in its buffer.
    /// Both hold elements of `shape`.
    BufferExtend {
        operands: Range,
        shape: ShapeId,
    },
    /// A buffer nothing else holds, with room for `count` elements of
    /// `shape`, which holds no claim, holding none of them yet: for
    /// something outside to write elements into where they lie, from its
    /// first.
    BufferRoom {
        count: ValueId,
        shape: ShapeId,
    },
    /// Where element `start` of `buffer`, whose elements are of `shape`,
    /// lies: the first of a sequence's elements, which lie one after another
    /// from there, for something outside to read or write where they lie.
    /// The buffer is borrowed, and is only held for as long as something
    /// uses it: see [`Op::Keep`].
    BufferAt {
        buffer: ValueId,
        start: ValueId,
        shape: ShapeId,
    },
    /// Hold `value` until here, doing nothing with it: what keeps a buffer
    /// alive while something outside reads or writes where it lies.
    Keep {
        value: ValueId,
    },
    /// Read leaf `index` of element `start` of `buffer`, whose elements are
    /// of `shape`. The result value says the class it is read as.
    BufferField {
        buffer: ValueId,
        start: ValueId,
        index: u32,
        shape: ShapeId,
    },
    Binary {
        op: Binary,
        left: ValueId,
        right: ValueId,
    },
    Compare {
        relation: Relation,
        left: ValueId,
        right: ValueId,
    },
    Load {
        width: Width,
        address: ValueId,
        offset: Offset,
    },
    Store {
        width: Width,
        address: ValueId,
        offset: Offset,
        value: ValueId,
    },
    /// A product or quotient by a power of two, said the way a machine says
    /// it: `value` with its bits moved `by` places.
    ///
    /// The distance is known before the program runs, always. Nothing in the
    /// language shifts by a number it works out, and a target handed one
    /// would need a loop where it otherwise needs an instruction; this is
    /// written by recognising a product or quotient, so there is nothing for
    /// it to be but a number.
    ///
    /// Over a value the machine holds and not an arbitrary-precision
    /// natural, whose products go through the helpers and stay products.
    ///
    /// The class is a fit requirement, exactly as `Binary`'s is: a shift up
    /// past what the class holds is a program saying something untrue, not a
    /// modulus, except at a class that [wraps](Class::wraps).
    Shift {
        direction: Direction,
        value: ValueId,
        by: u16,
    },
    /// `value` read as the class of what this writes, which is the only
    /// place a width changes. Everything else works at the width its
    /// operands already have, so a target need not normalise after each
    /// operation.
    Convert {
        value: ValueId,
    },
    Call {
        function: FunctionId,
        args: Range,
    },
    /// IEEE 754 arithmetic on bit patterns: each operand, and what this
    /// writes, is the pattern of a value of `float`'s format, held as a
    /// number of that many bits. Written only for a target that computes
    /// these itself (see [`crate::platform::Routines::with_floats`]), for
    /// which it is one instruction; a NaN it writes may be any NaN.
    Float {
        float: crate::float::Float,
        operands: Range,
    },
    If {
        condition: ValueId,
        then_region: RegionId,
        else_region: RegionId,
    },
    /// Runs `body` with `initial`, then with whatever each `Continue`
    /// carries, until a `Break` leaves.
    Loop {
        initial: Range,
        body: RegionId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exit {
    /// Leave the enclosing `if`, giving it its results.
    Yield,
    Continue,
    Break,
    Return,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Terminator {
    pub exit: Exit,
    pub values: Range,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    pub params: Range,
    /// The instructions, contiguous, so that walking one is a scan.
    pub ops: Range,
    /// Absent only when the instructions cannot fall through. Validation
    /// derives this from call signatures and structured transfers.
    pub terminator: Option<Terminator>,
}

/// Returning no values is different from never returning. Builders accept
/// borrowed classes; stored declarations hold a range in the signature pool.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Returns<T> {
    Never,
    Values(T),
}

impl Returns<Range> {
    /// The result classes, empty for a call which cannot return.
    #[must_use]
    pub const fn classes(self) -> Range {
        match self {
            Self::Never => Range::EMPTY,
            Self::Values(classes) => classes,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Definition {
    /// Reserved root and parameter values, not yet a built body.
    Declared(RegionId),
    Body(RegionId),
    /// A function implemented outside this program. Targets check whether
    /// they can provide its name and signature.
    External,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Parameter {
    pub name: Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// The provider symbol for an external, or a descriptive name for a body.
    /// Source aliases are resolved before constructing this declaration.
    pub name: Symbol,
    /// Parameter classes in the signature pool. A body's parameter values
    /// belong to its root region; external declarations need no SSA values.
    pub params: Range,
    /// Diagnostic names, parallel to `params`.
    pub(super) parameters: Range,
    pub returns: Returns<Range>,
    pub definition: Definition,
    /// Whether a call of it does nothing but answer, so that a call whose
    /// answer nothing reads may go. Only a body this tier writes itself is,
    /// since nothing below can tell what a body does beyond answering.
    pub inert: bool,
}

impl Function {
    #[must_use]
    pub const fn body(&self) -> Option<RegionId> {
        match self.definition {
            Definition::Body(body) => Some(body),
            Definition::Declared(_) | Definition::External => None,
        }
    }

    /// The provider name, derived from this function's definition and name.
    #[must_use]
    pub const fn external(&self) -> Option<Symbol> {
        match self.definition {
            Definition::Declared(_) | Definition::Body(_) => None,
            Definition::External => Some(self.name),
        }
    }
}

impl Class {
    /// How many bits it needs, on a machine whose word is this wide.
    ///
    /// A fixed width says its own. Anything else is as wide as the machine
    /// is, which is why this is a question a target answers and not one a
    /// class answers alone.
    ///
    /// # Panics
    /// If asked for the width of an arbitrary-precision natural. Targets
    /// without that representation must reject it before selecting widths.
    #[must_use]
    pub fn bits(self, word: u16) -> u16 {
        match self {
            Self::Held(facts) => facts
                .width()
                .expect("a number with no greatest has no fixed width"),
            Self::Cell | Self::Buffer | Self::Word | Self::Address => word,
            Self::Natural => panic!("an arbitrary-precision integer has no fixed width"),
        }
    }

    /// How many bits hold every number it can be, where it is a number and
    /// something says how big it gets.
    #[must_use]
    pub fn width(self) -> Option<u16> {
        match self {
            Self::Held(facts) => facts.width(),
            Self::Cell | Self::Buffer | Self::Natural | Self::Word | Self::Address => None,
        }
    }

    /// Whether a sum, a difference, a product or an [`Op::Shift`] up written
    /// at this class answers modulo two to its width rather than having to
    /// fit it: where it is sixty-four bits wide.
    ///
    /// Not a [`Binary::ShiftUp`], whose distance is worked out while the
    /// program runs and may be the width or more: a machine takes that
    /// modulo its word, so a target is handed one in one instruction only
    /// because a value moved that far fits only where it is nought.
    ///
    /// Nothing is held wider. A sum or a product of two such numbers taken
    /// modulo 2^64, which is what a `U64`'s are, has nowhere wider to be
    /// worked out and narrowed after, as a `U32`'s is; without this it is
    /// worked out as a natural, a heap object and a division. And it costs
    /// no target anything: each holds a number this wide in exactly as many
    /// bits, a register on x86-64 and words on narrower machines, kept to as
    /// many as the class has, and its instructions answer the same modulo
    /// that. What is known of the least such a value can be says nothing
    /// once it may have wrapped, so a class written for one says only its
    /// width.
    #[must_use]
    pub fn wraps(self) -> bool {
        matches!(self, Self::Held(_)) && self.width() == Some(64)
    }

    /// Whether a value of this class can be read as one of `wanted` without
    /// anything happening in between. A width is what a value needs and
    /// what it holds above that is nought, so a narrower one is already a
    /// wider one; the other way needs taking modulo, which is an operation
    /// rather than an assumption.
    #[must_use]
    pub fn fits(self, wanted: Self) -> bool {
        match (self, wanted) {
            (Self::Address, Self::Address)
            | (Self::Cell, Self::Cell)
            | (Self::Buffer, Self::Buffer)
            | (Self::Word, Self::Word)
            | (Self::Natural, Self::Natural) => true,
            // Every number a machine word holds is one, and a number with
            // no greatest is not something a word is known to hold.
            (Self::Held(facts), Self::Word) => matches!(facts.width(), Some(bits) if bits <= 64),
            // Room, not range: a value is already read as anything with
            // room for it, and two numbers needing the same bits need the
            // same bits whatever else is known about them. Whether a
            // narrowing takes anything off is a different question, asked
            // of the facts by whoever wants to know.
            (Self::Held(held), Self::Held(wanted)) => match (held.width(), wanted.width()) {
                (_, None) => true,
                (None, Some(_)) => false,
                (Some(held), Some(wanted)) => held <= wanted,
            },
            _ => false,
        }
    }
}

/// A constant taken modulo its class. Everything else fits its class by
/// construction; a constant is where a builder could write one that does
/// not, and this is what it means if it does.
#[must_use]
pub(super) fn wrap(class: Class, value: u64) -> u64 {
    match class.width() {
        Some(bits) if bits < 64 => value & ((1 << bits) - 1),
        _ => value,
    }
}
