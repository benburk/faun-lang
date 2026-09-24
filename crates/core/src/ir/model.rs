//! Operations, regions, declarations, and their IDs.
//!
//! [`super::Program`] owns the pools these values refer to.

use crate::facts::Facts;
pub use crate::index::Range;
use crate::index::index;

// `Symbol` is a name, held as a run of characters in the program's own
// pool. Most passes compare and copy symbols as integers; renderers read
// function names, and targets read logical-entry parameter names.
index!(ValueId, DataId, FunctionId, RegionId, Symbol);

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// An immutable algebraic value. Ownership is tracked for this class;
    /// its object address and layout remain private to legalization.
    Cell,
    /// Where a sequence's elements live. A sequence is a buffer and a
    /// length, and the length says which of the buffer's elements it holds:
    /// the last that many. Ownership is tracked; layout is legalization's.
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binary {
    Add,
    /// Word subtraction; on `Natural`, truncated subtraction (monus).
    /// Lowering uses it for predecessors only on a nonzero branch.
    Sub,
    /// Product. A fixed result is a fit requirement, not a modulus.
    Mul,
    /// Unsigned quotient, with `Div(x, 0) = 0`.
    Div,
    /// Unsigned remainder, with `Mod(x, 0) = x`.
    Mod,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation {
    Equal,
    /// Unsigned, like every comparison on a word.
    Less,
}

/// Which way a shift moves the bits it keeps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Toward the high bits: a product by two to the power of the distance.
    Up,
    /// Toward the low bits: the unsigned quotient by the same.
    Down,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    Byte,
    Word,
}

/// A distance from an address, in units the target scales. `Words` is how a
/// machine with a word narrower than 64 bits keeps its own stride.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Offset {
    Bytes(i32),
    Words(i32),
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
    /// Construct one immutable algebraic object. Fields retain their own
    /// classes; `tag` is meaningful only within the erased source type.
    Cell {
        tag: u32,
        fields: Range,
    },
    /// Read the constructor tag of a cell.
    CellTag {
        cell: ValueId,
    },
    /// Read one field. The result value says the field's class.
    CellField {
        cell: ValueId,
        index: u32,
    },
    /// A buffer holding no elements.
    BufferEmpty,
    /// The buffer whose last `len + 1` elements are `fields`, one value per
    /// leaf of the new first element, followed by the last `len` of
    /// `buffer`. Takes a claim to `buffer` and to each field, so a buffer
    /// nothing else holds may be written in place.
    BufferPush {
        buffer: ValueId,
        len: ValueId,
        fields: Range,
    },
    /// Read leaf `index` of the first of the last `len` elements of
    /// `buffer`. The result value says the leaf's class.
    BufferField {
        buffer: ValueId,
        len: ValueId,
        index: u32,
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
    /// modulus.
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
