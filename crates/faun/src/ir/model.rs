//! Operations, regions, declarations, and their IDs.
//!
//! [`super::Program`] owns the pools these values refer to.

pub use crate::index::Range;
use crate::index::index;

// `Symbol` is a name, held as a run of characters in the program's own
// pool. The IR never reads those characters: names are compared and copied
// as integers, and the text comes back only to render one.
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
    /// An arbitrary-precision nonnegative integer. Never a wrapping word.
    Natural,
    /// As wide as an address, whatever the target's is.
    Word,
    /// A value needing at least this many bits, and never more. It is a
    /// requirement rather than a modulus: a target may hold one in anything
    /// wider, since what it holds above those bits is nought.
    ///
    /// So nothing wraps of its own accord. Arithmetic on values that fit
    /// answers a value that fits, because the tier above worked out what
    /// they could be before saying how wide to hold them, and taking one
    /// modulo a width is what [`Op::Convert`] is for -- a program asking,
    /// rather than a machine deciding.
    Fixed {
        bits: u16,
    },
    Address,
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
    Constant {
        class: Class,
        value: u64,
    },
    /// Unsigned magnitude in little-endian bytes, held in the data pool.
    NaturalConstant(DataId),
    AddressOf(DataId),
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
    /// `value` read as `class`, which is the only place a width changes.
    /// Everything else works at the width its operands already have, so a
    /// target need not normalise after each operation.
    Convert {
        class: Class,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// The provider symbol for an external, or a descriptive name for a body.
    /// Source aliases are resolved before constructing this declaration.
    pub name: Symbol,
    /// Parameter classes in the signature pool. A body's parameter values
    /// belong to its root region; external declarations need no SSA values.
    pub params: Range,
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
    pub const fn bits(self, word: u16) -> u16 {
        match self {
            Self::Fixed { bits } => bits,
            Self::Word | Self::Address => word,
            Self::Natural => panic!("an arbitrary-precision integer has no fixed width"),
        }
    }

    /// Whether a value of this class can be read as one of `wanted` without
    /// anything happening in between. A width is what a value needs and
    /// what it holds above that is nought, so a narrower one is already a
    /// wider one; the other way needs taking modulo, which is an operation
    /// rather than an assumption.
    #[must_use]
    pub const fn fits(self, wanted: Self) -> bool {
        match (self, wanted) {
            (Self::Address, Self::Address)
            | (Self::Word, Self::Word)
            | (Self::Natural, Self::Natural) => true,
            (Self::Fixed { bits }, Self::Word) => bits <= 64,
            (Self::Fixed { bits }, Self::Fixed { bits: wanted }) => bits <= wanted,
            _ => false,
        }
    }
}

/// A constant taken modulo its class. Everything else fits its class by
/// construction; a constant is where a builder could write one that does
/// not, and this is what it means if it does.
#[must_use]
pub(super) const fn wrap(class: Class, value: u64) -> u64 {
    match class {
        Class::Fixed { bits } if bits < 64 => value & ((1 << bits) - 1),
        _ => value,
    }
}
