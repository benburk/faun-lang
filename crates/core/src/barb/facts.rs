//! Final-program analysis: recognized equations, value ranges and affine forms.

use num_bigint::BigUint;
use num_traits::Zero;

use super::affine::Affine;
use super::bounds::{Bounds, Ranges};
use super::model::{CtorId, ExprId, FnId};
use super::program::Program;

/// Operations on unbounded naturals. These are not wrapping machine ops.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Add,
    Monus,
    Mul,
    /// The quotient is zero when the divisor is zero.
    Div,
    /// The remainder is the dividend when the divisor is zero.
    Mod,
    /// Constructor identity matters: a Bool's declaration order is arbitrary.
    Equals {
        yes: CtorId,
        no: CtorId,
    },
    LessThan {
        yes: CtorId,
        no: CtorId,
    },
}

impl Operation {
    pub(super) fn calculate(self, a: &BigUint, b: &BigUint) -> Option<BigUint> {
        Some(match self {
            Self::Add => a + b,
            Self::Monus => {
                if a < b {
                    BigUint::zero()
                } else {
                    a - b
                }
            }
            Self::Mul => a * b,
            Self::Div => {
                if b.is_zero() {
                    BigUint::zero()
                } else {
                    a / b
                }
            }
            Self::Mod => {
                if b.is_zero() {
                    a.clone()
                } else {
                    a % b
                }
            }
            Self::Equals { .. } | Self::LessThan { .. } => return None,
        })
    }

    pub(super) fn compare(self, a: &BigUint, b: &BigUint) -> Option<CtorId> {
        match self {
            Self::Equals { yes, no } => Some(if a == b { yes } else { no }),
            Self::LessThan { yes, no } => Some(if a < b { yes } else { no }),
            _ => None,
        }
    }
}

/// A question about a sequence, answered from how a sequence is held rather
/// than by walking it. Like an [`Operation`], it is recognized from what a
/// definition computes, never from its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SequenceOperation {
    /// How many elements the one parameter holds: nought for the empty
    /// sequence and one more than the rest's for a step, whatever the
    /// element.
    Length,
    /// The first parameter's elements put before the second's, last first.
    ReverseOnto,
    /// The first parameter's elements put before the second's, in order.
    Prepend,
}

/// Which definitions are recognized, one entry per function in each table.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Recognised {
    pub operations: Vec<Option<Operation>>,
    pub sequences: Vec<Option<SequenceOperation>>,
}

impl Recognised {
    /// Whether a call to `id` is answered as what it was recognized as,
    /// rather than by walking its body.
    pub(super) fn answered(&self, id: FnId) -> bool {
        self.operations[id.index()].is_some() || self.sequences[id.index()].is_some()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Facts {
    recognised: Recognised,
    ranges: Ranges,
    affine: Vec<Option<Affine>>,
}

impl Facts {
    #[must_use]
    pub fn operation(&self, id: FnId) -> Option<Operation> {
        self.recognised
            .operations
            .get(id.index())
            .copied()
            .flatten()
    }
    /// Whether a call to `id` is answered as what it was recognized as,
    /// rather than by walking its body.
    #[must_use]
    pub fn answered(&self, id: FnId) -> bool {
        self.operation(id).is_some() || self.sequence_operation(id).is_some()
    }
    #[must_use]
    pub fn sequence_operation(&self, id: FnId) -> Option<SequenceOperation> {
        self.recognised.sequences.get(id.index()).copied().flatten()
    }
    #[must_use]
    pub fn held(&self, id: ExprId) -> Bounds {
        self.ranges
            .terms
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
    #[must_use]
    pub fn matched(&self, id: ExprId) -> Bounds {
        self.ranges
            .matched
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
    #[must_use]
    pub fn takes(&self, id: FnId) -> &[Bounds] {
        self.ranges.takes.get(id.index()).map_or(&[], Vec::as_slice)
    }
    #[must_use]
    pub(crate) fn affine(&self, id: ExprId) -> Option<&Affine> {
        self.affine.get(id.index())?.as_ref()
    }
    /// What field `at` of `ctor` can hold: every value built into it, or
    /// anything where a value was built out of sight or the field is the
    /// rest of a spine.
    #[must_use]
    pub fn field(&self, program: &Program, ctor: CtorId, at: usize) -> Bounds {
        self.ranges
            .fields
            .get(super::bounds::slot(program, ctor, at))
            .copied()
            .unwrap_or(Bounds::ANY)
    }
    #[must_use]
    pub fn answers(&self, id: FnId) -> Bounds {
        self.ranges
            .answers
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
}

/// Ranges and affine forms over `program`, given which of its functions are
/// recognised equations. [`Program::analyze`] keeps the answer.
#[must_use]
pub(super) fn analyze(
    program: &Program,
    recognised: Recognised,
    assumed: &super::Assumed,
) -> Facts {
    let ranges = super::bounds::analyze(program, &recognised, assumed);
    let affine = super::affine::analyze(program, &recognised.operations);
    Facts {
        recognised,
        ranges,
        affine,
    }
}
