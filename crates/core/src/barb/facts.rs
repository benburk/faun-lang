//! Final-program analysis: recognized equations, value ranges and affine forms.

use num_bigint::BigUint;
use num_traits::Zero;

use crate::float::Float;

use super::affine::Affine;
use super::bounds::{Bounds, Ranges};
use super::model::{CtorId, ExprId, FnId, TypeId};
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
    /// A bit wherever both have one.
    And,
    /// A bit wherever either has one.
    Or,
    /// A bit wherever exactly one has one.
    Xor,
    /// The first to the power of the second, where nought to the nought is
    /// one.
    Pow,
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

/// The widest power [`Operation::calculate`] works out.
const MOST_POWER_BITS: u64 = 1 << 20;

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
            Self::And => a & b,
            Self::Or => a | b,
            Self::Xor => a ^ b,
            // Too large a power is refused rather than worked out; the
            // evaluator's budget refuses it before asking.
            Self::Pow => {
                let exponent = u32::try_from(b).ok()?;
                if a.bits().saturating_mul(u64::from(exponent)) > MOST_POWER_BITS {
                    return None;
                }
                a.pow(exponent)
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
    /// The first parameter followed by the second, one more element.
    Append,
    /// The first parameter without as many of its first elements as the
    /// second counts, or without all of them where it counts more.
    Drop,
    /// As many of the first parameter's first elements as the second
    /// counts, or all of them where it counts more.
    Take,
    /// The first parameter with the element the second counts to replaced
    /// by the third, or unchanged where it counts past the last.
    Replace,
}

/// Which definitions are recognized, one entry per function in each table.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Recognised {
    pub operations: Vec<Option<Operation>>,
    pub sequences: Vec<Option<SequenceOperation>>,
    /// What a definition's claim says it computes; see
    /// [`super::Program::claim`].
    pub floats: Vec<Option<Float>>,
}

impl Recognised {
    /// Whether a call to `id` is answered as what it was recognized as,
    /// rather than by walking its body.
    pub(super) fn answered(&self, id: FnId) -> bool {
        self.operations[id.index()].is_some()
            || self.sequences[id.index()].is_some()
            || self.floats[id.index()].is_some()
    }

    /// The first definition recognized as `operation` over `params`,
    /// answering `result`.
    pub(super) fn operation_over(
        &self,
        program: &Program,
        operation: Operation,
        params: &[TypeId],
        result: TypeId,
    ) -> Option<FnId> {
        (0..self.operations.len()).map(FnId::at).find(|&id| {
            self.operations[id.index()] == Some(operation)
                && program.params(id) == params
                && program.function(id).result == result
        })
    }

    /// The first definition recognized as `operation` over `params`.
    pub(super) fn sequence_over(
        &self,
        program: &Program,
        operation: SequenceOperation,
        params: &[TypeId],
    ) -> Option<FnId> {
        (0..self.sequences.len()).map(FnId::at).find(|&id| {
            self.sequences[id.index()] == Some(operation) && program.params(id) == params
        })
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
        self.operation(id).is_some()
            || self.sequence_operation(id).is_some()
            || self.float(id).is_some()
    }
    /// The IEEE 754 operation `id` was claimed to compute: an answer a
    /// target with the instruction gives in its place, and one without it
    /// by walking the body.
    #[must_use]
    pub fn float(&self, id: FnId) -> Option<Float> {
        self.recognised.floats.get(id.index()).copied().flatten()
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
    pub fn affine(&self, id: ExprId) -> Option<&Affine> {
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
    /// A definition the range walk found still changing when it stopped
    /// going round: where there is one, the walk forgot every bound, and
    /// every number is held as though it could be any size.
    #[must_use]
    pub const fn unsettled(&self) -> Option<FnId> {
        self.ranges.unsettled
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
    mut recognised: Recognised,
    assumed: &super::Assumed,
) -> Facts {
    if !assumed.floats {
        recognised.floats.fill(None);
    }
    let ranges = super::bounds::analyze(program, &recognised, assumed);
    let affine = super::affine::analyze(program, &recognised.operations);
    Facts {
        recognised,
        ranges,
        affine,
    }
}
