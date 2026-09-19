//! Semantic facts read from definitions, shared by folding and lowering.

use num_bigint::BigUint;
use num_traits::Zero;

use super::bounds::{Bounds, Known};
use super::ir::{CtorId, ExprId, FnId, Program};

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Facts {
    operations: Vec<Option<Operation>>,
    known: Known,
}

impl Facts {
    #[must_use]
    pub fn operation(&self, id: FnId) -> Option<Operation> {
        self.operations.get(id.index()).copied().flatten()
    }
    #[must_use]
    pub fn held(&self, id: ExprId) -> Bounds {
        self.known
            .terms
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
    #[must_use]
    pub fn matched(&self, id: ExprId) -> Bounds {
        self.known
            .matched
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
    #[must_use]
    pub fn takes(&self, id: FnId) -> &[Bounds] {
        self.known.takes.get(id.index()).map_or(&[], Vec::as_slice)
    }
    #[must_use]
    pub fn answers(&self, id: FnId) -> Bounds {
        self.known
            .answers
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
}

#[must_use]
pub fn recognise(program: &Program) -> Facts {
    let operations = super::arithmetic::recognise(program);
    let known = super::bounds::walk(program, &operations);
    Facts { operations, known }
}
