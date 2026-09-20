//! Checked boundaries. No raw bytes or constructor trees enter the constant
//! pool until their type, shape and complete encoding have been verified.

use std::fmt;

use super::{Held, Shape, Value, read_u64, shape};
use crate::barb::budget::{Budget, LimitExceeded};
use crate::barb::model::TypeDefinition;
use crate::barb::{ConstId, CtorId, Program, TypeId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructionError {
    UndefinedType(TypeId),
    UnknownConstructor(CtorId),
    UnknownConstant(ConstId),
    FieldCount { expected: usize, actual: usize },
    FieldType { expected: TypeId, actual: TypeId },
    Limit(LimitExceeded),
}

impl From<LimitExceeded> for ConstructionError {
    fn from(error: LimitExceeded) -> Self {
        Self::Limit(error)
    }
}
impl fmt::Display for ConstructionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(limit) => fmt::Display::fmt(limit, f),
            error => write!(f, "invalid constant construction: {error:?}"),
        }
    }
}
impl std::error::Error for ConstructionError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UndefinedType(TypeId),
    UnterminatedHeader,
    InvalidTag(TypeId),
    TrailingBytes,
    Limit(LimitExceeded),
}

impl From<LimitExceeded> for DecodeError {
    fn from(error: LimitExceeded) -> Self {
        Self::Limit(error)
    }
}
impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(limit) => fmt::Display::fmt(limit, f),
            error => write!(f, "invalid constant encoding: {error:?}"),
        }
    }
}
impl std::error::Error for DecodeError {}

fn defined(program: &Program, owner: TypeId) -> bool {
    program
        .types
        .get(owner)
        .is_some_and(|ty| matches!(ty.definition, TypeDefinition::Defined(_)))
}

pub(in crate::barb) fn tree(
    program: &Program,
    owner: TypeId,
    value: &Value,
) -> Result<(), ConstructionError> {
    // Iterative validation also handles a large caller-built unary natural.
    let mut pending = vec![(owner, value)];
    while let Some((owner, value)) = pending.pop() {
        if !defined(program, owner) {
            return Err(ConstructionError::UndefinedType(owner));
        }
        let ctor = program
            .ctors
            .get(value.0)
            .ok_or(ConstructionError::UnknownConstructor(value.0))?;
        if ctor.owner != owner {
            return Err(ConstructionError::FieldType {
                expected: owner,
                actual: ctor.owner,
            });
        }
        let expected = program.fields(value.0).len();
        if expected != value.1.len() {
            return Err(ConstructionError::FieldCount {
                expected,
                actual: value.1.len(),
            });
        }
        pending.extend(program.fields(value.0).iter().copied().zip(&value.1));
    }
    Ok(())
}

pub(in crate::barb) fn fields(
    program: &Program,
    ctor: CtorId,
    count: usize,
    owners: impl Iterator<Item = Result<TypeId, ConstructionError>>,
) -> Result<(), ConstructionError> {
    let held = program
        .ctors
        .get(ctor)
        .ok_or(ConstructionError::UnknownConstructor(ctor))?;
    if !defined(program, held.owner) {
        return Err(ConstructionError::UndefinedType(held.owner));
    }
    let expected = program.fields(ctor);
    if expected.len() != count {
        return Err(ConstructionError::FieldCount {
            expected: expected.len(),
            actual: count,
        });
    }
    for (&expected, actual) in expected.iter().zip(owners) {
        let actual = actual?;
        if expected != actual {
            return Err(ConstructionError::FieldType { expected, actual });
        }
    }
    Ok(())
}

pub(in crate::barb) fn read(
    program: &Program,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Result<Held, DecodeError> {
    budget.bytes(bytes.len())?;
    if extent(program, owner, bytes, budget)? != bytes.len() {
        return Err(DecodeError::TrailingBytes);
    }
    Ok(Held {
        owner,
        bytes: bytes.to_vec(),
    })
}

fn header(bytes: &[u8]) -> Result<usize, DecodeError> {
    Ok(bytes
        .iter()
        .position(|byte| byte & 0x80 == 0)
        .ok_or(DecodeError::UnterminatedHeader)?
        + 1)
}

// Imports charge the input bytes; evaluator scans charge visits, just as before.
// Both use this one type-directed extent walk.
pub(super) fn extent(
    program: &Program,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Result<usize, DecodeError> {
    budget.descend(|budget| {
        if !defined(program, owner) {
            return Err(DecodeError::UndefinedType(owner));
        }
        let (ctor, mut at, count, recursive) = match shape(program, owner) {
            Shape::Spine {
                cons, recursive, ..
            } => {
                let took = header(bytes)?;
                if program.fields(cons).len() == 1 {
                    return Ok(took);
                }
                let count = u32::try_from(read_u64(bytes).0.ok_or(LimitExceeded::Work)?)
                    .map_err(|_| LimitExceeded::Work)?;
                (cons, took, count, Some(recursive))
            }
            Shape::Tagged => {
                let (tag, took) = if program.ctors(owner).len() == 1 {
                    (0, 0)
                } else {
                    let took = header(bytes)?;
                    let tag = read_u64(bytes).0.ok_or(DecodeError::InvalidTag(owner))?;
                    (tag, took)
                };
                let tag = u32::try_from(tag).map_err(|_| DecodeError::InvalidTag(owner))?;
                if usize::try_from(tag).unwrap() >= program.ctors(owner).len() {
                    return Err(DecodeError::InvalidTag(owner));
                }
                (program.ctor_at(owner, tag), took, 1, None)
            }
        };
        for _ in 0..count {
            for (index, &field) in program.fields(ctor).iter().enumerate() {
                if recursive != Some(index) {
                    at += extent(program, field, &bytes[at..], budget)?;
                }
            }
        }
        Ok(at)
    })
}
