//! Checked boundaries. Only declaration metadata is needed to establish a
//! constant's type and complete encoded extent; no access to program storage.

use std::fmt;

use super::{Shape, Value, header_bytes, read_u64, shape};
use crate::barb::budget::{Budget, LimitExceeded};
use crate::barb::model::TypeDefinition;
use crate::barb::types::TypeInfo;
use crate::barb::{CtorId, TypeId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructionError {
    UndefinedType(TypeId),
    NotNatural(TypeId),
    NotByteSpine(TypeId),
    UnknownConstructor(CtorId),
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

/// Why an encoding's extent could not be walked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::barb) enum DecodeError {
    UndefinedType(TypeId),
    UnterminatedHeader,
    InvalidTag(TypeId),
    Limit(LimitExceeded),
}

impl From<LimitExceeded> for DecodeError {
    fn from(error: LimitExceeded) -> Self {
        Self::Limit(error)
    }
}

fn defined(types: TypeInfo<'_>, owner: TypeId) -> bool {
    types
        .get_type(owner)
        .is_some_and(|ty| matches!(ty.definition, TypeDefinition::Defined(_)))
}

pub(super) fn natural(types: TypeInfo<'_>, owner: TypeId) -> Result<(), ConstructionError> {
    if !defined(types, owner) {
        return Err(ConstructionError::UndefinedType(owner));
    }
    match shape(types, owner) {
        Shape::Spine { cons, .. } if types.fields(cons).len() == 1 => Ok(()),
        _ => Err(ConstructionError::NotNatural(owner)),
    }
}

pub(super) fn byte_spine(types: TypeInfo<'_>, owner: TypeId) -> Result<(), ConstructionError> {
    if !defined(types, owner) {
        return Err(ConstructionError::UndefinedType(owner));
    }
    let Shape::Spine {
        cons, recursive, ..
    } = shape(types, owner)
    else {
        return Err(ConstructionError::NotByteSpine(owner));
    };
    let mut elements = types
        .fields(cons)
        .iter()
        .enumerate()
        .filter(|(at, _)| *at != recursive);
    let Some((_, &element)) = elements.next() else {
        return Err(ConstructionError::NotByteSpine(owner));
    };
    // A wrapper of a natural encodes as the natural, as reading one back
    // says: a spine of `U8` is a spine of bytes.
    let element = super::view::peeled(types, element);
    if elements.next().is_some() || element.is_none_or(|element| natural(types, element).is_err()) {
        return Err(ConstructionError::NotByteSpine(owner));
    }
    Ok(())
}

pub(super) fn tree(
    types: TypeInfo<'_>,
    owner: TypeId,
    value: &Value,
) -> Result<(), ConstructionError> {
    // Iterative validation also handles a large caller-built unary natural.
    let mut pending = vec![(owner, value)];
    while let Some((owner, value)) = pending.pop() {
        if !defined(types, owner) {
            return Err(ConstructionError::UndefinedType(owner));
        }
        let ctor = types
            .get_ctor(value.0)
            .ok_or(ConstructionError::UnknownConstructor(value.0))?;
        if ctor.owner != owner {
            return Err(ConstructionError::FieldType {
                expected: owner,
                actual: ctor.owner,
            });
        }
        let expected = types.fields(value.0).len();
        if expected != value.1.len() {
            return Err(ConstructionError::FieldCount {
                expected,
                actual: value.1.len(),
            });
        }
        pending.extend(types.fields(value.0).iter().copied().zip(&value.1));
    }
    Ok(())
}

pub(super) fn fields(
    types: TypeInfo<'_>,
    ctor: CtorId,
    count: usize,
    owners: impl Iterator<Item = Result<TypeId, ConstructionError>>,
) -> Result<(), ConstructionError> {
    let held = types
        .get_ctor(ctor)
        .ok_or(ConstructionError::UnknownConstructor(ctor))?;
    if !defined(types, held.owner) {
        return Err(ConstructionError::UndefinedType(held.owner));
    }
    let expected = types.fields(ctor);
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

fn header(bytes: &[u8]) -> Result<usize, DecodeError> {
    Ok(header_bytes(bytes)
        .ok_or(DecodeError::UnterminatedHeader)?
        .len())
}

// Evaluator scans charge visits as they walk an encoding's extent.
pub(super) fn extent(
    types: TypeInfo<'_>,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Result<usize, DecodeError> {
    budget.descend(|budget| {
        if !defined(types, owner) {
            return Err(DecodeError::UndefinedType(owner));
        }
        let (ctor, mut at, count, recursive) = match shape(types, owner) {
            Shape::Spine {
                cons, recursive, ..
            } => {
                let took = header(bytes)?;
                if types.fields(cons).len() == 1 {
                    return Ok(took);
                }
                let count = u32::try_from(read_u64(bytes).0.ok_or(LimitExceeded::Work)?)
                    .map_err(|_| LimitExceeded::Work)?;
                (cons, took, count, Some(recursive))
            }
            Shape::Tagged => {
                let (tag, took) = if types.ctors(owner).len() == 1 {
                    (0, 0)
                } else {
                    let took = header(bytes)?;
                    let tag = read_u64(bytes).0.ok_or(DecodeError::InvalidTag(owner))?;
                    (tag, took)
                };
                let tag = u32::try_from(tag).map_err(|_| DecodeError::InvalidTag(owner))?;
                if usize::try_from(tag).unwrap() >= types.ctors(owner).len() {
                    return Err(DecodeError::InvalidTag(owner));
                }
                (types.ctor_at(owner, tag), took, 1, None)
            }
        };
        for _ in 0..count {
            for (index, &field) in types.fields(ctor).iter().enumerate() {
                if recursive != Some(index) {
                    at += extent(types, field, &bytes[at..], budget)?;
                }
            }
        }
        Ok(at)
    })
}
