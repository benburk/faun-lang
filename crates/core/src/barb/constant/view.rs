//! Semantic views of validated constants. Views borrow only declaration metadata
//! and an exact encoded value, never the whole program or mutable pool storage.

use num_bigint::BigUint;
use num_traits::One;

use super::{
    ConstructionError, Held, Shape, checked, header_bytes, read_natural, read_u64, shape,
    write_natural,
};
use crate::barb::budget::{Budget, LimitExceeded};
use crate::barb::types::TypeInfo;
use crate::barb::{CtorId, TypeId};

/// A borrowed, well-typed value. Obtain it from [`crate::barb::Program::constant`]
/// rather than attaching a type to bytes or replacing its validated encoding.
///
/// ```compile_fail
/// use faun_core::barb::Constant;
/// fn forge(mut value: Constant<'_>) { value.bytes = &[0]; }
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Constant<'a> {
    types: TypeInfo<'a>,
    owner: TypeId,
    bytes: &'a [u8],
}

/// Disjoint structural cases, independent of source type names.
#[derive(Clone, Copy, Debug)]
pub enum ConstantView<'a> {
    Natural(NaturalView<'a>),
    Spine(SpineView<'a>),
    Constructor(ConstructorView<'a>),
}

#[derive(Clone, Copy, Debug)]
pub struct NaturalView<'a>(Constant<'a>);

#[derive(Clone, Copy, Debug)]
pub struct SpineView<'a>(Constant<'a>);

#[derive(Clone, Copy, Debug)]
pub struct ConstructorView<'a> {
    constant: Constant<'a>,
    ctor: CtorId,
}

/// A natural was valid, but did not fit the requested machine word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TooWide;

impl std::fmt::Display for TooWide {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("natural does not fit u64")
    }
}
impl std::error::Error for TooWide {}

/// A byte view is a capability, not another kind of constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteView<'a> {
    Borrowed(&'a [u8]),
    NeedsDecoding,
}

impl NaturalView<'_> {
    /// # Errors
    /// If this natural exceeds `u64`. No constructor chain is expanded.
    pub fn try_u64(self) -> Result<u64, TooWide> {
        read_u64(self.0.bytes).0.ok_or(TooWide)
    }

    /// Read the magnitude, not its unary constructor chain.
    #[must_use]
    pub fn to_biguint(self) -> BigUint {
        read_natural(self.0.bytes).0
    }
}

impl<'a> SpineView<'a> {
    /// Element count without traversing or expanding the spine.
    #[must_use]
    pub fn length(self) -> BigUint {
        read_natural(self.0.bytes).0
    }

    /// Borrow the encoded elements when each occupies exactly one byte.
    #[must_use]
    pub fn byte_slice(self) -> ByteView<'a> {
        let (count, at) = read_u64(self.0.bytes);
        let payload = &self.0.bytes[at..];
        match count.and_then(|count| usize::try_from(count).ok()) {
            Some(count) if payload.len() == count => ByteView::Borrowed(payload),
            _ => ByteView::NeedsDecoding,
        }
    }

    /// Decode a spine whose one element field is a natural no greater than
    /// 255. The shape, not a source type name, establishes byte capability.
    #[must_use]
    pub fn to_bytes(self) -> Option<Vec<u8>> {
        let Shape::Spine {
            cons, recursive, ..
        } = shape(self.0.types, self.0.owner)
        else {
            return None;
        };
        let mut elements = self
            .0
            .types
            .fields(cons)
            .iter()
            .enumerate()
            .filter(|(at, _)| *at != recursive);
        let (_, &element) = elements.next()?;
        if elements.next().is_some() {
            return None;
        }
        let Shape::Spine { cons, .. } = shape(self.0.types, element) else {
            return None;
        };
        if self.0.types.fields(cons).len() != 1 {
            return None;
        }

        let (count, mut at) = read_u64(self.0.bytes);
        let count = usize::try_from(count?).ok()?;
        let mut bytes = Vec::with_capacity(count);
        for _ in 0..count {
            let (value, took) = read_u64(&self.0.bytes[at..]);
            bytes.push(u8::try_from(value?).ok()?);
            at += took;
        }
        (at == self.0.bytes.len()).then_some(bytes)
    }
}

impl<'a> ConstructorView<'a> {
    #[must_use]
    pub const fn constructor(self) -> CtorId {
        self.ctor
    }

    /// Borrow fields without materializing their constructor trees.
    ///
    /// # Errors
    /// If locating encoded field boundaries exceeds the budget.
    pub fn fields(self, budget: &mut Budget) -> Result<Vec<Constant<'a>>, LimitExceeded> {
        let value = self.constant;
        budget.bytes(value.bytes.len())?;
        budget.spend(
            u64::try_from(value.types.fields(self.ctor).len()).map_err(|_| LimitExceeded::Work)?,
        )?;
        let mut at = value.head().at;
        let mut fields = Vec::new();
        for &owner in value.types.fields(self.ctor) {
            let took = field_extent(value.types, owner, &value.bytes[at..], budget)?;
            fields.push(Constant::new(
                value.types,
                owner,
                &value.bytes[at..at + took],
            ));
            at += took;
        }
        Ok(fields)
    }
}

impl<'a> Constant<'a> {
    // Only the codec and pool may establish this invariant, including field views.
    pub(super) const fn new(types: TypeInfo<'a>, owner: TypeId, bytes: &'a [u8]) -> Self {
        Self {
            types,
            owner,
            bytes,
        }
    }

    #[must_use]
    pub const fn owner(self) -> TypeId {
        self.owner
    }

    #[must_use]
    pub const fn encoded(self) -> &'a [u8] {
        self.bytes
    }

    #[must_use]
    pub fn view(self) -> ConstantView<'a> {
        match shape(self.types, self.owner) {
            Shape::Spine { cons, .. } if self.types.fields(cons).len() == 1 => {
                ConstantView::Natural(NaturalView(self))
            }
            Shape::Spine { .. } => ConstantView::Spine(SpineView(self)),
            Shape::Tagged => ConstantView::Constructor(ConstructorView {
                constant: self,
                ctor: self.head().ctor,
            }),
        }
    }

    /// Identify the outer constructor without allocating or decoding a bigint.
    #[must_use]
    pub fn constructor(self) -> CtorId {
        self.head().ctor
    }

    pub(in crate::barb) fn to_owned(self, budget: &mut Budget) -> Result<Held, LimitExceeded> {
        budget.bytes(self.bytes.len())?;
        Ok(Held {
            owner: self.owner,
            bytes: self.bytes.to_vec(),
        })
    }

    fn head(self) -> Head {
        match shape(self.types, self.owner) {
            Shape::Spine {
                nil,
                cons,
                recursive,
            } => {
                let header = header_bytes(self.bytes).expect("a validated count");
                if header.iter().any(|byte| byte & 0x7f != 0) {
                    Head {
                        ctor: cons,
                        at: header.len(),
                        tail: Some(recursive),
                    }
                } else {
                    Head {
                        ctor: nil,
                        at: header.len(),
                        tail: None,
                    }
                }
            }
            Shape::Tagged => {
                let (tag, at) = if self.types.ctors(self.owner).len() > 1 {
                    let (tag, took) = read_u64(self.bytes);
                    (
                        u32::try_from(tag.expect("a validated tag")).expect("a validated tag"),
                        took,
                    )
                } else {
                    (0, 0)
                };
                Head {
                    ctor: self.types.ctor_at(self.owner, tag),
                    at,
                    tail: None,
                }
            }
        }
    }

    /// Split one value, charging before copies and while locating nested fields.
    /// Only requesting a tail decodes and decrements its count.
    pub(in crate::barb) fn parts(
        self,
        budget: &mut Budget,
    ) -> Result<(CtorId, Vec<Held>), LimitExceeded> {
        budget.bytes(self.bytes.len())?;
        let Head { ctor, mut at, tail } = self.head();
        budget.spend(
            u64::try_from(self.types.fields(ctor).len()).map_err(|_| LimitExceeded::Work)?,
        )?;
        let mut fields = Vec::new();
        for (index, &owner) in self.types.fields(ctor).iter().enumerate() {
            if tail != Some(index) {
                let took = field_extent(self.types, owner, &self.bytes[at..], budget)?;
                fields.push(Held {
                    owner,
                    bytes: self.bytes[at..at + took].to_vec(),
                });
                at += took;
            }
        }
        if let Some(recursive) = tail {
            // The head proved the count nonzero. No caller can request a
            // predecessor for an empty spine through this branch.
            let count = read_natural(self.bytes).0 - BigUint::one();
            let mut bytes = Vec::new();
            write_natural(&count, &mut bytes);
            bytes.extend_from_slice(&self.bytes[at..]);
            fields.insert(
                recursive,
                Held {
                    owner: self.owner,
                    bytes,
                },
            );
        }
        Ok((ctor, fields))
    }
}

/// Locate a field's end before creating a view of exactly one value.
fn field_extent(
    types: TypeInfo<'_>,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Result<usize, LimitExceeded> {
    checked::extent(types, owner, bytes, budget).map_err(|error| match error {
        super::DecodeError::Limit(limit) => limit,
        _ => unreachable!("a field of a validated constant: {error}"),
    })
}

struct Head {
    ctor: CtorId,
    at: usize,
    tail: Option<usize>,
}

impl Held {
    pub(in crate::barb) fn as_constant<'a>(&'a self, types: TypeInfo<'a>) -> Constant<'a> {
        Constant::new(types, self.owner, &self.bytes)
    }

    // Arithmetic recognition establishes this precondition. Public numeric
    // construction instead returns the validation error at the pool boundary.
    pub(in crate::barb) fn number(types: TypeInfo<'_>, owner: TypeId, n: &BigUint) -> Self {
        checked::natural(types, owner).expect("a proven natural type");
        let mut bytes = Vec::new();
        write_natural(n, &mut bytes);
        Self { owner, bytes }
    }

    pub(in crate::barb) fn build(
        types: TypeInfo<'_>,
        ctor: CtorId,
        fields: &[Self],
        budget: &mut Budget,
    ) -> Result<Self, ConstructionError> {
        checked::fields(
            types,
            ctor,
            fields.len(),
            fields.iter().map(|value| Ok(value.owner())),
        )?;
        Ok(Self::assemble(
            types,
            ctor,
            fields.iter().map(|value| value.as_constant(types)),
            budget,
        )?)
    }

    /// Both construction entry points validate fields before entering here.
    /// A cloned slice iterator permits sizing and tail lookup without collecting
    /// field views or allocating an owned value for each field.
    #[expect(
        clippy::too_many_lines,
        reason = "one encoding dispatch with its conservative reservation"
    )]
    pub(super) fn assemble<'a>(
        types: TypeInfo<'a>,
        ctor: CtorId,
        fields: impl ExactSizeIterator<Item = Constant<'a>> + Clone,
        budget: &mut Budget,
    ) -> Result<Self, LimitExceeded> {
        let owner = types.ctor(ctor).owner;
        let shape = shape(types, owner);
        let payload = fields
            .clone()
            .try_fold(0usize, |n, field| n.checked_add(field.bytes.len()))
            .ok_or(LimitExceeded::ValueSize)?;
        let overhead = if matches!(shape, Shape::Spine { .. }) {
            1
        } else {
            5
        };
        budget.bytes(
            payload
                .checked_add(overhead)
                .ok_or(LimitExceeded::ValueSize)?,
        )?;
        let mut bytes = Vec::new();
        match shape {
            Shape::Spine { nil, recursive, .. } => {
                if ctor == nil {
                    return Ok(Self {
                        owner,
                        bytes: vec![0],
                    });
                }
                let tail = fields
                    .clone()
                    .nth(recursive)
                    .expect("validated constructor arity")
                    .encoded();
                let (count, took) = read_natural(tail);
                write_natural(&(count + BigUint::one()), &mut bytes);
                for (at, field) in fields.enumerate() {
                    if at != recursive {
                        bytes.extend_from_slice(field.bytes);
                    }
                }
                bytes.extend_from_slice(&tail[took..]);
            }
            Shape::Tagged => {
                if types.ctors(owner).len() > 1 {
                    write_natural(&BigUint::from(types.tag(ctor)), &mut bytes);
                }
                for field in fields {
                    bytes.extend_from_slice(field.bytes);
                }
            }
        }
        Ok(Self { owner, bytes })
    }
}

pub(in crate::barb) fn natural_size(bits: u64) -> Result<usize, LimitExceeded> {
    usize::try_from(bits.div_ceil(7).max(1)).map_err(|_| LimitExceeded::ValueSize)
}
