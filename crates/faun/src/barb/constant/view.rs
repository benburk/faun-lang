//! Semantic views of validated constants. Constructors are private: callers
//! refine a constant into disjoint structural cases, not competing guesses at
//! what untyped bytes might mean. Recursive scans retain the shared budget.

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::{
    ConstructionError, Held, Shape, check_fields, read_natural, read_u64, shape, write_natural,
};
use crate::barb::budget::{Budget, LimitExceeded};
use crate::barb::{ConstId, CtorId, Program, TypeId};

/// A borrowed, well-typed value in this program's encoding.
/// Obtain it from [`Program::constant`], never by attaching a type to raw bytes.
///
/// ```compile_fail
/// use faun::barb::{Constant, Program, TypeId};
/// let program = Program::default();
/// let forged = Constant { program: &program, owner: TypeId::at(0), bytes: &[0] };
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Constant<'a> {
    program: &'a Program,
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
}

impl<'a> ConstructorView<'a> {
    #[must_use]
    pub const fn constructor(self) -> CtorId {
        self.ctor
    }

    /// Borrow the fields without materializing their constructor trees.
    ///
    /// # Errors
    /// If locating encoded field boundaries exceeds the budget.
    pub fn fields(self, budget: &mut Budget) -> Result<Vec<Constant<'a>>, LimitExceeded> {
        let value = self.constant;
        // Borrowing avoids copies, not the work of scanning encoded headers.
        budget.bytes(value.bytes.len())?;
        budget.spend(
            u64::try_from(value.program.fields(self.ctor).len())
                .map_err(|_| LimitExceeded::Work)?,
        )?;
        let mut at = value.head().at;
        let mut fields = Vec::new();
        for &owner in value.program.fields(self.ctor) {
            let took = field_extent(value.program, owner, &value.bytes[at..], budget)?;
            fields.push(Constant::new(
                value.program,
                owner,
                &value.bytes[at..at + took],
            ));
            at += took;
        }
        Ok(fields)
    }
}

impl<'a> Constant<'a> {
    pub(in crate::barb) fn stored(program: &'a Program, id: ConstId) -> Self {
        Self::new(program, program.consts[id].owner, program.known_bytes(id))
    }

    // Only the codec may establish this invariant, including views into fields.
    const fn new(program: &'a Program, owner: TypeId, bytes: &'a [u8]) -> Self {
        Self {
            program,
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
        match shape(self.program, self.owner) {
            Shape::Spine { cons, .. } if self.program.fields(cons).len() == 1 => {
                ConstantView::Natural(NaturalView(self))
            }
            Shape::Spine { .. } => ConstantView::Spine(SpineView(self)),
            Shape::Tagged => ConstantView::Constructor(ConstructorView {
                constant: self,
                ctor: self.head().ctor,
            }),
        }
    }

    /// Every valid value has an outer constructor, including a compact natural.
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
        let (ctor, at, tail) = match shape(self.program, self.owner) {
            Shape::Spine {
                nil,
                cons,
                recursive,
            } => {
                let (count, took) = read_natural(self.bytes);
                if count.is_zero() {
                    return Head {
                        ctor: nil,
                        at: took,
                        tail: None,
                    };
                }
                (cons, took, Some((recursive, count - BigUint::one())))
            }
            Shape::Tagged => {
                let (tag, took) = if self.program.ctors(self.owner).len() > 1 {
                    let (tag, took) = read_u64(self.bytes);
                    (
                        u32::try_from(tag.expect("a validated tag")).expect("a validated tag"),
                        took,
                    )
                } else {
                    (0, 0)
                };
                (self.program.ctor_at(self.owner, tag), took, None)
            }
        };
        Head { ctor, at, tail }
    }

    /// Split one value, charging before copies and while locating nested fields.
    /// A spine's tail needs a new count prefix, not just a borrowed slice.
    pub(in crate::barb) fn parts(
        self,
        budget: &mut Budget,
    ) -> Result<(CtorId, Vec<Held>), LimitExceeded> {
        budget.bytes(self.bytes.len())?;
        let Head { ctor, mut at, tail } = self.head();
        budget.spend(
            u64::try_from(self.program.fields(ctor).len()).map_err(|_| LimitExceeded::Work)?,
        )?;
        let mut fields = Vec::new();
        for (index, &owner) in self.program.fields(ctor).iter().enumerate() {
            if tail
                .as_ref()
                .is_none_or(|(recursive, _)| index != *recursive)
            {
                let took = field_extent(self.program, owner, &self.bytes[at..], budget)?;
                fields.push(Held {
                    owner,
                    bytes: self.bytes[at..at + took].to_vec(),
                });
                at += took;
            }
        }
        if let Some((recursive, count)) = tail {
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

/// A field starts a stream that may also contain later fields. Locate its end
/// before creating a Constant: a Constant always contains exactly one value.
fn field_extent(
    program: &Program,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Result<usize, LimitExceeded> {
    super::checked::extent(program, owner, bytes, budget).map_err(|error| match error {
        super::DecodeError::Limit(limit) => limit,
        _ => unreachable!("a field of a validated constant: {error}"),
    })
}

struct Head {
    ctor: CtorId,
    at: usize,
    tail: Option<(usize, BigUint)>,
}

impl Held {
    pub(in crate::barb) fn as_constant<'a>(&'a self, program: &'a Program) -> Constant<'a> {
        Constant::new(program, self.owner, &self.bytes)
    }

    pub(in crate::barb) fn number(program: &Program, owner: TypeId, n: &BigUint) -> Self {
        assert!(
            matches!(shape(program, owner), Shape::Spine { cons, .. } if program.fields(cons).len() == 1),
            "a natural type"
        );
        let mut bytes = Vec::new();
        write_natural(n, &mut bytes);
        Self { owner, bytes }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "keep the encoding cases and their checked preflight together"
    )]
    pub(in crate::barb) fn build(
        program: &Program,
        ctor: CtorId,
        fields: &[Self],
        budget: &mut Budget,
    ) -> Result<Self, ConstructionError> {
        check_fields(
            program,
            ctor,
            fields.len(),
            fields.iter().map(|value| Ok(value.owner())),
        )?;
        let owner = program.ctor(ctor).owner;
        // Preserve conservative reservations and copying charges.
        let payload = fields
            .iter()
            .try_fold(0usize, |n, f| n.checked_add(f.bytes.len()))
            .ok_or(LimitExceeded::ValueSize)?;
        let overhead = if matches!(shape(program, owner), Shape::Spine { .. }) {
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
        match shape(program, owner) {
            Shape::Spine { nil, recursive, .. } => {
                if ctor == nil {
                    return Ok(Self {
                        owner,
                        bytes: vec![0],
                    });
                }
                let tail = &fields[recursive].bytes;
                let (count, took) = read_natural(tail);
                write_natural(&(count + BigUint::one()), &mut bytes);
                for (at, field) in fields.iter().enumerate() {
                    if at != recursive {
                        bytes.extend_from_slice(&field.bytes);
                    }
                }
                bytes.extend_from_slice(&tail[took..]);
            }
            Shape::Tagged => {
                if program.ctors(owner).len() > 1 {
                    write_natural(&BigUint::from(program.tag(ctor)), &mut bytes);
                }
                for field in fields {
                    bytes.extend_from_slice(&field.bytes);
                }
            }
        }
        Ok(Self { owner, bytes })
    }
}

pub(in crate::barb) fn natural_size(bits: u64) -> Result<usize, LimitExceeded> {
    usize::try_from(bits.div_ceil(7).max(1)).map_err(|_| LimitExceeded::ValueSize)
}
