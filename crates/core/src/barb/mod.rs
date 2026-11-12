//! barb: the first-order core IR.
//!
//! It decides:
//!
//! - The inductive types a program is built from, and their constructors
//! - Which operations run, over which values, in what order
//! - That every function is defined for every input
//!
//! It does not decide:
//!
//! - How a value is represented, how wide it is, or where it is laid out
//! - Where a value is retained, released, or reused in place
//! - Anything a target names
//!
//! Every value is an inductive term, and the term language is in A-normal
//! form: an argument is an [`Atom`], an atom is a local, and anything else
//! is let-bound first. Monomorphisation and defunctionalisation happen above
//! this tier, so a type is a name with constructors and nothing more — no
//! parameters, no arrows, no variables.
//!
//! Deliberately absent, each folding into something simpler:
//!
//! - `If` — a [`Expr::Match`] on `Bool`
//! - tuples and records — single-constructor inductives
//! - blocks — ordered bindings and a tail expression in a [`Body`]
//! - `absurd` — a match with no arms
//! - `Lam`/`App` — first-order; recursion lives between top-level names
//! - primitives — arithmetic is recursion over a constructor, and the
//!   recognizer establishes the arithmetic facts used by lower tiers
//!
//! # What a program has to be
//!
//! [`validate`] answers most of it: every call and construction saturated,
//! every name a term reads bound by something above it, every match with an
//! arm per constructor in the order the declaration gave them. A program
//! built rather than written gets these checks too. Whether a definition
//! stops is not asked; see [`optimize`] for what that allows. This is not a full type checker or a validator for corrupted arenas:
//! frontend typing and the pool-construction invariants remain preconditions.
//!
//! Two other things must come from outside, because nothing here can see them:
//!
//! - **What a name with no body does.** Such a name is something outside
//!   answers for, and nothing about it can be read. Barb knows no target, so
//!   it takes no range for one, nor for what the entry is handed: the tier
//!   lowering the program says what it assumes of values from outside, as
//!   an [`Assumed`], and the analysis it asks for is its own.
//! - **What effects those names perform.** Calls reaching a bodyless name
//!   are observable even if their answers are unused. Their order, path and
//!   multiplicity are preserved without a world-state argument.
//!
//! # What a pass may do
//!
//! Preserve answers and eager evaluation of opaque calls. A bodyless name
//! may perform an effect or exit without returning, even if its result is
//! unused. Without further proof, keep its multiplicity, order and path.
//!
//! A definition with a body may never come back: nothing here asks whether
//! one stops. Where its answer is needed, by a bodyless call, by the entry's
//! answer, or by a match deciding either, a call that never comes back hangs
//! the program there. Where its answer is not needed and it reaches no
//! bodyless name, a pass may leave it out, so whether it would have come
//! back is not observable. That is all the license there is: a pass never
//! concludes that anything stops, and so never derives from a call that it
//! must have answered.
//!
//! The bounded optimizer substitutes already-evaluated ANF atoms, leaves
//! argument bindings in place when applying laws. Cleanup removes aliases and
//! unused pure expressions, including calls reaching no bodyless name and
//! matches with only pure arms. It retains calls and matches with effects.
//! Constant evaluation refuses a whole call or match if any
//! selected eager binding cannot be evaluated, and its budget bounds the
//! work, so a definition that never comes back cannot hang the compiler.
//!
//! Doing less work is the point of a pass rather than a rule over one.
//! Nothing here knows what a branch costs, what a word is, or how often
//! anything runs, so the tier that knows prices is the tier that may trade
//! work for time.
//!
//! # Code organization
//!
//! - `model`: terms, declarations, IDs, and their small intrinsic methods.
//! - `program`: [`Program`], its pools, queries, and construction entry points.
//! - `builder`: [`Builder`], the temporary state for scoped body construction.
//! - Other modules own named algorithms: validation, analysis, rendering,
//!   and rewriting. A capability-specific impl may live with its algorithm;
//!   ordinary program queries and mutations stay with the owning type.
//!
//! The machine IR follows the same split. Public types are re-exported here;
//! the file layout is not part of the public API.

mod affine;
mod arithmetic;
mod bounds;
mod budget;
mod builder;
mod calls;
mod claim;
mod cleanup;
mod constant;
mod copy;
mod counters;
mod descent;
mod evaluate;
mod facts;
#[cfg(test)]
pub(crate) mod fixture;
mod forward;
mod fuse;
mod head;
mod inline;
mod inplace;
mod model;
mod normalize;
mod optimize;
mod pretty;
mod program;
mod sequence;
mod specialize;
mod sweep;
mod terms;
mod types;
mod validate;
mod walk;

pub use affine::Affine;
pub use bounds::{Assumed, Bounds};
pub use budget::{Budget, FoldLimits, LimitExceeded};
pub use builder::Builder;
pub use constant::{
    ByteView, Constant, ConstantView, ConstructionError, ConstructorView, NaturalView, SpineView,
    TooWide, Value,
};
// `Shape` is how the constant codec reads an encoding, which is a different
// question from how a value is held. Representation selection asks
// `TypeShape`, so nothing outside this tier needs this one.
pub(crate) use constant::Shape;
pub use facts::{Facts, Operation, SequenceLengths, SequenceOperation};

pub use inline::InlineLimits;
pub use model::{
    Arm, Atom, Body, ByteSequence, ConstId, Ctor, CtorId, Definition, Expr, ExprId, Field, FnId,
    Function, Local, Range, Symbol, Type, TypeId,
};
#[cfg(test)]
pub(crate) use normalize::fold;
#[cfg(test)]
pub(crate) use normalize::normalize_with_limits;
pub(crate) use normalize::structural;
pub use optimize::optimize;
pub(crate) use program::shape;
pub use program::{Program, type_shape};
pub use program::{single_field, single_field_constant};
pub use types::TypeShape;
pub use validate::{Refusal, validate};

/// Individual optimizer steps used to construct machine-IR test inputs.
#[cfg(feature = "backend-tests")]
pub mod test_support {
    use super::{InlineLimits, Program, normalize};

    pub fn structural(program: &mut Program) {
        normalize::structural(program);
    }

    pub fn normalize_with_limits(program: &mut Program, limits: InlineLimits) {
        normalize::normalize_with_limits(program, limits);
    }

    pub fn fold(program: &mut Program) {
        normalize::fold(program);
    }
}

#[cfg(test)]
use constant::decode;

#[cfg(test)]
mod arithmetic_tests;
#[cfg(test)]
mod bitwise_tests;
#[cfg(test)]
mod constant_tests;
#[cfg(test)]
mod library_tests;
#[cfg(test)]
mod normalization_tests;
#[cfg(test)]
mod optimization_tests;
#[cfg(test)]
mod tests;
