//! barb: the first-order core IR.
//!
//! It decides:
//!
//! - The inductive types a program is built from, and their constructors
//! - Which operations run, over which values, in what order
//! - Totality: that every function is defined for every input and stops
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
//! arm per constructor in the order the declaration gave them, and every
//! definition stopping. A program built rather than written gets these checks
//! too. This is not a full type checker or a validator for corrupted arenas:
//! frontend typing and the pool-construction invariants remain preconditions.
//!
//! Two other things must come from outside, because nothing here can see them:
//!
//! - **What a name with no body does.** Such a name is something outside
//!   answers for, and nothing about it can be read — so what is known of
//!   one is what the tier above said, which is today [`Function::bounds`]
//!   for a finite host result, and will be more.
//! - **What effects those names perform.** Programs express dependencies by
//!   threading state through calls. Optimizations also retain eager bindings:
//!   an unused answer does not prove a call harmless or that it returns.
//!
//! # What a pass may do
//!
//! Preserve answers and eager evaluation of opaque calls. A bodyless name
//! may perform an effect or exit without returning, even if its result is
//! unused. Without further proof, keep its multiplicity, order and path.
//!
//! The bounded optimizer substitutes already-evaluated ANF atoms, leaves
//! argument bindings in place when applying laws. Cleanup removes aliases and
//! unused atoms, constants and constructors, but retains calls and matches.
//! Constant evaluation refuses a whole call or match if any
//! selected eager binding cannot be evaluated. Totality checking runs before
//! any of these rewrites; optimization must not hide a rejected definition.
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

mod arithmetic;
mod bounds;
mod budget;
mod builder;
mod cleanup;
mod constant;
mod evaluate;
mod facts;
mod fold;
mod inline;
mod laws;
mod model;
mod normalize;
mod optimize;
mod pretty;
mod program;
mod stops;
mod validate;

pub use bounds::Bounds;
pub use budget::{Budget, FoldLimits, LimitExceeded};
pub use builder::Builder;
pub use constant::{
    ByteView, Constant, ConstantView, ConstructionError, ConstructorView, DecodeError, NaturalView,
    Shape, SpineView, TooWide, Value, shape,
};
pub use facts::{Facts, Operation, analyze};
pub use fold::{fold, fold_with_limits};
pub use inline::InlineLimits;
pub use model::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Definition, Expr, ExprId, FnId, Function, Local, Range,
    Symbol, Type, TypeId,
};
pub use normalize::{normalize_with_limits, structural};
pub use optimize::{OptimizeOptions, optimize};
pub use program::Program;
pub use validate::validate;

#[cfg(test)]
use constant::decode;

#[cfg(test)]
mod arena_tests;
#[cfg(test)]
mod arithmetic_tests;
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
