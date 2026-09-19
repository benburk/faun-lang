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
//! - blocks — chains of [`Expr::Let`]
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
//! definition stopping. A program built rather than written is checked the
//! same way, so none of it rests on a frontend's good manners.
//!
//! Two things are left to one, because nothing here can see them:
//!
//! - **What a name with no body does.** Such a name is something outside
//!   answers for, and nothing about it can be read — so what is known of
//!   one is what the tier above said, which is today [`Function::bounds`]
//!   for a finite host result, and will be more.
//! - **The order those names run in.** Nothing here is observable, so
//!   nothing here orders anything: a program whose operations must happen
//!   in an order says so by handing each one a value the next one takes.
//!   Then the order is what every pass already respects, and an operation
//!   is kept because something reads what it answered, up to whatever the
//!   program itself answers. Say it another way and this tier does what the
//!   program actually said rather than what was meant by it.
//!
//! # What a pass may do
//!
//! Anything that keeps what the program answers, with one exception.
//!
//! There is no effect here. A name with no body is a value something
//! outside works out: ordered where dataflow orders it, dropped where
//! nothing reads it, and otherwise opaque. What a target does while running
//! one cannot be seen from here, so the rule is about how many times such a
//! call runs rather than where it sits.
//!
//! > A pass may not make a call to a bodyless function run more times on
//! > any path than the program says.
//!
//! Lifting one out of a single arm breaks it, since the path through the
//! other arm did not run it. Lifting one out of every arm does not, nor
//! does pushing a copy into each: what runs on a path is what ran before.
//! Everything else is free -- a pure term may be moved, shared, dropped, or
//! worked out here rather than left to run there, and totality is what
//! makes the last of those stop.
//!
//! Doing less work is the point of a pass rather than a rule over one.
//! Nothing here knows what a branch costs, what a word is, or how often
//! anything runs, so the tier that knows prices is the tier that may trade
//! work for time.

mod arithmetic;
mod bounds;
mod builder;
mod constant;
mod evaluate;
mod facts;
mod fold;
mod ir;
mod normalize;
mod pretty;
mod stops;
mod validate;

pub use bounds::Bounds;
pub use builder::Builder;
pub use constant::{Shape, Value, as_bytes, as_natural, as_number, decode, shape};
pub use facts::{Facts, Operation, recognise};
pub use fold::fold;
pub use ir::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Local, Program, Range,
    Symbol, Type, TypeId,
};
pub use normalize::normalize;
pub use validate::validate;

#[cfg(test)]
mod arithmetic_tests;
#[cfg(test)]
mod tests;
