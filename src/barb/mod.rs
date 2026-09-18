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
//!   machine tier is what recognises it
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
//!   one is what the tier above said, which is today [`Function::answers`]
//!   and will be more.
//! - **The order those names run in.** Nothing here is observable, so
//!   nothing here orders anything: a program whose operations must happen
//!   in an order says so by handing each one a value the next one takes.
//!   Then the order is what every pass already respects, and a program that
//!   must reach its last operation reaches it because the last one answers
//!   what the program answers.
//!
//! # What a pass may do
//!
//! Rewrite a program to do less work. That is the whole model: nothing here
//! knows what a branch costs, what a word is, or how often anything runs,
//! so nothing here is in a position to spend work to save time. The tier
//! that knows what things cost is the tier that may make that trade.
//!
//! One rule follows from it and is worth stating on its own, since it is
//! the one a pass could break while believing it was doing less work:
//!
//! > A pass may not move a term out of an arm into what runs before it,
//! > since an arm may not run.
//!
//! Everything else a pass might want is already safe. Moving a term *into*
//! the arm that needs it does less work, and so does moving one out of
//! every arm at once. Dropping a term nothing reads does less work. Two
//! terms that are the same term are one term's work. And working a term out
//! here rather than leaving it to run there is no work at all, which is
//! what totality buys: a term that is worth working out is a term that
//! stops.

mod bounds;
mod builder;
mod constant;
mod facts;
mod fold;
mod ir;
mod pretty;
mod stops;
mod validate;

pub use bounds::Bounds;
pub use builder::Builder;
pub use constant::{Shape, Value, as_bytes, as_number, decode, shape};
pub use facts::{Facts, Operation, recognise};
pub use fold::fold;
pub use ir::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Local, Program, Range,
    Symbol, Type, TypeId,
};
pub use validate::validate;

#[cfg(test)]
mod tests;
