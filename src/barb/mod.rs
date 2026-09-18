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

mod bounds;
mod builder;
mod constant;
mod facts;
mod fold;
mod ir;
mod parse;
mod pretty;

pub use bounds::Bounds;
pub use builder::Builder;
pub use constant::{Shape, Value, as_bytes, as_number, decode, shape};
pub use facts::{Facts, Operation, recognise};
pub use fold::fold;
pub use ir::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Local, Program, Range,
    Symbol, Type, TypeId,
};
pub use parse::parse;

/// Which argument a name something outside answers for hands back, where it
/// hands one back at all. The effects are the one place a name has no body
/// to read, so this is the one thing that has to be said of them rather
/// than worked out.
fn answered(name: &str) -> Option<usize> {
    parse::EFFECTS
        .into_iter()
        .find(|(held, ..)| *held == name)
        .and_then(|(_, _, answers)| match answers {
            parse::Answers::Argument(held) => Some(held),
            parse::Answers::Never => None,
        })
}

#[cfg(test)]
mod tests;
