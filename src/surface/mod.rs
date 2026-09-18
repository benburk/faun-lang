//! A surface: text a program is written in, read into [`barb`](crate::barb).
//!
//! The tier below is a core, not a language: inductive types and rewrites,
//! everything first-order, nothing partial, and no representation. This is
//! one language over it, and deliberately the closest one -- what it adds
//! is a syntax, names for what a clause matches, an authority, and a rule
//! about what may do observable work. It adds no generics, no inference
//! beyond which declared type a name has, and nothing that specialises.
//!
//! What is here rather than below is everything a different language over
//! the same core would want to decide differently: how a program is
//! written, what its builtin types are, which names something outside
//! answers for, and what may call them. The core is told the answers and
//! never the rules -- a definition with no body is one something outside
//! answers for, whatever the language above calls that.

mod parse;

pub use parse::parse;

#[cfg(test)]
mod tests;
