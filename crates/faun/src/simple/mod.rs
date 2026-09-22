//! The archived simple frontend: text read directly into [`barb`](crate::barb).
//!
//! This remains the smallest executable test of the core and backends. It is
//! deliberately close to Barb: first-order, monomorphic, and without the type
//! inference or richer forms of the primary [`surface`](crate::surface)
//! frontend. New language work belongs there; compatibility fixes for old
//! `.fn` programs belong here.
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
