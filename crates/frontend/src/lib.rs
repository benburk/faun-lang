//! The primary Faun frontend, following Ori's source language.
//!
//! Parsing retains compact source spans. Module loading and qualification then
//! produce symbol-based HIR without merging raw ASTs. Checking performs
//! Hindley–Milner inference, nominal receiver-directed method resolution, and
//! contextual literal elaboration. Reachable monomorphic entries can then be
//! specialized, defunctionalized, and lowered to Barb.

pub mod ast;
mod barb_lower;
pub mod blessed;
pub mod check;
mod grammar;
pub mod hir;
pub mod lex;
pub mod literal;
pub mod lower;
pub mod modules;
mod parse;
pub mod resolve;
pub mod source;
mod specialize;
pub mod symbol;

pub use modules::ModuleId;
pub use parse::{ParseError, parse, parse_in};
pub use source::{Source, SourceId, Sources};
pub use symbol::{Symbol, Symbols};

#[cfg(test)]
mod tests;
