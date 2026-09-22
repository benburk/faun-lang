//! The primary Faun frontend, following Ori's source language.
//!
//! Parsing retains compact source spans. Module loading and qualification then
//! produce symbol-based HIR without merging raw ASTs. The first checking slice
//! supplies contextual `Nat`, `Int`, and `Str` literal elaboration; full type
//! inference and whole-program Barb lowering remain separate work.

pub mod ast;
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
pub mod symbol;

pub use modules::ModuleId;
pub use parse::{ParseError, parse, parse_in};
pub use source::{Source, SourceId, Sources};
pub use symbol::{Symbol, Symbols};

#[cfg(test)]
mod tests;
