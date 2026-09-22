//! The primary Faun frontend, following Ori's source language.
//!
//! This first slice contains the allocation-light lexer and a PEG grammar for
//! nominal constructor types, first-order signatures, function clauses, local
//! bindings, calls, methods, and operators. The accepted language is a strict
//! subset of Ori: unsupported forms are rejected at parsing rather than kept in
//! an AST that the compiler cannot yet lower.

pub mod ast;
mod grammar;
pub mod lex;
mod parse;

pub use parse::{ParseError, parse};

#[cfg(test)]
mod tests;
