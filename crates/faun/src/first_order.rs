//! The first-order program resource checking and pattern compilation read.
//!
//! [`crate::callbacks`] leaves no function value: every callback is made
//! into the definition it is handed to, and every call of one is direct.
//! What is left is the specialized program with nothing but data flowing
//! between definitions, which these types say by having no way to hold a
//! function. Function signatures and the distinction between external providers
//! and defined bodies survive callback lowering.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::hir::LocalId;
use crate::specialize::{FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

/// A specialized program whose values are all data.
#[derive(Clone, Debug)]
pub(crate) struct Program {
    /// Where the program starts, when it is an application.
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, crate::declarations::Data>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) definition: Definition,
}

/// Keep a provider declaration separate from a body, even one with no clauses.
#[derive(Clone, Debug)]
pub(crate) enum Definition {
    External(Symbol),
    Body(Vec<Clause>),
}

#[derive(Clone, Debug)]
pub(crate) struct Clause {
    pub(crate) patterns: Vec<Pattern>,
    pub(crate) guard: Option<Expr>,
    pub(crate) body: Body,
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) bindings: Vec<Binding>,
    pub(crate) result: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub(crate) pattern: Pattern,
    pub(crate) value: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Expr {
    /// Where it was written, which a diagnostic about it points at.
    pub(crate) module: ModuleId,
    pub(crate) span: crate::ast::Span,
    pub(crate) ty: Type,
    pub(crate) kind: ExprKind,
}

#[derive(Clone, Debug)]
pub(crate) enum ExprKind {
    Local(LocalId),
    Natural(BigUint),
    /// A `List(U8)` known whole.
    Bytes(Vec<u8>),
    Construct(Symbol, Vec<Expr>),
    Record(Vec<(Symbol, Expr)>),
    /// A record with the fields named replaced.
    Update(Box<Expr>, Vec<(Symbol, Expr)>),
    Tuple(Vec<Expr>),
    Project(Box<Expr>, Symbol),
    DirectCall(FunctionKey, Vec<Expr>),
    /// The value as this expression's wider type; see
    /// [`crate::specialize::ExprKind::Widen`].
    Widen(Box<Expr>),
    /// `value?`; see [`crate::specialize::ExprKind::Try`].
    Try(Box<Expr>),
    /// `if condition then yes else no`; see [`crate::hir::ExprKind::If`].
    /// Pattern compiling binds it on a line of its own, each branch a body.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`; see [`crate::hir::ExprKind::Is`]. Pattern
    /// compiling makes each a match, the names it binds in scope where it
    /// holds.
    Is(Box<Expr>, Vec<(Pattern, Option<Expr>)>),
    /// Bindings, then the answer; see [`crate::hir::ExprKind::Block`].
    /// Pattern compiling takes its bindings out ahead of the expression it
    /// stands in.
    Block(Box<Body>),
}
