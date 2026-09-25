//! The first-order program Barb lowering reads.
//!
//! [`crate::callbacks`] leaves no function value: every callback is made
//! into the definition it is handed to, and every call of one is direct.
//! What is left is the specialized program with nothing but data flowing
//! between definitions, which these types say by having no way to hold a
//! function.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::hir::{self as h, LocalId};
use crate::specialize::{self, FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

/// A specialized program whose values are all data.
#[derive(Clone, Debug)]
pub(crate) struct Program {
    /// Where the program starts, when it is an application.
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, h::DataDecl>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) clauses: Vec<Clause>,
    pub(crate) provider: Option<Symbol>,
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
    Construct(Symbol, Vec<Expr>),
    Record(Vec<(Symbol, Expr)>),
    /// A record with the fields named replaced.
    Update(Box<Expr>, Vec<(Symbol, Expr)>),
    Tuple(Vec<Expr>),
    Project(Box<Expr>, Symbol),
    DirectCall(FunctionKey, Vec<Expr>),
    /// The value as this expression's wider type; see
    /// [`specialize::ExprKind::Widen`].
    Widen(Box<Expr>),
    /// `value?`; see [`specialize::ExprKind::Try`].
    Try(Box<Expr>),
}

/// `program`, whose function values [`crate::callbacks`] has made into
/// definitions, as the first-order program it is.
///
/// # Panics
///
/// If a function value is left, which callback specialization refuses.
pub(crate) fn first_order(program: specialize::Program) -> Program {
    Program {
        entry: program.entry,
        functions: program.functions.into_iter().map(function).collect(),
        data: program.data,
    }
}

fn function(function: specialize::Function) -> Function {
    Function {
        key: function.key,
        clauses: function
            .clauses
            .into_iter()
            .map(|clause| Clause {
                patterns: clause.patterns,
                guard: clause.guard.map(expr),
                body: body(clause.body),
            })
            .collect(),
        provider: function.provider,
    }
}

fn body(body: specialize::Body) -> Body {
    Body {
        bindings: body
            .bindings
            .into_iter()
            .map(|binding| Binding {
                pattern: binding.pattern,
                value: expr(binding.value),
            })
            .collect(),
        result: expr(body.result),
    }
}

fn exprs(expressions: Vec<specialize::Expr>) -> Vec<Expr> {
    expressions.into_iter().map(expr).collect()
}

fn expr(expression: specialize::Expr) -> Expr {
    use specialize::ExprKind as S;
    let kind = match expression.kind {
        S::Local(local) => ExprKind::Local(local),
        S::Natural(magnitude) => ExprKind::Natural(magnitude),
        S::Construct(constructor, fields) => ExprKind::Construct(constructor, exprs(fields)),
        S::Record(fields) => ExprKind::Record(
            fields
                .into_iter()
                .map(|(name, field)| (name, expr(field)))
                .collect(),
        ),
        S::Update(base, fields) => ExprKind::Update(
            Box::new(expr(*base)),
            fields
                .into_iter()
                .map(|(name, field)| (name, expr(field)))
                .collect(),
        ),
        S::Tuple(members) => ExprKind::Tuple(exprs(members)),
        S::Project(receiver, field) => ExprKind::Project(Box::new(expr(*receiver)), field),
        S::DirectCall(key, arguments) => ExprKind::DirectCall(key, exprs(arguments)),
        S::Widen(value) => ExprKind::Widen(Box::new(expr(*value))),
        S::Try(value) => ExprKind::Try(Box::new(expr(*value))),
        S::Function(_) | S::ConstructorFunction(_) | S::Lambda(..) | S::Invoke(..) => {
            unreachable!("callback specialization leaves no function value")
        }
    };
    Expr {
        module: expression.module,
        span: expression.span,
        ty: expression.ty,
        kind,
    }
}
