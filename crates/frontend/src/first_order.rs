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
use crate::specialize::{Connective, FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

/// A specialized program whose values are all data.
#[derive(Clone, Debug)]
pub(crate) struct Program {
    /// Where the program starts, when it is an application.
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, crate::declarations::Data>,
    /// Where each definition is written, which a refusal naming one by
    /// name points at.
    pub(crate) written: HashMap<Symbol, (ModuleId, crate::ast::Span)>,
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

impl Body {
    /// Each line's value, then the answer.
    pub(crate) fn exprs(&self) -> impl Iterator<Item = &Expr> {
        let values = self.bindings.iter().map(|binding| &binding.value);
        values.chain([&self.result])
    }
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

impl Expr {
    /// Visit each expression directly inside this one, in the order it is
    /// worked out. A walk matches the forms it has something to say of and
    /// leaves the rest to this.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per expression form, so a new form must say what is inside it"
    )]
    pub(crate) fn for_each_child<'a>(&'a self, mut visit: impl FnMut(&'a Self)) {
        match &self.kind {
            ExprKind::Local(_) | ExprKind::Natural(_) | ExprKind::Bytes(_) => {}
            ExprKind::Construct(_, list)
            | ExprKind::Tuple(list)
            | ExprKind::DirectCall(_, list) => list.iter().for_each(visit),
            ExprKind::Record(fields) => {
                for (_, value) in fields {
                    visit(value);
                }
            }
            ExprKind::Update(base, fields) => {
                visit(base);
                for (_, value) in fields {
                    visit(value);
                }
            }
            ExprKind::Project(inner, _)
            | ExprKind::Widen(inner)
            | ExprKind::Try(inner)
            | ExprKind::Return(inner) => visit(inner),
            ExprKind::Connective(_, left, right) => {
                visit(left);
                visit(right);
            }
            ExprKind::If(condition, yes, no) => {
                visit(condition);
                visit(yes);
                visit(no);
            }
            ExprKind::Is(value, rows) => {
                visit(value);
                rows.iter()
                    .filter_map(|(_, guard)| guard.as_ref())
                    .for_each(visit);
            }
            ExprKind::Match(value, arms) => {
                visit(value);
                for arm in arms {
                    let guards = arm.rows.iter().filter_map(|(_, guard)| guard.as_ref());
                    guards.chain([&arm.body]).for_each(&mut visit);
                }
            }
            ExprKind::Block(body) => body.exprs().for_each(visit),
        }
    }

    /// Visit this expression, then every one inside it.
    pub(crate) fn for_each_within<'a>(&'a self, visit: &mut impl FnMut(&'a Self)) {
        visit(self);
        self.for_each_child(|child| child.for_each_within(visit));
    }

    /// Visit each local this expression binds itself, not those its
    /// children bind.
    pub(crate) fn for_each_bound(&self, mut visit: impl FnMut(LocalId)) {
        let visit = &mut visit;
        match &self.kind {
            ExprKind::Is(_, rows) => rows
                .iter()
                .for_each(|(pattern, _)| pattern.for_each_bound(visit)),
            ExprKind::Match(_, arms) => {
                let rows = arms.iter().flat_map(|arm| &arm.rows);
                for (pattern, _) in rows {
                    pattern.for_each_bound(visit);
                }
            }
            ExprKind::Block(body) => {
                for binding in &body.bindings {
                    binding.pattern.for_each_bound(visit);
                }
            }
            _ => {}
        }
    }
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
    /// `left & right` or `left | right` on `Bool`; see
    /// [`crate::specialize::ExprKind::Connective`].
    Connective(Connective, Box<Expr>, Box<Expr>),
    /// The value as this expression's wider type; see
    /// [`crate::specialize::ExprKind::Widen`].
    Widen(Box<Expr>),
    /// `value?`; see [`crate::specialize::ExprKind::Try`].
    Try(Box<Expr>),
    /// `return value`; see [`crate::hir::ExprKind::Return`]. Pattern
    /// compiling makes the branch it ends one answering the function.
    Return(Box<Expr>),
    /// `if condition then yes else no`; see [`crate::hir::ExprKind::If`].
    /// Pattern compiling binds it on a line of its own, each branch a body.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`; see [`crate::hir::ExprKind::Is`]. Pattern
    /// compiling makes each a match, the names it binds in scope where it
    /// holds.
    Is(Box<Expr>, Vec<(Pattern, Option<Expr>)>),
    /// `value is ( arms )`; see [`crate::hir::ExprKind::Match`]. Pattern
    /// compiling binds it on a line of its own, one decision for every arm.
    Match(Box<Expr>, Vec<Arm>),
    /// Bindings, then the answer; see [`crate::hir::ExprKind::Block`].
    /// Pattern compiling takes its bindings out ahead of the expression it
    /// stands in.
    Block(Box<Body>),
}

/// One arm; see [`crate::specialize::Arm`].
#[derive(Clone, Debug)]
pub(crate) struct Arm {
    pub(crate) rows: Vec<(Pattern, Option<Expr>)>,
    pub(crate) body: Expr,
}
