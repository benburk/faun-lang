//! Checked HIR: types and elaboration decisions belong to their occurrences.
//!
//! Calls through generic bounds and generic numerals remain explicit until
//! specialization. No source syntax or site-indexed inference tables are needed
//! to interpret an expression. Patterns cannot contain an ambiguous constructor.

use std::collections::HashMap;
use std::convert::Infallible;

use crate::ast::Span;
use crate::blessed::LiteralExpr;
use crate::check::{InferredBound, InferredScheme, InferredType};
use crate::hir::{self as h, LocalId, SiteId};
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub data: HashMap<Symbol, crate::declarations::Data>,
    pub members: HashMap<(Symbol, Symbol), Symbol>,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub module: ModuleId,
    pub span: Span,
    pub name: Symbol,
    pub scheme: InferredScheme,
    pub definition: Definition,
}

#[derive(Clone, Debug)]
pub enum Definition {
    External(Symbol),
    Body(Vec<Clause>),
}

#[derive(Clone, Debug)]
pub struct Clause {
    pub span: Span,
    pub signature: Signature,
    pub bounds: Vec<InferredBound>,
    pub patterns: Vec<Pattern>,
    pub guard: Option<Expr>,
    pub body: Body,
    pub locals: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub parameters: Vec<InferredType>,
    pub result: InferredType,
}

pub type Pattern = h::Pattern<Infallible>;

/// One arm; see [`crate::hir::Arm`].
#[derive(Clone, Debug)]
pub struct Arm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Body {
    pub bindings: Vec<Binding>,
    pub result: Expr,
}

#[derive(Clone, Debug)]
pub struct Binding {
    pub pattern: Pattern,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub site: SiteId,
    pub span: Span,
    pub ty: InferredType,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum Target {
    Direct(Symbol),
    /// Through a `where` bound, met at each specialization by `owner`'s
    /// member. A `bare` one, named with no call, is `owner`'s field where it
    /// has one.
    Bound {
        owner: InferredType,
        member: Symbol,
        bare: bool,
    },
}

#[derive(Clone, Debug)]
pub struct Numeral {
    pub magnitude: num_bigint::BigUint,
    pub negative: bool,
    pub scale: Option<u32>,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Local(LocalId),
    Function(Symbol),
    Constructor(Symbol),
    Construct(Symbol, Vec<Expr>),
    Literal(LiteralExpr),
    Numeral(Numeral),
    Record(Vec<(Symbol, Expr)>),
    Update(Box<Expr>, Vec<(Symbol, Expr)>),
    Tuple(Vec<Expr>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    /// Arguments include the receiver, when there is one.
    Method(Target, Vec<Expr>),
    Project(Box<Expr>, Symbol),
    Widen(Box<Expr>),
    Try(Box<Expr>),
    /// `return value`; see [`crate::hir::ExprKind::Return`].
    Return(Box<Expr>),
    /// `if condition then yes else no`; see [`crate::hir::ExprKind::If`].
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`; see [`crate::hir::ExprKind::Is`].
    Is(Box<Expr>, Pattern),
    /// `value is ( arms )`; see [`crate::hir::ExprKind::Match`].
    Match(Box<Expr>, Vec<Arm>),
    /// Bindings, then the answer; see [`crate::hir::ExprKind::Block`].
    Block(Box<Body>),
    /// A loop; see [`crate::hir::Loop`].
    Loop(Box<Loop>),
    /// `continue`; see [`crate::hir::ExprKind::Continue`].
    Continue(Vec<Expr>),
    /// `break`; see [`crate::hir::ExprKind::Break`].
    Break(Vec<Expr>),
}

/// A loop; see [`crate::hir::Loop`].
#[derive(Clone, Debug)]
pub struct Loop {
    pub carried: Vec<(Expr, LocalId, LocalId)>,
    pub head: LoopHead,
    pub body: Body,
    pub rest: Body,
}

/// What a loop runs over; see [`crate::hir::LoopHead`].
#[derive(Clone, Debug)]
pub enum LoopHead {
    While(Expr),
    For(Pattern, Expr),
}
