//! Name-resolved frontend representation.
//!
//! Every global identity is an interned [`Symbol`], and each local is a compact
//! index scoped to one clause. Source spellings and module visibility no longer
//! need to be consulted after this boundary.

use num_bigint::BigUint;

use super::ast::{BinaryOp, Span, UnaryOp};
use super::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub source: ModuleId,
    /// Canonical method definitions reachable through this module's scope.
    pub visible_methods: Vec<Symbol>,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Data(DataDecl),
    Signature(SignatureDecl),
    Clause(Clause),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl {
    pub span: Span,
    pub name: Symbol,
    pub parameters: Vec<Symbol>,
    pub constructors: Vec<ConstructorDecl>,
    pub wrapper: Option<WrapperDecl>,
    pub methods: Vec<MethodItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapperDecl {
    pub constructor: Symbol,
    pub field: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: Symbol,
    pub fields: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MethodItem {
    Signature(SignatureDecl),
    Clause(Clause),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureDecl {
    pub span: Span,
    pub name: Symbol,
    /// The source-level spelling, retained for method lookup and diagnostics.
    pub spelling: Symbol,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub constraints: Vec<Constraint>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
    pub name: Symbol,
    pub arguments: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Named(Symbol, Vec<Self>),
    Variable(Symbol),
    Function(Vec<Self>, Box<Self>),
    Variants(Vec<ConstructorDecl>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub span: Span,
    pub name: Symbol,
    pub patterns: Vec<Pattern>,
    pub guard: Option<Expr>,
    pub body: Body,
    pub locals: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);

impl LocalId {
    #[must_use]
    pub(crate) fn index(self) -> usize {
        usize::try_from(self.0).expect("u32 fits usize")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Wild,
    Bind(LocalId),
    Constructor(Symbol, Vec<Self>),
    Number { magnitude: BigUint, negative: bool },
    Range(BigUint, BigUint),
    List(Vec<Self>, Option<Box<Self>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub bindings: Vec<Binding>,
    pub result: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub pattern: Pattern,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Local(LocalId),
    Global(Symbol),
    Constructor(Symbol),
    Number(BigUint),
    String(Vec<StringPart>),
    List(Vec<Expr>, Option<Box<Expr>>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Symbol),
    Method(Box<Expr>, Symbol, Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    Text(Vec<u8>),
    Splice(Expr),
}
