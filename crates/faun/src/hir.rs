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

/// One requirement in a `where` clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    /// A member every type `variable` stands for must have: a method whose
    /// first parameter is the receiver, or a value, a function of none.
    Member {
        variable: Symbol,
        member: Symbol,
        ty: Type,
    },
    Alias {
        name: Symbol,
        arguments: Vec<Type>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Named(Symbol, Vec<Self>),
    Variable(Symbol),
    Function(Vec<Self>, Box<Self>),
    /// A closed tag row, each tag named by its spelling.
    Variants(Vec<ConstructorDecl>),
    /// A record's fields, and whether it is open: `{x: T *}` has at least
    /// `x`, and whatever else a caller's record does.
    Record(Vec<(Symbol, Self)>, bool),
    /// A positional product of two or more, which never passes for a record.
    Tuple(Vec<Self>),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

impl LocalId {
    #[must_use]
    pub(crate) fn index(self) -> usize {
        usize::try_from(self.0).expect("u32 fits usize")
    }
}

/// Where a constructor word was written whose meaning its position decides,
/// numbered across the program so checking can say which it chose.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SiteId(pub u32);

/// A capitalised word some visible declaration claims. It may name any of
/// `candidates`, or the structural tag it spells; which is its position's
/// type to decide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dual {
    pub site: SiteId,
    pub spelling: Symbol,
    pub candidates: Vec<Symbol>,
    /// Inside a type's block, the constructor that type declares with this
    /// word, which is the only declared one the word may read as there.
    pub home: Option<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Wild,
    Bind(LocalId),
    Constructor(Symbol, Vec<Self>),
    /// A structural tag, named by its spelling: it belongs to no declaration,
    /// and the scrutinee is a tag row that holds it.
    Tag(Symbol, Vec<Self>),
    /// A word a declaration claims, whose reading the scrutinee's type
    /// decides.
    Dual(Dual, Vec<Self>),
    Number {
        magnitude: BigUint,
        negative: bool,
    },
    Range(BigUint, BigUint),
    List(Vec<Self>, Option<Box<Self>>),
    /// Named fields, and whether the pattern ignores the others.
    Record(Vec<(Symbol, Self)>, bool),
    Tuple(Vec<Self>),
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
    /// A structural tag, named by its spelling. Applied, it carries fields;
    /// alone, it is a tag with none.
    Tag(Symbol),
    /// `a.zero`: the member a `where` bound on type variable `a` names,
    /// where `a` is spelled as the signature spells it.
    Associated(Symbol, Symbol),
    /// A word a declaration claims, whose reading its position decides.
    Dual(Dual),
    Number(BigUint),
    String(Vec<StringPart>),
    List(Vec<Expr>, Option<Box<Expr>>),
    Record(Vec<(Symbol, Expr)>),
    /// A record's fields replaced: the record, and the new values.
    Update(Box<Expr>, Vec<(Symbol, Expr)>),
    Tuple(Vec<Expr>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Symbol),
    Method(Box<Expr>, Symbol, Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// `value?`: an `Ok`'s value, or the `Err` answered at once by the
    /// clause or lambda it is written in.
    Try(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    Text(Vec<u8>),
    Splice(Expr),
}
