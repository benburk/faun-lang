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
    /// The definitions this module's `expect`s became, in the order written:
    /// each is among `items`, answering a `Bool`, with a name no source can
    /// write.
    pub expectations: Vec<Symbol>,
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

/// One end of a range pattern: a magnitude, negated or not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bound {
    pub magnitude: BigUint,
    pub negative: bool,
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
    /// `lo..hi`, inclusive, either end open where it is `None`.
    Range(Option<Bound>, Option<Bound>),
    List(Vec<Self>, Option<Box<Self>>),
    /// Named fields, and whether the pattern ignores the others.
    Record(Vec<(Symbol, Self)>, bool),
    Tuple(Vec<Self>),
    /// A string's bytes, matched by `Str.equals`: a test, never a shape.
    String(Vec<u8>),
    /// Either of two or more alternatives, each binding the same locals.
    /// Only a clause's parameters hold one.
    Or(Vec<Self>),
}

impl Pattern {
    /// The rows `patterns` stand for: one for each way of choosing an
    /// alternative of every `|` in them, in the order written. Without one,
    /// that is `patterns` alone.
    #[must_use]
    pub fn rows(patterns: &[Self]) -> Vec<Vec<Self>> {
        product(patterns.iter().map(Self::choices).collect())
    }

    /// Whether an `|` is anywhere in this pattern.
    #[must_use]
    pub fn has_alternatives(&self) -> bool {
        match self {
            Self::Or(_) => true,
            Self::Constructor(_, fields)
            | Self::Tag(_, fields)
            | Self::Dual(_, fields)
            | Self::Tuple(fields) => fields.iter().any(Self::has_alternatives),
            Self::List(elements, rest) => {
                elements.iter().any(Self::has_alternatives)
                    || rest.as_deref().is_some_and(Self::has_alternatives)
            }
            Self::Record(fields, _) => fields.iter().any(|(_, field)| field.has_alternatives()),
            Self::Wild
            | Self::Bind(_)
            | Self::Number { .. }
            | Self::Range(..)
            | Self::String(_) => false,
        }
    }

    /// This pattern once for each way of choosing an alternative of every
    /// `|` in it, and so once alone where there is none.
    #[must_use]
    pub fn choices(&self) -> Vec<Self> {
        match self {
            Self::Or(alternatives) => alternatives.iter().flat_map(Self::choices).collect(),
            Self::Constructor(constructor, fields) => Self::rows(fields)
                .into_iter()
                .map(|fields| Self::Constructor(*constructor, fields))
                .collect(),
            Self::Tag(label, fields) => Self::rows(fields)
                .into_iter()
                .map(|fields| Self::Tag(*label, fields))
                .collect(),
            Self::Dual(dual, fields) => Self::rows(fields)
                .into_iter()
                .map(|fields| Self::Dual(dual.clone(), fields))
                .collect(),
            Self::Tuple(members) => Self::rows(members).into_iter().map(Self::Tuple).collect(),
            Self::List(elements, rest) => list_choices(elements, rest.as_deref()),
            Self::Record(fields, open) => {
                let patterns: Vec<Self> = fields.iter().map(|(_, field)| field.clone()).collect();
                Self::rows(&patterns)
                    .into_iter()
                    .map(|row| {
                        let named = fields.iter().map(|(name, _)| *name).zip(row).collect();
                        Self::Record(named, *open)
                    })
                    .collect()
            }
            Self::Wild
            | Self::Bind(_)
            | Self::Number { .. }
            | Self::Range(..)
            | Self::String(_) => vec![self.clone()],
        }
    }
}

/// [`Pattern::choices`] of a list pattern: its elements' rows, each with each
/// choice of its rest.
fn list_choices(elements: &[Pattern], rest: Option<&Pattern>) -> Vec<Pattern> {
    let rests: Vec<Option<Pattern>> = rest.map_or_else(
        || vec![None],
        |rest| rest.choices().into_iter().map(Some).collect(),
    );
    Pattern::rows(elements)
        .into_iter()
        .flat_map(|row| {
            rests
                .iter()
                .map(move |rest| Pattern::List(row.clone(), rest.clone().map(Box::new)))
        })
        .collect()
}

/// Every row taking one choice from each column, the first column varying
/// slowest.
fn product(columns: Vec<Vec<Pattern>>) -> Vec<Vec<Pattern>> {
    columns.into_iter().fold(vec![Vec::new()], |rows, column| {
        rows.iter()
            .flat_map(|row| {
                column.iter().map(move |choice| {
                    let mut row = row.clone();
                    row.push(choice.clone());
                    row
                })
            })
            .collect()
    })
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
    /// A decimal numeral, `digits / 10^scale`, which only a float is.
    Decimal(BigUint, u32),
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
