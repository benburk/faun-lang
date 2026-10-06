//! Name-resolved frontend representation.
//!
//! Every global identity is an interned [`Symbol`], and each local is a compact
//! index scoped to one clause. Source spellings and module visibility no longer
//! need to be consulted after this boundary. [`SiteId`] identifies written and
//! generated occurrences independently of their diagnostic spans.

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
        /// The alias of one parameter whose application at `variable`
        /// required it, outermost, where one did: what a signature writes
        /// to require it again, `Hasher(h)`.
        through: Option<Symbol>,
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
    /// A record's fields, and whether it is open: `{x: T, *}` has at least
    /// `x`, and whatever else a caller's record does.
    Record(Vec<(Symbol, Self)>, bool),
    /// A positional product of two or more, which never passes for a record.
    Tuple(Vec<Self>),
    /// Whatever the clauses of the signed function make it.
    Hole,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub site: SiteId,
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

/// Identify an expression, clause, or ambiguous constructor occurrence within
/// its resolved program.
///
/// Spans locate diagnostics; they do not identify nodes.
/// Cloning an occurrence preserves its identity; new occurrences need fresh IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SiteId(pub u32);

/// Allocate identities for written and generated HIR in one program.
#[derive(Clone, Debug, Default)]
pub(crate) struct Sites(u32);

impl Sites {
    pub(crate) const fn fresh(&mut self) -> SiteId {
        let site = SiteId(self.0);
        self.0 = self.0.checked_add(1).expect("fewer than 2^32 HIR sites");
        site
    }

    pub(crate) const fn expr(&mut self, span: Span, kind: ExprKind) -> Expr {
        Expr {
            site: self.fresh(),
            span,
            kind,
        }
    }
}

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
pub enum Pattern<D = Dual> {
    Wild,
    Bind(LocalId),
    Constructor(Symbol, Vec<Self>),
    /// A structural tag, named by its spelling: it belongs to no declaration,
    /// and the scrutinee is a tag row that holds it.
    Tag(Symbol, Vec<Self>),
    /// A word a declaration claims, whose reading the scrutinee's type
    /// decides.
    Dual(D, Vec<Self>),
    Number {
        magnitude: BigUint,
        negative: bool,
    },
    /// `lo..hi`, inclusive, either end open where it is `None`.
    Range(Option<Bound>, Option<Bound>),
    List(Vec<Self>, Option<Box<Self>>),
    /// A list ending in the elements of the second, what comes before them
    /// matched by the first: a list's rest, `[*front, last]`.
    Ending(Box<Self>, Vec<Self>),
    /// Named fields, and whether the pattern ignores the others.
    Record(Vec<(Symbol, Self)>, bool),
    Tuple(Vec<Self>),
    /// A string's bytes, matched by `Str.equals`: a test, never a shape.
    String(Vec<u8>),
    /// Either of two or more alternatives, each binding the same locals.
    /// Only a clause's parameters hold one.
    Or(Vec<Self>),
    /// `name is pattern`: the whole value bound, and taken apart.
    As(LocalId, Box<Self>),
}

impl<D: Clone> Pattern<D> {
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
            Self::Ending(front, last) => {
                front.has_alternatives() || last.iter().any(Self::has_alternatives)
            }
            Self::Record(fields, _) => fields.iter().any(|(_, field)| field.has_alternatives()),
            Self::As(_, pattern) => pattern.has_alternatives(),
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
            Self::As(local, pattern) => pattern
                .choices()
                .into_iter()
                .map(|pattern| Self::As(*local, Box::new(pattern)))
                .collect(),
            Self::List(elements, rest) => list_choices(elements, rest.as_deref()),
            Self::Ending(front, last) => ending_choices(front, last),
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
fn list_choices<D: Clone>(elements: &[Pattern<D>], rest: Option<&Pattern<D>>) -> Vec<Pattern<D>> {
    let rests: Vec<Option<Pattern<D>>> = rest.map_or_else(
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

/// [`Pattern::choices`] of a list's end: each choice of its front, with its
/// last elements' rows.
fn ending_choices<D: Clone>(front: &Pattern<D>, last: &[Pattern<D>]) -> Vec<Pattern<D>> {
    let rows = Pattern::rows(last);
    front
        .choices()
        .into_iter()
        .flat_map(|front| {
            rows.iter()
                .map(move |row| Pattern::Ending(Box::new(front.clone()), row.clone()))
        })
        .collect()
}

/// Every row taking one choice from each column, the first column varying
/// slowest.
fn product<D: Clone>(columns: Vec<Vec<Pattern<D>>>) -> Vec<Vec<Pattern<D>>> {
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
    pub site: SiteId,
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
    /// `if condition then yes else no`: the branch the condition chooses.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`: whether it matches. What the pattern binds is
    /// seen where resolution scoped it: along an `&` chain, and in the
    /// `then` branch of an `if` whose condition this is part of.
    Is(Box<Expr>, Pattern),
    /// Bindings, then the answer: a block written inside an expression.
    /// Its locals are the clause's, numbered apart from every other.
    Block(Box<Body>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    Text(Vec<u8>),
    /// A string-valued expression, including the generated `to_str` call.
    Splice(Expr),
}
