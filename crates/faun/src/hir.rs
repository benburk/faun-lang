//! Name-resolved frontend representation.
//!
//! Every global identity is an interned [`Symbol`], and each local is a compact
//! index scoped to one clause. Source spellings and module visibility no longer
//! need to be consulted after this boundary. [`SiteId`] identifies written and
//! generated occurrences independently of their diagnostic spans.

use std::collections::HashSet;
use std::convert::Infallible;

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
    /// Where the result's type is written, where a signature writes it.
    pub result_span: Option<Span>,
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
    /// Each local a name bound again in a branch is after it, which every
    /// branch going on binds, and the name: checking holds the branches to
    /// one type there.
    pub merged: Vec<(LocalId, Symbol)>,
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
pub(crate) struct Sites {
    next: u32,
    /// The `to_str` calls splices were written as. Each is a splice's text:
    /// the value itself where specialization finds it a `Str`.
    spliced: HashSet<SiteId>,
}

impl Sites {
    pub(crate) const fn fresh(&mut self) -> SiteId {
        let site = SiteId(self.next);
        self.next = self.next.checked_add(1).expect("fewer than 2^32 HIR sites");
        site
    }

    /// Mark `site`, a `to_str` call, as a written splice's text.
    pub(crate) fn splice(&mut self, site: SiteId) {
        self.spliced.insert(site);
    }

    /// Whether `site` is a written splice's text.
    pub(crate) fn is_spliced(&self, site: SiteId) -> bool {
        self.spliced.contains(&site)
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
    /// Whether it was written as a character literal.
    pub character: bool,
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
        /// Whether it was written as a character literal.
        character: bool,
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

    /// Each pattern directly inside this one, in the order written; an
    /// `|`'s are its alternatives.
    pub fn parts(&self) -> impl Iterator<Item = &Self> {
        let (before, list, fields, after): (_, &[Self], &[(Symbol, Self)], _) = match self {
            Self::Constructor(_, parts)
            | Self::Tag(_, parts)
            | Self::Dual(_, parts)
            | Self::Tuple(parts)
            | Self::Or(parts) => (None, parts, &[], None),
            Self::List(elements, rest) => (None, elements, &[], rest.as_deref()),
            Self::Ending(front, last) => (Some(&**front), last, &[], None),
            Self::Record(fields, _) => (None, &[], fields, None),
            Self::As(_, inner) => (Some(&**inner), &[], &[], None),
            Self::Wild
            | Self::Bind(_)
            | Self::Number { .. }
            | Self::Range(..)
            | Self::String(_) => (None, &[], &[], None),
        };
        let fields = fields.iter().map(|(_, field)| field);
        before.into_iter().chain(list).chain(fields).chain(after)
    }

    /// Whether an `|` is anywhere in this pattern.
    #[must_use]
    pub fn has_alternatives(&self) -> bool {
        matches!(self, Self::Or(_)) || self.parts().any(Self::has_alternatives)
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

/// One way a `value is ( arms )` goes: its guard asks the equalities its
/// pattern does first, as a clause's does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub bindings: Vec<Binding>,
    pub result: Expr,
}

impl Body {
    /// Each line's value, then the answer.
    pub(crate) fn exprs(&self) -> impl Iterator<Item = &Expr> {
        let values = self.bindings.iter().map(|binding| &binding.value);
        values.chain([&self.result])
    }

    /// [`Self::exprs`], each changeable.
    pub(crate) fn exprs_mut(&mut self) -> impl Iterator<Item = &mut Expr> {
        let values = self.bindings.iter_mut().map(|binding| &mut binding.value);
        values.chain([&mut self.result])
    }
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

impl Expr {
    /// Visit each expression directly inside this one, in the order it is
    /// worked out. A walk matches the forms it has something to say of and
    /// leaves the rest to this.
    pub(crate) fn for_each_child<'a>(&'a self, mut visit: impl FnMut(&'a Self)) {
        let visited: Result<(), Infallible> = self.try_for_each_child(|child| {
            visit(child);
            Ok(())
        });
        let Ok(()) = visited;
    }

    /// The same, stopping at the first child `visit` refuses.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per expression form, so a new form must say what is inside it"
    )]
    pub(crate) fn try_for_each_child<'a, E>(
        &'a self,
        mut visit: impl FnMut(&'a Self) -> Result<(), E>,
    ) -> Result<(), E> {
        match &self.kind {
            ExprKind::Local(_)
            | ExprKind::Global(_)
            | ExprKind::Constructor(_)
            | ExprKind::Tag(_)
            | ExprKind::Associated(..)
            | ExprKind::Dual(_)
            | ExprKind::Number(_)
            | ExprKind::Character(_)
            | ExprKind::Decimal(..) => Ok(()),
            ExprKind::String(parts) => parts.iter().try_for_each(|part| match part {
                StringPart::Text(_) => Ok(()),
                StringPart::Splice(inner) => visit(inner),
            }),
            ExprKind::List(elements, rest) => {
                elements.iter().chain(rest.as_deref()).try_for_each(visit)
            }
            ExprKind::Record(fields) => fields.iter().try_for_each(|(_, value)| visit(value)),
            ExprKind::Update(base, fields) => {
                visit(base)?;
                fields.iter().try_for_each(|(_, value)| visit(value))
            }
            ExprKind::Tuple(members) | ExprKind::Continue(members) | ExprKind::Break(members) => {
                members.iter().try_for_each(visit)
            }
            ExprKind::Lambda(_, inner)
            | ExprKind::Member(inner, _)
            | ExprKind::Unary(_, inner)
            | ExprKind::Try(inner)
            | ExprKind::Return(inner)
            | ExprKind::Is(inner, _) => visit(inner),
            ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
                visit(head)?;
                arguments.iter().try_for_each(visit)
            }
            ExprKind::Binary(_, left, right) => {
                visit(left)?;
                visit(right)
            }
            ExprKind::If(condition, yes, no) => {
                visit(condition)?;
                visit(yes)?;
                visit(no)
            }
            ExprKind::Match(value, arms) => {
                visit(value)?;
                arms.iter().try_for_each(|arm| {
                    arm.guard.iter().chain([&arm.body]).try_for_each(&mut visit)
                })
            }
            ExprKind::Block(body) => body.exprs().try_for_each(visit),
            ExprKind::Loop(looped) => {
                for (initial, _, _) in &looped.carried {
                    visit(initial)?;
                }
                visit(looped.head.value())?;
                looped.body.exprs().try_for_each(&mut visit)?;
                looped.rest.exprs().try_for_each(visit)
            }
        }
    }

    /// [`Self::for_each_child`], each child changeable.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per expression form, so a new form must say what is inside it"
    )]
    pub(crate) fn for_each_child_mut(&mut self, mut visit: impl FnMut(&mut Self)) {
        match &mut self.kind {
            ExprKind::Local(_)
            | ExprKind::Global(_)
            | ExprKind::Constructor(_)
            | ExprKind::Tag(_)
            | ExprKind::Associated(..)
            | ExprKind::Dual(_)
            | ExprKind::Number(_)
            | ExprKind::Character(_)
            | ExprKind::Decimal(..) => {}
            ExprKind::String(parts) => {
                for part in parts {
                    if let StringPart::Splice(inner) = part {
                        visit(inner);
                    }
                }
            }
            ExprKind::List(elements, rest) => {
                elements
                    .iter_mut()
                    .chain(rest.as_deref_mut())
                    .for_each(visit);
            }
            ExprKind::Record(fields) => {
                for (_, value) in fields.iter_mut() {
                    visit(value);
                }
            }
            ExprKind::Update(base, fields) => {
                visit(base);
                for (_, value) in fields.iter_mut() {
                    visit(value);
                }
            }
            ExprKind::Tuple(members) | ExprKind::Continue(members) | ExprKind::Break(members) => {
                members.iter_mut().for_each(visit);
            }
            ExprKind::Lambda(_, inner)
            | ExprKind::Member(inner, _)
            | ExprKind::Unary(_, inner)
            | ExprKind::Try(inner)
            | ExprKind::Return(inner)
            | ExprKind::Is(inner, _) => visit(inner),
            ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
                visit(head);
                arguments.iter_mut().for_each(visit);
            }
            ExprKind::Binary(_, left, right) => {
                visit(left);
                visit(right);
            }
            ExprKind::If(condition, yes, no) => {
                visit(condition);
                visit(yes);
                visit(no);
            }
            ExprKind::Match(value, arms) => {
                visit(value);
                for arm in arms {
                    arm.guard
                        .iter_mut()
                        .chain([&mut arm.body])
                        .for_each(&mut visit);
                }
            }
            ExprKind::Block(body) => body.exprs_mut().for_each(visit),
            ExprKind::Loop(looped) => {
                for (initial, _, _) in &mut looped.carried {
                    visit(initial);
                }
                visit(looped.head.value_mut());
                looped.body.exprs_mut().for_each(&mut visit);
                looped.rest.exprs_mut().for_each(visit);
            }
        }
    }
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
    /// A character literal, a numeral of its scalar value.
    Character(char),
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
    /// `return value`, after a line's `else`: the clause's or lambda's
    /// answer, at once.
    Return(Box<Expr>),
    /// `if condition then yes else no`: the branch the condition chooses.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`: whether it matches. What the pattern binds is
    /// seen where resolution scoped it: along an `&` chain, and in the
    /// `then` branch of an `if` whose condition this is part of.
    Is(Box<Expr>, Pattern),
    /// `value is ( arms )`: the first arm that matches answers. What an
    /// arm's pattern binds is seen by its guard and its body.
    Match(Box<Expr>, Vec<Arm>),
    /// Bindings, then the answer: a block written inside an expression.
    /// Its locals are the clause's, numbered apart from every other.
    Block(Box<Body>),
    /// A loop, holding the lines after it; see [`Loop`].
    Loop(Box<Loop>),
    /// `continue`: the next round, each name the loop carries as it is
    /// here, in the loop's order.
    Continue(Vec<Expr>),
    /// `break`: out of the loop, each name the loop carries as it is here.
    Break(Vec<Expr>),
}

/// `while condition ( body )` or `for pattern in list ( body )`, and the
/// lines after it, `rest`, which go on once it ends.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loop {
    /// Each name bound before the loop and again in its body: its value
    /// going in, the local it is within a round, and the one it is after
    /// the loop.
    pub carried: Vec<(Expr, LocalId, LocalId)>,
    pub head: LoopHead,
    /// The round, its answer a `continue`, or a leave, on every way through.
    pub body: Body,
    pub rest: Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoopHead {
    /// While the condition holds, what it binds seen by the round.
    While(Expr),
    /// Once for each element of the list, the pattern binding it.
    For(Pattern, Expr),
}

impl LoopHead {
    /// What the head works out: the condition, or the list.
    pub(crate) const fn value(&self) -> &Expr {
        match self {
            Self::While(value) | Self::For(_, value) => value,
        }
    }

    pub(crate) const fn value_mut(&mut self) -> &mut Expr {
        match self {
            Self::While(value) | Self::For(_, value) => value,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    Text(Vec<u8>),
    /// A string-valued expression, including the generated `to_str` call.
    Splice(Expr),
}
