//! Polymorphic type inference and receiver-directed method resolution.
//!
//! Explicit signatures are universally quantified. Unsigned definitions use
//! Algorithm W over call-graph components, keeping recursive groups
//! monomorphic until the whole group has been checked. Method calls are held
//! until ordinary unification (and numeral defaulting) identifies a receiver.
//! Bodyless-method derivation is deliberately outside this pass.
//!
//! Tag rows unify as Rémy's rows: shared tags unify their fields and an open
//! side's tail takes what only the other holds. A signature's result rows get
//! a tail its scheme quantifies; skolemized for the body, that tail is rigid,
//! so the body answers only the written tags and callers may widen them. A
//! closed row answered where such a row is wanted is subsumed, and the
//! expression is recorded as widened. Clauses taking a row apart without a
//! catch-all close it. A word a declaration claims waits, as a method does,
//! for its position's type to choose between the tag and the constructor.
//!
//! `where` bounds are structural. A signed body meets its written bounds at
//! its rigid variables; a use of a bounded definition owes its bounds, met
//! where the use's types are known or owed in turn. An unsigned component's
//! methods still open on a variable it generalizes become its bounds, as do
//! its numerals of a generic type, through `of_nat`. Specialization calls
//! each concrete type's own member.

#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::blessed::{self, LiteralExpr, NumeralType, PreludeIds};
use super::diagnostic::Diagnostic;
use super::hir as h;
use super::resolve::ResolvedProgram;
use super::{ModuleId, Symbol, Symbols};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub ty: Symbol,
    pub value: LiteralExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub target: Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub field: Symbol,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeVariable {
    index: u32,
    rigid: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InferredType {
    Variable(TypeVariable),
    Named(Symbol, Vec<Self>),
    Function(Vec<Self>, Box<Self>),
    /// A tag row: the tags it holds, and a variable standing for the tags a
    /// caller may add, where it is open.
    Variants(Vec<(Symbol, Vec<Self>)>, Option<Box<Self>>),
    /// A record's fields, and where it is open the rest of a caller's.
    Record(Vec<(Symbol, Self)>, Option<Box<Self>>),
    /// A positional product of two or more.
    Tuple(Vec<Self>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredScheme {
    pub variables: Vec<TypeVariable>,
    pub ty: InferredType,
    /// What every type the variables stand for must have.
    pub bounds: Vec<InferredBound>,
}

/// A `where` bound, written or inferred: every type `owner` stands for has
/// `member`, at `ty`. A method's type takes the owner first; a value's, as
/// `a.zero : a` is, is a function of nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredBound {
    pub owner: InferredType,
    pub member: Symbol,
    pub ty: InferredType,
    /// Reached through the type rather than as a method of a value.
    pub associated: bool,
}

/// A call through a bound: the concrete type `owner` stands for at a
/// specialization says whose `member` it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub owner: InferredType,
    pub member: Symbol,
}

/// A numeral whose type a definition leaves generic, built through its
/// type's `of_nat` at each specialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredNumeral {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub magnitude: num_bigint::BigUint,
    pub negative: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub ty: InferredType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClauseSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub ty: InferredType,
    /// The bounds of the definition, over this clause's type variables.
    pub bounds: Vec<InferredBound>,
}

/// A resolved program with what checking learned about it.
#[derive(Clone, Debug)]
pub struct CheckedProgram {
    pub resolved: ResolvedProgram,
    /// The standard identities its literals and patterns were checked against.
    pub prelude: PreludeIds,
    pub types: Types,
}

/// Which reading a word some declaration claims took, by its site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    /// The declared constructor its position demanded, or its one declared
    /// reading, where nothing decided.
    Constructor(Symbol),
    /// The structural tag it spells, where its position is a tag row.
    Tag(Symbol),
}

/// The types checking inferred for a program's HIR, by site.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Types {
    /// Principal schemes for signed and inferred global values.
    pub values: HashMap<Symbol, InferredScheme>,
    /// Instantiated types for every expression occurrence.
    pub expressions: Vec<ExpressionSite>,
    /// The function type used while checking each clause.
    pub clauses: Vec<ClauseSite>,
    pub literals: Vec<LiteralSite>,
    pub methods: Vec<MethodSite>,
    pub projections: Vec<ProjectionSite>,
    /// Expressions whose value a signed definition answers with, and the
    /// wider type it is answered as: a closed tag row standing where the
    /// signature's row is one a caller may widen.
    pub widenings: Vec<ExpressionSite>,
    /// Which reading each word a declaration claims took.
    pub readings: HashMap<h::SiteId, Reading>,
    /// Calls through `where` bounds.
    pub bound_sites: Vec<BoundSite>,
    /// Numerals of a generic type.
    pub deferred_numerals: Vec<DeferredNumeral>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub message: String,
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CheckError {}

/// Infer every definition, check declared signatures, resolve methods, and
/// elaborate literals.
///
/// Type variables in signatures are universally quantified at each use.
/// Unsigned recursive groups are inferred monomorphically and generalized only
/// after the group closes. `where` constraints are rejected until bounded
/// polymorphism has a representation in checked HIR.
///
/// # Errors
///
/// Reports type, arity, ambiguous-method, unsupported-constraint, and literal
/// protocol failures, and clauses that leave a case unmatched.
pub fn type_check(
    resolved: ResolvedProgram,
    prelude: PreludeIds,
) -> Result<CheckedProgram, Diagnostic> {
    let types = validate_effects(&resolved.program, &resolved.symbols).and_then(|()| {
        let types = Checker::new(&resolved.program, &resolved.symbols, &prelude)?
            .check(&resolved.program)?;
        crate::exhaustive::exhaustive(&resolved.program, &resolved.symbols, &prelude, &types)?;
        Ok(types)
    });
    match types {
        Ok(types) => Ok(CheckedProgram {
            resolved,
            prelude,
            types,
        }),
        Err(error) => Err(resolved.diagnostic(error.module, error.span, error.message)),
    }
}

/// Validate the selected host ABI and the application's `main!` signature.
///
/// # Errors
///
/// Rejects host declarations or an entry whose checked type differs from the
/// canonical `Host` and `Nat` identities or the structural empty variant type.
pub fn check_application_abi(
    checked: &CheckedProgram,
    host: &crate::host::HostIds,
    main: &crate::host::Main,
) -> Result<(), Diagnostic> {
    let resolved = &checked.resolved;
    let failure = |module, span, message: &str| resolved.diagnostic(module, span, message.into());
    let module = main.module;
    let span = resolved
        .program
        .modules
        .iter()
        .flat_map(|module| &module.items)
        .find_map(|item| match item {
            h::Item::Signature(signature) if signature.name == main.symbol => Some(signature.span),
            h::Item::Clause(clause) if clause.name == main.symbol => Some(clause.span),
            _ => None,
        })
        .unwrap_or_default();
    // `Host` wraps the record of startup values its target produces. Which
    // fields a target can produce is the target's to say, when lowering.
    let carries = resolved
        .program
        .modules
        .iter()
        .flat_map(|module| &module.items)
        .find_map(|item| match item {
            h::Item::Data(data) if data.name == host.host => data.wrapper.as_ref(),
            _ => None,
        });
    if !carries.is_some_and(|wrapper| matches!(wrapper.field, h::Type::Record(..))) {
        return Err(failure(
            module,
            span,
            "the application ABI requires `Host` to wrap a record of startup values",
        ));
    }

    for (name, expected, written) in [
        (
            main.symbol,
            InferredType::Function(
                vec![InferredType::Named(host.host, Vec::new())],
                Box::new(InferredType::Variants(Vec::new(), None)),
            ),
            "main! : Host -> []",
        ),
        (
            host.exit,
            InferredType::Function(
                vec![
                    InferredType::Named(host.host, Vec::new()),
                    InferredType::Named(checked.prelude.nat, Vec::new()),
                ],
                Box::new(InferredType::Variants(Vec::new(), None)),
            ),
            "exit! : Host Nat -> []",
        ),
    ] {
        let Some(scheme) = checked.types.values.get(&name) else {
            return Err(failure(
                module,
                span,
                &format!("the application ABI requires `{written}`"),
            ));
        };
        if !scheme.variables.is_empty() || scheme.ty != expected {
            return Err(failure(
                module,
                span,
                &format!("the application ABI requires `{written}`"),
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Var(u32),
    Rigid(u32),
    Named(Symbol, Vec<Self>),
    Function(Vec<Self>, Box<Self>),
    /// A tag row: the tags it holds, and where it is open, a tail standing
    /// for the rest. A tail is a variable, which unification may widen, or
    /// rigid: a signed definition's own result row, which its body may not
    /// widen and each caller may.
    Variants(Vec<(Symbol, Vec<Self>)>, Option<Box<Self>>),
    /// A record's fields, in one order, and where it is open, a tail
    /// standing for the fields a caller's record has besides.
    Record(Vec<(Symbol, Self)>, Option<Box<Self>>),
    /// A positional product of two or more, which never unifies with a
    /// record.
    Tuple(Vec<Self>),
}

/// The tags of a row, each with its fields.
type Tags = Vec<(Symbol, Vec<Ty>)>;

/// Which kind of row a row unification builds: a tag row, whose entries
/// are tags and their fields, or a record, whose entries are fields each
/// held as a one-type entry.
#[derive(Clone, Copy, Debug)]
enum Former {
    Tags,
    Fields,
}

impl Former {
    fn build(self, entries: Tags, tail: Option<Box<Ty>>) -> Ty {
        match self {
            Self::Tags => Ty::Variants(entries, tail),
            Self::Fields => Ty::Record(
                entries
                    .into_iter()
                    .map(|(name, mut held)| (name, held.remove(0)))
                    .collect(),
                tail,
            ),
        }
    }
}

/// A record's fields as row entries.
fn entries(fields: &[(Symbol, Ty)]) -> Tags {
    fields
        .iter()
        .map(|(name, ty)| (*name, vec![ty.clone()]))
        .collect()
}

/// Why two types do not unify.
#[derive(Clone, Debug)]
enum Mismatch {
    Reason(&'static str),
    /// One tag written with two numbers of fields.
    Fields(usize, usize),
    /// Tags a row holds that `row` -- closed, or a caller's to widen --
    /// cannot take.
    NotAmong {
        tags: Vec<Symbol>,
        row: Ty,
    },
}

impl Mismatch {
    fn describe(&self, symbols: &Symbols) -> String {
        match self {
            Self::Reason(reason) => (*reason).to_owned(),
            Self::Fields(one, other) => {
                format!("one tag is written with {one} and with {other} fields")
            }
            Self::NotAmong {
                tags: fields,
                row: row @ Ty::Record(..),
            } => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|field| format!("`{}`", symbols.text(*field)))
                    .collect();
                format!(
                    "the record `{}` has no field {}",
                    show(row, symbols),
                    fields.join(" or ")
                )
            }
            Self::NotAmong { tags, row } => {
                let tags: Vec<_> = tags
                    .iter()
                    .map(|tag| format!("`{}`", spelled(*tag, symbols)))
                    .collect();
                let (subject, verb) = if tags.len() == 1 {
                    (tags[0].clone(), "is")
                } else {
                    (tags.join(" and "), "are")
                };
                format!(
                    "{subject} {verb} not among the tags of `{}`, which admits no others",
                    show(row, symbols)
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Scheme {
    variables: Vec<u32>,
    ty: Ty,
}

#[derive(Clone, Debug)]
struct MethodImpl {
    owner: Symbol,
    target: Symbol,
    scheme: Scheme,
    /// Whether this is a bound of the definition being checked, which
    /// names no implementation until it is specialized.
    bound: bool,
}

/// A `where` bound over a definition's type variables; see
/// [`InferredBound`].
#[derive(Clone, Debug)]
struct Bound {
    owner: Ty,
    member: Symbol,
    ty: Ty,
    /// Whether the member is reached through the type, `a.zero()` or
    /// `a.of_nat(n)`, rather than as a method of a value of it, which is
    /// its type's first parameter.
    associated: bool,
}

impl Bound {
    fn substituted(&self, replacements: &HashMap<u32, Ty>) -> Self {
        Self {
            owner: substitute(&self.owner, replacements),
            member: self.member,
            ty: substitute(&self.ty, replacements),
            associated: self.associated,
        }
    }
}

/// How much a stretch of checking decides when it finishes.
#[derive(Clone, Copy)]
enum Finish<'t> {
    /// A binding: what the rest of its definition may decide waits for it.
    Binding,
    /// A signed clause, whose variables are rigid: everything is decided.
    Signed,
    /// An unsigned component about to be generalized, its definitions'
    /// types and names: what stays open on their variables becomes bounds.
    Unsigned(&'t [Ty], &'t HashSet<Symbol>),
}

#[derive(Clone, Debug)]
struct FieldImpl {
    owner: Symbol,
    scheme: Scheme,
}

#[derive(Clone, Debug)]
struct PendingMethod {
    module: ModuleId,
    span: super::ast::Span,
    name: Symbol,
    receiver: Ty,
    arguments: Vec<Ty>,
    result: Ty,
    reach: Reach,
    resolved: bool,
    /// A bound a use of a definition owes rather than a call written: it
    /// must be met, and names nothing where it stands.
    obligation: bool,
}

/// How a member is reached.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reach {
    /// Called on a value, `x.add(y)`.
    Called,
    /// Named on a value with no call, `x.name`: a field, or a method of no
    /// other arguments.
    Bare,
    /// Through the type, `a.zero()`: a value of the type rather than a
    /// method of one.
    Type,
}

/// A claimed word awaiting its position's decision. `fields` are what it is
/// applied to, where it is; `result` is its position's type.
#[derive(Clone, Debug)]
struct PendingTag {
    module: ModuleId,
    span: super::ast::Span,
    dual: h::Dual,
    fields: Option<Vec<Ty>>,
    /// Where each field was written, for a word applied in an expression:
    /// a field is a value flowing into the constructor, which may be widened
    /// there. A pattern's fields flow out, and have none.
    field_spans: Vec<super::ast::Span>,
    result: Ty,
    resolved: bool,
}

/// A tag written alone, awaiting whether its position wants a value or a
/// function building one.
#[derive(Clone, Debug)]
struct PendingBare {
    module: ModuleId,
    span: super::ast::Span,
    label: Symbol,
    ty: Ty,
    resolved: bool,
}

/// Patterns whose rows close once every word in them has its reading.
#[derive(Clone, Debug)]
struct PendingClosing {
    module: ModuleId,
    span: super::ast::Span,
    ty: Ty,
    rows: Vec<(h::Pattern, bool)>,
}

/// Where each pending list stood when a stretch of checking began, which
/// is the part of each that stretch settles.
#[derive(Clone, Copy, Debug)]
struct Marks {
    methods: usize,
    numerals: usize,
    tags: usize,
    closings: usize,
}

#[derive(Clone, Debug)]
struct PendingNumeral {
    module: ModuleId,
    span: super::ast::Span,
    magnitude: num_bigint::BigUint,
    negative: bool,
    ty: Ty,
    resolved: bool,
}

#[derive(Clone, Debug, Default)]
struct Infer {
    links: Vec<Option<Ty>>,
    next_rigid: u32,
}

impl Infer {
    fn fresh(&mut self) -> Ty {
        let id = u32::try_from(self.links.len()).expect("fewer than 2^32 inference variables");
        self.links.push(None);
        Ty::Var(id)
    }

    fn resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(id) => self.links[usize::try_from(*id).expect("u32 fits usize")]
                .as_ref()
                .map_or_else(|| ty.clone(), |link| self.resolve(link)),
            Ty::Rigid(_) => ty.clone(),
            Ty::Named(name, arguments) => {
                Ty::Named(*name, arguments.iter().map(|ty| self.resolve(ty)).collect())
            }
            Ty::Function(parameters, result) => Ty::Function(
                parameters.iter().map(|ty| self.resolve(ty)).collect(),
                Box::new(self.resolve(result)),
            ),
            // A row is resolved flat: a tail bound to a row gives up its
            // tags, so what comes back ends in an unbound tail or none.
            Ty::Variants(tags, tail) => {
                let mut tags: Tags = tags
                    .iter()
                    .map(|(name, fields)| {
                        (*name, fields.iter().map(|ty| self.resolve(ty)).collect())
                    })
                    .collect();
                let tail = match tail.as_deref().map(|tail| self.resolve(tail)) {
                    Some(Ty::Variants(more, rest)) => {
                        tags.extend(more);
                        rest
                    }
                    other => other.map(Box::new),
                };
                Ty::Variants(tags, tail)
            }
            Ty::Record(fields, tail) => {
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve(ty)))
                    .collect();
                let tail = match tail.as_deref().map(|tail| self.resolve(tail)) {
                    Some(Ty::Record(more, rest)) => {
                        fields.extend(more);
                        rest
                    }
                    other => other.map(Box::new),
                };
                fields.sort_by_key(|(name, _)| *name);
                Ty::Record(fields, tail)
            }
            Ty::Tuple(members) => Ty::Tuple(members.iter().map(|ty| self.resolve(ty)).collect()),
        }
    }

    fn unify(&mut self, left: &Ty, right: &Ty) -> Result<(), Mismatch> {
        let left = self.resolve(left);
        let right = self.resolve(right);
        match (&left, &right) {
            (Ty::Var(a), Ty::Var(b)) if a == b => Ok(()),
            (Ty::Rigid(a), Ty::Rigid(b)) if a == b => Ok(()),
            (Ty::Var(id), other) | (other, Ty::Var(id)) => {
                if contains(other, *id) {
                    Err(Mismatch::Reason("a type would contain itself"))
                } else {
                    self.links[usize::try_from(*id).expect("u32 fits usize")] = Some(other.clone());
                    Ok(())
                }
            }
            (Ty::Named(a, aa), Ty::Named(b, ba)) if a == b && aa.len() == ba.len() => {
                for (a, b) in aa.iter().zip(ba) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (Ty::Function(ap, ar), Ty::Function(bp, br)) if ap.len() == bp.len() => {
                for (a, b) in ap.iter().zip(bp) {
                    self.unify(a, b)?;
                }
                self.unify(ar, br)
            }
            (Ty::Variants(a, at), Ty::Variants(b, bt)) => {
                self.unify_rows(Former::Tags, (a, at.as_deref()), (b, bt.as_deref()))
            }
            (Ty::Record(a, at), Ty::Record(b, bt)) => self.unify_rows(
                Former::Fields,
                (&entries(a), at.as_deref()),
                (&entries(b), bt.as_deref()),
            ),
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            _ => Err(Mismatch::Reason("incompatible types")),
        }
    }

    /// Unify what a body answers with what its signature says it answers,
    /// except that a closed tag row may stand where the signature's row is
    /// one a caller may widen, if it holds none of the caller's tags. That
    /// takes a widening where the value is answered, which this says.
    ///
    /// Unification alone would refuse `f : [A] -> [A]` written `f(x) -> x`:
    /// the parameter is closed, and the result's rest is the caller's.
    fn subsume(&mut self, actual: &Ty, expected: &Ty) -> Result<bool, Mismatch> {
        let actual = self.resolve(actual);
        let expected = self.resolve(expected);
        match (&actual, &expected) {
            (Ty::Named(a, aa), Ty::Named(b, ba)) if a == b && aa.len() == ba.len() => {
                let mut widened = false;
                for (a, b) in aa.iter().zip(ba) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                let mut widened = false;
                for (a, b) in a.iter().zip(b) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Record(a, a_tail), Ty::Record(b, b_tail)) => {
                let mut widened = false;
                for (name, field) in a {
                    if let Some((_, other)) = b.iter().find(|(found, _)| found == name) {
                        widened |= self.subsume(field, other)?;
                    }
                }
                // The shared fields are settled, so the left takes the
                // right's types for them; what remains is which fields each
                // record has.
                let settled = |fields: &[(Symbol, Ty)], other: &[(Symbol, Ty)]| -> Tags {
                    fields
                        .iter()
                        .map(|(name, ty)| {
                            let shared = other.iter().find(|(found, _)| found == name);
                            (
                                *name,
                                vec![shared.map_or_else(|| ty.clone(), |(_, ty)| ty.clone())],
                            )
                        })
                        .collect()
                };
                self.unify_rows(
                    Former::Fields,
                    (&settled(a, b), a_tail.as_deref()),
                    (&entries(b), b_tail.as_deref()),
                )?;
                Ok(widened)
            }
            (Ty::Variants(a, a_tail), Ty::Variants(b, b_tail)) => {
                let mut widened = false;
                for (name, fields) in a {
                    if let Some((_, other)) = b.iter().find(|(found, _)| found == name) {
                        if fields.len() != other.len() {
                            return Err(Mismatch::Fields(fields.len(), other.len()));
                        }
                        for (field, other) in fields.iter().zip(other) {
                            widened |= self.subsume(field, other)?;
                        }
                    }
                }
                // The shared tags' fields are settled; what remains is which
                // tags each row holds.
                let settled = |tags: &[(Symbol, Vec<Ty>)], other: &[(Symbol, Vec<Ty>)]| -> Tags {
                    tags.iter()
                        .map(|(name, fields)| {
                            let shared = other.iter().any(|(found, _)| found == name);
                            (*name, if shared { Vec::new() } else { fields.clone() })
                        })
                        .collect()
                };
                let (left, right) = (settled(a, b), settled(b, a));
                match self.unify_rows(
                    Former::Tags,
                    (&left, a_tail.as_deref()),
                    (&right, b_tail.as_deref()),
                ) {
                    Ok(()) => Ok(widened),
                    Err(_)
                        if a_tail.is_none()
                            && matches!(b_tail.as_deref(), Some(Ty::Rigid(_)))
                            && a.iter()
                                .all(|(name, _)| b.iter().any(|(found, _)| found == name)) =>
                    {
                        Ok(true)
                    }
                    Err(mismatch) => Err(mismatch),
                }
            }
            _ => self.unify(&actual, &expected).map(|()| false),
        }
    }

    /// Row unification, for tag rows and record rows alike: entries both
    /// rows hold unify, and each
    /// open side's tail takes the tags only the other holds. A closed row
    /// takes nothing, and neither does a rigid tail, which stands for tags
    /// only a caller knows.
    fn unify_rows(
        &mut self,
        former: Former,
        (left, left_tail): (&[(Symbol, Vec<Ty>)], Option<&Ty>),
        (right, right_tail): (&[(Symbol, Vec<Ty>)], Option<&Ty>),
    ) -> Result<(), Mismatch> {
        for (name, fields) in left {
            if let Some((_, other)) = right.iter().find(|(found, _)| found == name) {
                if fields.len() != other.len() {
                    return Err(Mismatch::Fields(fields.len(), other.len()));
                }
                for (a, b) in fields.iter().zip(other) {
                    self.unify(a, b)?;
                }
            }
        }
        let only = |from: &[(Symbol, Vec<Ty>)], other: &[(Symbol, Vec<Ty>)]| -> Tags {
            from.iter()
                .filter(|(name, _)| !other.iter().any(|(found, _)| found == name))
                .cloned()
                .collect()
        };
        let (only_left, only_right) = (only(left, right), only(right, left));
        let not_among =
            |extra: &Tags, tags: &[(Symbol, Vec<Ty>)], tail: Option<&Ty>| Mismatch::NotAmong {
                tags: extra.iter().map(|(name, _)| *name).collect(),
                row: former.build(tags.to_vec(), tail.cloned().map(Box::new)),
            };
        match (left_tail, right_tail) {
            (None, None) if only_left.is_empty() && only_right.is_empty() => Ok(()),
            (None, None) if only_left.is_empty() => Err(not_among(&only_right, left, None)),
            (None, None) => Err(not_among(&only_left, right, None)),
            (Some(Ty::Var(v)), None) => {
                if !only_left.is_empty() {
                    return Err(not_among(&only_left, right, None));
                }
                self.unify(&Ty::Var(*v), &former.build(only_right, None))
            }
            (None, Some(Ty::Var(v))) => {
                if !only_right.is_empty() {
                    return Err(not_among(&only_right, left, None));
                }
                self.unify(&Ty::Var(*v), &former.build(only_left, None))
            }
            (Some(Ty::Var(v)), Some(Ty::Var(w))) => {
                if v == w {
                    return if only_left.is_empty() && only_right.is_empty() {
                        Ok(())
                    } else {
                        Err(Mismatch::Reason(
                            "two rows share their rest, so neither may hold what the other lacks",
                        ))
                    };
                }
                let rest = Box::new(self.fresh());
                self.unify(&Ty::Var(*v), &former.build(only_right, Some(rest.clone())))?;
                self.unify(&Ty::Var(*w), &former.build(only_left, Some(rest)))
            }
            (Some(Ty::Var(v)), Some(rigid @ Ty::Rigid(_))) => {
                if !only_left.is_empty() {
                    return Err(not_among(&only_left, right, right_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_right, Some(Box::new(rigid.clone()))),
                )
            }
            (Some(rigid @ Ty::Rigid(_)), Some(Ty::Var(v))) => {
                if !only_right.is_empty() {
                    return Err(not_among(&only_right, left, left_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_left, Some(Box::new(rigid.clone()))),
                )
            }
            (Some(Ty::Rigid(a)), Some(Ty::Rigid(b)))
                if a == b && only_left.is_empty() && only_right.is_empty() =>
            {
                Ok(())
            }
            _ => Err(Mismatch::Reason(
                "a row whose rest a caller chooses is neither closed nor another caller's",
            )),
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        self.instantiated(scheme).0
    }

    /// A scheme instantiated, with the variable each of its own became.
    fn instantiated(&mut self, scheme: &Scheme) -> (Ty, HashMap<u32, Ty>) {
        let replacements: HashMap<_, _> = scheme
            .variables
            .iter()
            .map(|variable| (*variable, self.fresh()))
            .collect();
        (substitute(&scheme.ty, &replacements), replacements)
    }

    fn skolemize(&mut self, scheme: &Scheme) -> (Ty, HashMap<u32, Ty>) {
        let replacements: HashMap<_, _> = scheme
            .variables
            .iter()
            .map(|variable| {
                let rigid = self.next_rigid;
                self.next_rigid = self
                    .next_rigid
                    .checked_add(1)
                    .expect("fewer than 2^32 rigid type variables");
                (*variable, Ty::Rigid(rigid))
            })
            .collect();
        (substitute(&scheme.ty, &replacements), replacements)
    }
}

/// Whether a written type holds no function anywhere: the type of data.
fn first_order(ty: &h::Type) -> bool {
    match ty {
        h::Type::Function(..) => false,
        h::Type::Variable(_) => true,
        h::Type::Named(_, arguments) => arguments.iter().all(first_order),
        h::Type::Variants(tags) => tags.iter().flat_map(|tag| &tag.fields).all(first_order),
        h::Type::Record(fields, _) => fields.iter().all(|(_, field)| first_order(field)),
        h::Type::Tuple(members) => members.iter().all(first_order),
    }
}

/// Whether a written type is one a parameter may have: data, or a function
/// of at least one parameter answering data, itself passed its own.
fn passable(ty: &h::Type) -> bool {
    match ty {
        h::Type::Function(parameters, result) => {
            !parameters.is_empty() && parameters.iter().all(passable) && first_order(result)
        }
        other => first_order(other),
    }
}

fn contains(ty: &Ty, variable: u32) -> bool {
    match ty {
        Ty::Var(id) => *id == variable,
        Ty::Rigid(_) => false,
        Ty::Named(_, arguments) => arguments.iter().any(|ty| contains(ty, variable)),
        Ty::Function(parameters, result) => {
            parameters.iter().any(|ty| contains(ty, variable)) || contains(result, variable)
        }
        Ty::Variants(tags, tail) => {
            tags.iter()
                .flat_map(|(_, fields)| fields)
                .any(|ty| contains(ty, variable))
                || tail.as_deref().is_some_and(|tail| contains(tail, variable))
        }
        Ty::Record(fields, tail) => {
            fields.iter().any(|(_, ty)| contains(ty, variable))
                || tail.as_deref().is_some_and(|tail| contains(tail, variable))
        }
        Ty::Tuple(members) => members.iter().any(|ty| contains(ty, variable)),
    }
}

fn substitute(ty: &Ty, replacements: &HashMap<u32, Ty>) -> Ty {
    match ty {
        Ty::Var(id) => replacements.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Rigid(_) => ty.clone(),
        Ty::Named(name, arguments) => Ty::Named(
            *name,
            arguments
                .iter()
                .map(|ty| substitute(ty, replacements))
                .collect(),
        ),
        Ty::Function(parameters, result) => Ty::Function(
            parameters
                .iter()
                .map(|ty| substitute(ty, replacements))
                .collect(),
            Box::new(substitute(result, replacements)),
        ),
        Ty::Variants(tags, tail) => Ty::Variants(
            tags.iter()
                .map(|(name, fields)| {
                    (
                        *name,
                        fields
                            .iter()
                            .map(|ty| substitute(ty, replacements))
                            .collect(),
                    )
                })
                .collect(),
            tail.as_deref()
                .map(|tail| Box::new(substitute(tail, replacements))),
        ),
        Ty::Record(fields, tail) => Ty::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, substitute(ty, replacements)))
                .collect(),
            tail.as_deref()
                .map(|tail| Box::new(substitute(tail, replacements))),
        ),
        Ty::Tuple(members) => Ty::Tuple(
            members
                .iter()
                .map(|ty| substitute(ty, replacements))
                .collect(),
        ),
    }
}

struct Checker<'a> {
    symbols: &'a Symbols,
    prelude: &'a PreludeIds,
    infer: Infer,
    values: HashMap<Symbol, Scheme>,
    constructors: HashMap<Symbol, Scheme>,
    methods: HashMap<Symbol, Vec<MethodImpl>>,
    fields: HashMap<Symbol, Vec<FieldImpl>>,
    visible_methods: HashMap<ModuleId, HashSet<Symbol>>,
    pending_methods: Vec<PendingMethod>,
    pending_numerals: Vec<PendingNumeral>,
    pending_tags: Vec<PendingTag>,
    pending_bare: Vec<PendingBare>,
    pending_closings: Vec<PendingClosing>,
    /// Each definition's bounds, over its scheme's variables.
    bounds: HashMap<Symbol, Vec<Bound>>,
    /// Each signed definition's type variables, by the names it writes them.
    variable_names: HashMap<Symbol, HashMap<Symbol, u32>>,
    /// The bounds of the signed body being checked, and its variables by
    /// name, rigid as its body sees them.
    current: Vec<Bound>,
    current_names: HashMap<Symbol, Ty>,
    bound_sites: Vec<(ModuleId, super::ast::Span, Ty, Symbol)>,
    deferred_numerals: Vec<DeferredNumeral>,
    /// What the clause or lambda being checked answers, innermost last,
    /// which is what a `?` in it answers early with. A guard answers
    /// nothing.
    answers: Vec<Option<Ty>>,
    expression_types: Vec<(ModuleId, super::ast::Span, Ty)>,
    clause_types: Vec<(ModuleId, super::ast::Span, Ty, Vec<Bound>)>,
    widenings: Vec<(ModuleId, super::ast::Span, Ty)>,
    checked: Types,
}

impl<'a> Checker<'a> {
    fn new(
        program: &h::Program,
        symbols: &'a Symbols,
        prelude: &'a PreludeIds,
    ) -> Result<Self, CheckError> {
        let mut checker = Self {
            symbols,
            prelude,
            infer: Infer::default(),
            values: HashMap::new(),
            constructors: HashMap::new(),
            methods: HashMap::new(),
            fields: HashMap::new(),
            visible_methods: program
                .modules
                .iter()
                .map(|module| {
                    (
                        module.source,
                        module.visible_methods.iter().copied().collect(),
                    )
                })
                .collect(),
            pending_methods: Vec::new(),
            pending_numerals: Vec::new(),
            pending_tags: Vec::new(),
            pending_bare: Vec::new(),
            pending_closings: Vec::new(),
            answers: Vec::new(),
            bounds: HashMap::new(),
            variable_names: HashMap::new(),
            current: Vec::new(),
            current_names: HashMap::new(),
            bound_sites: Vec::new(),
            deferred_numerals: Vec::new(),
            expression_types: Vec::new(),
            clause_types: Vec::new(),
            widenings: Vec::new(),
            checked: Types::default(),
        };
        for module in &program.modules {
            for item in &module.items {
                match item {
                    h::Item::Signature(signature) => {
                        checker.add_signature(module.source, signature, None)?;
                    }
                    h::Item::Data(data) => checker.add_data(module.source, data)?,
                    h::Item::Clause(_) => {}
                }
            }
        }
        checker.validate_literal_protocols(program)?;
        Ok(checker)
    }

    fn add_data(&mut self, module: ModuleId, data: &h::DataDecl) -> Result<(), CheckError> {
        let written = data
            .constructors
            .iter()
            .map(|constructor| (constructor.name, constructor.fields.as_slice()))
            .chain(
                data.wrapper
                    .iter()
                    .map(|wrapper| (wrapper.constructor, std::slice::from_ref(&wrapper.field))),
            );
        for (constructor, fields) in written {
            if !fields.iter().all(first_order) {
                return Err(failure(
                    module,
                    data.span,
                    format!(
                        "constructor `{}` holds a function; data may not store functions",
                        spelled(constructor, self.symbols)
                    ),
                ));
            }
        }
        let mut variables = HashMap::new();
        for parameter in &data.parameters {
            let fresh = self.infer.fresh();
            variables.insert(*parameter, fresh);
        }
        let arguments: Vec<_> = data
            .parameters
            .iter()
            .map(|parameter| variables[parameter].clone())
            .collect();
        let result = Ty::Named(data.name, arguments);
        for constructor in &data.constructors {
            let fields: Vec<_> = constructor
                .fields
                .iter()
                .map(|field| self.surface_type(field, &mut variables))
                .collect();
            let ty = if fields.is_empty() {
                result.clone()
            } else {
                Ty::Function(fields, Box::new(result.clone()))
            };
            self.constructors.insert(
                constructor.name,
                Scheme {
                    variables: free_variables(&ty),
                    ty,
                },
            );
        }
        if let Some(wrapper) = &data.wrapper {
            let field = self.surface_type(&wrapper.field, &mut variables);
            if matches!(&field, Ty::Record(_, Some(_))) {
                return Err(failure(
                    module,
                    data.span,
                    "a declared type's record is closed; a record with `*` is written where it is taken",
                ));
            }
            if let Ty::Record(fields, _) = &field {
                for (name, field_ty) in fields {
                    let ty = Ty::Function(vec![result.clone()], Box::new(field_ty.clone()));
                    self.fields.entry(*name).or_default().push(FieldImpl {
                        owner: data.name,
                        scheme: Scheme {
                            variables: free_variables(&ty),
                            ty,
                        },
                    });
                }
            }
            let ty = Ty::Function(vec![field], Box::new(result));
            self.constructors.insert(
                wrapper.constructor,
                Scheme {
                    variables: free_variables(&ty),
                    ty,
                },
            );
        }
        for method in &data.methods {
            if let h::MethodItem::Signature(signature) = method {
                self.add_signature(module, signature, Some(data.name))?;
            }
        }
        Ok(())
    }

    fn add_signature(
        &mut self,
        module: ModuleId,
        signature: &h::SignatureDecl,
        owner: Option<Symbol>,
    ) -> Result<(), CheckError> {
        // A function is passed into a call, so it is a parameter's type,
        // never an answer's or data's.
        if !first_order(&signature.result) || !signature.parameters.iter().all(passable) {
            return Err(failure(
                module,
                signature.span,
                format!(
                    "`{}` holds a function other than as a parameter; a function is passed into a call, never answered or stored",
                    self.symbols.text(signature.spelling)
                ),
            ));
        }
        let mut variables = HashMap::new();
        let parameters = signature
            .parameters
            .iter()
            .map(|ty| self.surface_type(ty, &mut variables))
            .collect();
        let result = self.surface_type(&signature.result, &mut variables);
        let ty = self.open_result_rows(&Ty::Function(parameters, Box::new(result)), true);
        let bounds = self.written_bounds(module, signature, &mut variables)?;
        let mut quantified = free_variables(&ty);
        for bound in &bounds {
            for variable in free_variables(&bound.ty) {
                if !quantified.contains(&variable) {
                    quantified.push(variable);
                }
            }
        }
        let scheme = Scheme {
            variables: quantified,
            ty,
        };
        self.values.insert(signature.name, scheme.clone());
        self.bounds.insert(signature.name, bounds);
        self.variable_names.insert(
            signature.name,
            variables
                .iter()
                .filter_map(|(name, ty)| match ty {
                    Ty::Var(variable) => Some((*name, *variable)),
                    _ => None,
                })
                .collect(),
        );
        if let Some(owner) = owner {
            self.methods
                .entry(signature.spelling)
                .or_default()
                .push(MethodImpl {
                    owner,
                    target: signature.name,
                    scheme,
                    bound: false,
                });
        }
        Ok(())
    }

    /// A signature's `where` bounds, over its own type variables. A
    /// variable a bound alone mentions is quantified too: which type it is,
    /// the bound's implementation says at each specialization. A bound may
    /// be on such a variable, one a bound on a variable already determined
    /// mentions, since that bound's implementation determines it in turn;
    /// on any other, it could never be met, and is refused.
    fn written_bounds(
        &mut self,
        module: ModuleId,
        signature: &h::SignatureDecl,
        variables: &mut HashMap<Symbol, Ty>,
    ) -> Result<Vec<Bound>, CheckError> {
        let mut bounds: Vec<Option<Bound>> = vec![None; signature.constraints.len()];
        loop {
            let mut progress = false;
            for (constraint, bound) in signature.constraints.iter().zip(&mut bounds) {
                let (variable, member, ty) = match constraint {
                    h::Constraint::Member {
                        variable,
                        member,
                        ty,
                    } => (*variable, *member, ty),
                    h::Constraint::Alias { .. } => {
                        unreachable!("resolution expands every constraint alias")
                    }
                };
                if bound.is_some() {
                    continue;
                }
                let Some(owner) = variables.get(&variable).cloned() else {
                    continue;
                };
                let ty = self.surface_type(ty, variables);
                // A member taking the type first is a method of its values;
                // anything else is reached through the type.
                let associated = !matches!(&ty, Ty::Function(parameters, _)
                    if parameters.first().is_some_and(|first| *first == owner));
                *bound = Some(Bound {
                    owner,
                    member,
                    ty,
                    associated,
                });
                progress = true;
            }
            if !progress {
                break;
            }
        }
        if let Some(h::Constraint::Member { variable, .. }) = signature
            .constraints
            .iter()
            .zip(&bounds)
            .find_map(|(constraint, bound)| bound.is_none().then_some(constraint))
        {
            return Err(failure(
                module,
                signature.span,
                format!(
                    "`where` bounds `{}`, which neither the signature nor another bound determines",
                    self.symbols.text(*variable)
                ),
            ));
        }
        Ok(bounds.into_iter().flatten().collect())
    }

    /// Give every nonempty tag row in result position a tail, which the
    /// scheme then quantifies.
    ///
    /// A signature's `Result(a [Empty])` says what this definition fails
    /// with, and its body is checked against exactly that: skolemized, the
    /// tail is rigid, so a body answering another tag is refused. It says
    /// nothing about callers, whose business it is whether `Empty` travels
    /// in one row with their own failures: instantiated, the tail is a
    /// variable they may widen. A row in a parameter is what a definition
    /// handles, and stays closed. The empty row is the type with no values
    /// rather than a failure row, and stays closed too.
    fn open_result_rows(&mut self, ty: &Ty, positive: bool) -> Ty {
        match ty {
            Ty::Var(_) | Ty::Rigid(_) => ty.clone(),
            Ty::Named(name, arguments) => Ty::Named(
                *name,
                arguments
                    .iter()
                    .map(|ty| self.open_result_rows(ty, positive))
                    .collect(),
            ),
            Ty::Function(parameters, result) => Ty::Function(
                parameters
                    .iter()
                    .map(|ty| self.open_result_rows(ty, !positive))
                    .collect(),
                Box::new(self.open_result_rows(result, positive)),
            ),
            Ty::Variants(tags, tail) => {
                let tags: Tags = tags
                    .iter()
                    .map(|(name, fields)| {
                        let fields = fields
                            .iter()
                            .map(|ty| self.open_result_rows(ty, positive))
                            .collect();
                        (*name, fields)
                    })
                    .collect();
                let tail = match tail {
                    None if positive && !tags.is_empty() => Some(Box::new(self.infer.fresh())),
                    other => other.clone(),
                };
                Ty::Variants(tags, tail)
            }
            Ty::Record(fields, tail) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.open_result_rows(ty, positive)))
                    .collect(),
                tail.clone(),
            ),
            Ty::Tuple(members) => Ty::Tuple(
                members
                    .iter()
                    .map(|ty| self.open_result_rows(ty, positive))
                    .collect(),
            ),
        }
    }

    fn surface_type(&mut self, ty: &h::Type, variables: &mut HashMap<Symbol, Ty>) -> Ty {
        match ty {
            h::Type::Named(name, arguments) => Ty::Named(
                *name,
                arguments
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
            ),
            h::Type::Variable(name) => variables
                .entry(*name)
                .or_insert_with(|| self.infer.fresh())
                .clone(),
            h::Type::Function(parameters, result) => Ty::Function(
                parameters
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
                Box::new(self.surface_type(result, variables)),
            ),
            // A written row is closed: it is exactly these tags.
            h::Type::Variants(constructors) => Ty::Variants(
                constructors
                    .iter()
                    .map(|constructor| {
                        (
                            constructor.name,
                            constructor
                                .fields
                                .iter()
                                .map(|ty| self.surface_type(ty, variables))
                                .collect(),
                        )
                    })
                    .collect(),
                None,
            ),
            // `*` stands for whatever other fields a caller's record has:
            // a tail of its own, which the scheme quantifies.
            h::Type::Record(fields, open) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.surface_type(ty, variables)))
                    .collect(),
                open.then(|| Box::new(self.infer.fresh())),
            ),
            h::Type::Tuple(members) => Ty::Tuple(
                members
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
            ),
        }
    }

    fn validate_literal_protocols(&self, program: &h::Program) -> Result<(), CheckError> {
        let Some(module) = program.modules.first().map(|module| module.source) else {
            return Ok(());
        };
        for (function, parameters, result, written) in [
            (
                self.prelude.int_of_nat,
                vec![self.prelude.nat],
                self.prelude.int,
                "Int.of_nat : Nat -> Int",
            ),
            (
                self.prelude.int_neg,
                vec![self.prelude.int],
                self.prelude.int,
                "Int.neg : Int -> Int",
            ),
        ] {
            let Some(scheme) = self.values.get(&function) else {
                return Err(failure(
                    module,
                    super::ast::Span::default(),
                    format!("the prelude must define `{written}` for integer literals"),
                ));
            };
            let expected = Ty::Function(
                parameters
                    .into_iter()
                    .map(|name| Ty::Named(name, Vec::new()))
                    .collect(),
                Box::new(Ty::Named(result, Vec::new())),
            );
            if scheme.ty != expected {
                return Err(failure(
                    module,
                    super::ast::Span::default(),
                    format!("the prelude must define `{written}` for integer literals"),
                ));
            }
        }
        Ok(())
    }

    fn check(mut self, program: &h::Program) -> Result<Types, CheckError> {
        let definitions = definitions(program);
        let unsigned: HashSet<_> = definitions
            .keys()
            .filter(|name| !self.values.contains_key(name))
            .copied()
            .collect();

        for component in components(&definitions, &unsigned) {
            let marks = self.marks();
            let mut monotypes = HashMap::new();
            for name in &component {
                let clauses = &definitions[name];
                let arity = clauses
                    .first()
                    .map_or(0, |(_, clause)| clause.patterns.len());
                if clauses
                    .iter()
                    .any(|(_, clause)| clause.patterns.len() != arity)
                {
                    let (module, clause) = clauses[0];
                    return Err(failure(
                        module,
                        clause.span,
                        "clauses of one function have different arities",
                    ));
                }
                let parameters = (0..arity).map(|_| self.infer.fresh()).collect();
                let ty = Ty::Function(parameters, Box::new(self.infer.fresh()));
                self.values.insert(
                    *name,
                    Scheme {
                        variables: Vec::new(),
                        ty: ty.clone(),
                    },
                );
                monotypes.insert(*name, ty);
            }
            for name in &component {
                for &(module, clause) in &definitions[name] {
                    self.check_clause(module, clause, &monotypes[name])?;
                }
            }
            let types: Vec<Ty> = monotypes.values().cloned().collect();
            let names = component_name_set(&monotypes);
            self.finish_pending(marks, Finish::Unsigned(&types, &names))?;
            for name in &component {
                let Ty::Function(parameters, _) = self.infer.resolve(&monotypes[name]) else {
                    continue;
                };
                let clauses = &definitions[name];
                for (column, parameter) in parameters.iter().enumerate() {
                    let rows = clauses
                        .iter()
                        .map(|(_, clause)| {
                            (clause.patterns[column].clone(), clause.guard.is_some())
                        })
                        .collect();
                    let (module, clause) = clauses[0];
                    self.close_rows(parameter, rows)
                        .map_err(|message| failure(module, clause.span, message))?;
                }
            }
            for name in &component {
                if let Ty::Function(_, result) = self.infer.resolve(&monotypes[name])
                    && matches!(*result, Ty::Function(..))
                {
                    let (module, clause) = definitions[name][0];
                    return Err(failure(
                        module,
                        clause.span,
                        format!(
                            "`{}` answers a function; a function is passed into a call, never answered",
                            spelled(*name, self.symbols)
                        ),
                    ));
                }
            }
            // Resolved, so that instantiating a scheme renames every
            // variable a bound mentions, not only the ones not yet linked.
            let bounds: Vec<Bound> = self
                .inferred_bounds(marks)?
                .into_iter()
                .map(|bound| Bound {
                    owner: self.infer.resolve(&bound.owner),
                    ty: self.infer.resolve(&bound.ty),
                    ..bound
                })
                .collect();
            for name in &component {
                for (module, clause) in &definitions[name] {
                    if let Some(site) = self
                        .clause_types
                        .iter_mut()
                        .find(|(at, span, _, _)| at == module && *span == clause.span)
                    {
                        site.3.clone_from(&bounds);
                    }
                }
            }
            for name in component {
                let ty = self.infer.resolve(&monotypes[&name]);
                let mut scheme = self.generalize(&ty, Some(&names));
                // A variable only a bound mentions is quantified too.
                let mentioned = bounds
                    .iter()
                    .flat_map(|bound| free_variables(&self.infer.resolve(&bound.ty)));
                let fixed: HashSet<u32> = self
                    .values
                    .iter()
                    .filter(|(held, _)| !names.contains(held))
                    .flat_map(|(_, scheme)| free_scheme(scheme))
                    .collect();
                for variable in mentioned {
                    if !fixed.contains(&variable) && !scheme.variables.contains(&variable) {
                        scheme.variables.push(variable);
                    }
                }
                self.bounds.insert(name, bounds.clone());
                self.values.insert(name, scheme);
            }
        }

        for (name, clauses) in &definitions {
            let Some(scheme) = self.values.get(name).cloned() else {
                continue;
            };
            if unsigned.contains(name) {
                continue;
            }
            for &(module, clause) in clauses {
                let marks = self.marks();
                let (ty, rigid) = self.infer.skolemize(&scheme);
                // The body meets its bounds as written, at its own rigid
                // variables, and names them by the signature's names.
                self.current = self
                    .bounds
                    .get(name)
                    .map(|bounds| {
                        bounds
                            .iter()
                            .map(|bound| bound.substituted(&rigid))
                            .collect()
                    })
                    .unwrap_or_default();
                self.current_names = self
                    .variable_names
                    .get(name)
                    .map(|names| {
                        names
                            .iter()
                            .filter_map(|(spelled, variable)| {
                                rigid.get(variable).map(|ty| (*spelled, ty.clone()))
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                self.check_clause(module, clause, &ty)?;
                self.finish_pending(marks, Finish::Signed)?;
                self.current.clear();
                self.current_names.clear();
            }
        }
        self.checked.values = self
            .values
            .iter()
            .map(|(&name, scheme)| (name, self.public_scheme(name, scheme)))
            .collect();
        self.checked.expressions = self
            .expression_types
            .iter()
            .map(|(module, span, ty)| ExpressionSite {
                module: *module,
                span: *span,
                ty: public_type(&self.infer.resolve(ty)),
            })
            .collect();
        self.checked.widenings = self
            .widenings
            .iter()
            .map(|(module, span, ty)| ExpressionSite {
                module: *module,
                span: *span,
                ty: public_type(&self.infer.resolve(ty)),
            })
            .collect();
        self.checked.clauses = self
            .clause_types
            .iter()
            .map(|(module, span, ty, bounds)| ClauseSite {
                module: *module,
                span: *span,
                ty: public_type(&self.infer.resolve(ty)),
                bounds: bounds
                    .iter()
                    .map(|bound| self.public_bound(bound))
                    .collect(),
            })
            .collect();
        self.checked.bound_sites = self
            .bound_sites
            .iter()
            .map(|(module, span, owner, member)| BoundSite {
                module: *module,
                span: *span,
                owner: public_type(&self.infer.resolve(owner)),
                member: *member,
            })
            .collect();
        self.checked.deferred_numerals = std::mem::take(&mut self.deferred_numerals);
        Ok(self.checked)
    }

    fn public_bound(&self, bound: &Bound) -> InferredBound {
        InferredBound {
            owner: public_type(&self.infer.resolve(&bound.owner)),
            member: bound.member,
            ty: public_type(&self.infer.resolve(&bound.ty)),
            associated: bound.associated,
        }
    }

    fn public_scheme(&self, name: Symbol, scheme: &Scheme) -> InferredScheme {
        InferredScheme {
            bounds: self
                .bounds
                .get(&name)
                .map(|bounds| {
                    bounds
                        .iter()
                        .map(|bound| self.public_bound(bound))
                        .collect()
                })
                .unwrap_or_default(),
            variables: scheme
                .variables
                .iter()
                .copied()
                .map(|index| TypeVariable {
                    index,
                    rigid: false,
                })
                .collect(),
            ty: public_type(&self.infer.resolve(&scheme.ty)),
        }
    }

    fn check_clause(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        function: &Ty,
    ) -> Result<(), CheckError> {
        self.clause_types
            .push((module, clause.span, function.clone(), self.current.clone()));
        let Ty::Function(parameters, result) = self.infer.resolve(function) else {
            return Err(failure(module, clause.span, "definition is not a function"));
        };
        if parameters.len() != clause.patterns.len() {
            return Err(failure(
                module,
                clause.span,
                format!(
                    "clause takes {} patterns but its signature takes {} parameters",
                    clause.patterns.len(),
                    parameters.len()
                ),
            ));
        }
        let mut locals = vec![None; usize::try_from(clause.locals).expect("u32 fits usize")];
        for (pattern, parameter) in clause.patterns.iter().zip(parameters) {
            self.pattern(module, pattern, &parameter, &mut locals, clause.span)?;
        }
        if let Some(guard) = &clause.guard {
            self.answers.push(None);
            let actual = self.expr(module, guard, &mut locals);
            self.answers.pop();
            let actual = actual?;
            self.unify_at(module, guard.span, &actual, &self.bool_type())?;
        }
        self.answers.push(Some((*result).clone()));
        let checked = self.clause_body(module, clause, &mut locals, &result);
        self.answers.pop();
        checked
    }

    /// A clause's bindings and answer, with what it answers on top of
    /// [`Self::answers`].
    fn clause_body(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        locals: &mut Vec<Option<Scheme>>,
        result: &Ty,
    ) -> Result<(), CheckError> {
        for binding in &clause.body.bindings {
            let marks = self.marks();
            let value = self.expr(module, &binding.value, locals)?;
            let mut bound = Vec::new();
            collect_pattern_locals(&binding.pattern, &mut bound);
            self.pattern(module, &binding.pattern, &value, locals, binding.value.span)?;
            self.pending_closings.push(PendingClosing {
                module,
                span: binding.value.span,
                ty: value.clone(),
                rows: vec![(binding.pattern.clone(), false)],
            });
            self.finish_pending(marks, Finish::Binding)?;
            if matches!(self.infer.resolve(&value), Ty::Function(..)) {
                return Err(failure(
                    module,
                    binding.value.span,
                    "a function may only be passed straight into a call; it cannot be bound, answered, or stored",
                ));
            }
            for local in bound {
                let ty = locals[local.index()]
                    .as_ref()
                    .expect("pattern binding installs its local")
                    .ty
                    .clone();
                locals[local.index()] = Some(self.generalize_local(&ty, locals, local));
            }
        }
        let actual = self.expr(module, &clause.body.result, locals)?;
        let span = clause.body.result.span;
        let widened = self.infer.subsume(&actual, result).map_err(|reason| {
            failure(
                module,
                span,
                match reason {
                    Mismatch::NotAmong { .. } => reason.describe(self.symbols),
                    _ => format!(
                        "type mismatch: {} and {} ({})",
                        show(&self.infer.resolve(&actual), self.symbols),
                        show(&self.infer.resolve(result), self.symbols),
                        reason.describe(self.symbols)
                    ),
                },
            )
        })?;
        if widened {
            self.widenings.push((module, span, (*result).clone()));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn pattern(
        &mut self,
        module: ModuleId,
        pattern: &h::Pattern,
        expected: &Ty,
        locals: &mut [Option<Scheme>],
        span: super::ast::Span,
    ) -> Result<(), CheckError> {
        match pattern {
            h::Pattern::Wild => Ok(()),
            h::Pattern::String(_) => {
                let str_ = Ty::Named(self.prelude.str_, Vec::new());
                self.unify_at(module, span, expected, &str_)
            }
            h::Pattern::Bind(local) => {
                locals[local.index()] = Some(Scheme {
                    variables: Vec::new(),
                    ty: expected.clone(),
                });
                Ok(())
            }
            h::Pattern::Constructor(constructor, fields) => {
                let Some(scheme) = self.constructors.get(constructor).cloned() else {
                    return Err(failure(module, span, "constructor has no declared type"));
                };
                let ty = self.infer.instantiate(&scheme);
                let (parameters, result) = match ty {
                    Ty::Function(parameters, result) => (parameters, *result),
                    result => (Vec::new(), result),
                };
                if fields.len() != parameters.len() {
                    return Err(failure(
                        module,
                        span,
                        "constructor pattern has the wrong number of fields",
                    ));
                }
                self.unify_at(module, span, expected, &result)?;
                for (field, parameter) in fields.iter().zip(parameters) {
                    self.pattern(module, field, &parameter, locals, span)?;
                }
                Ok(())
            }
            // A claimed word's reading is the scrutinee's type to decide.
            h::Pattern::Dual(dual, fields) => {
                let field_types: Vec<_> = fields.iter().map(|_| self.infer.fresh()).collect();
                self.pending_tags.push(PendingTag {
                    module,
                    span,
                    dual: dual.clone(),
                    fields: Some(field_types.clone()),
                    field_spans: Vec::new(),
                    result: expected.clone(),
                    resolved: false,
                });
                for (field, ty) in fields.iter().zip(&field_types) {
                    self.pattern(module, field, ty, locals, span)?;
                }
                Ok(())
            }
            // A tag pattern says the scrutinee is a row holding this tag.
            h::Pattern::Tag(label, fields) => {
                let field_types: Vec<_> = fields.iter().map(|_| self.infer.fresh()).collect();
                let row = Ty::Variants(
                    vec![(*label, field_types.clone())],
                    Some(Box::new(self.infer.fresh())),
                );
                self.unify_at(module, span, expected, &row)?;
                for (field, ty) in fields.iter().zip(&field_types) {
                    self.pattern(module, field, ty, locals, span)?;
                }
                Ok(())
            }
            h::Pattern::Number {
                magnitude,
                negative,
            } => {
                self.pending_numerals.push(PendingNumeral {
                    module,
                    span,
                    magnitude: magnitude.clone(),
                    negative: *negative,
                    ty: expected.clone(),
                    resolved: false,
                });
                Ok(())
            }
            h::Pattern::Range(start, end) => {
                for magnitude in [start, end] {
                    self.pending_numerals.push(PendingNumeral {
                        module,
                        span,
                        magnitude: magnitude.clone(),
                        negative: false,
                        ty: expected.clone(),
                        resolved: false,
                    });
                }
                Ok(())
            }
            h::Pattern::List(elements, rest) => {
                let element = self.infer.fresh();
                self.unify_at(module, span, expected, &self.list_type(element.clone()))?;
                for pattern in elements {
                    self.pattern(module, pattern, &element, locals, span)?;
                }
                if let Some(rest) = rest {
                    self.pattern(module, rest, expected, locals, span)?;
                }
                Ok(())
            }
            // `{x *}` names some fields and takes a record with any others.
            h::Pattern::Record(fields, open) => {
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|(name, _)| (*name, self.infer.fresh()))
                    .collect();
                let rest = open.then(|| Box::new(self.infer.fresh()));
                self.unify_at(
                    module,
                    span,
                    expected,
                    &Ty::Record(field_types.clone(), rest),
                )?;
                for ((_, pattern), (_, ty)) in fields.iter().zip(field_types) {
                    self.pattern(module, pattern, &ty, locals, span)?;
                }
                Ok(())
            }
            h::Pattern::Tuple(members) => {
                let member_types: Vec<_> = members.iter().map(|_| self.infer.fresh()).collect();
                self.unify_at(module, span, expected, &Ty::Tuple(member_types.clone()))?;
                for (member, ty) in members.iter().zip(&member_types) {
                    self.pattern(module, member, ty, locals, span)?;
                }
                Ok(())
            }
        }
    }

    fn expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        let ty = self.infer_expr(module, expression, locals)?;
        self.expression_types
            .push((module, expression.span, ty.clone()));
        Ok(ty)
    }

    fn infer_expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        match &expression.kind {
            h::ExprKind::Local(local) => {
                let Some(scheme) = locals[local.index()].as_ref() else {
                    return Err(failure(
                        module,
                        expression.span,
                        "local has no inferred type",
                    ));
                };
                Ok(self.infer.instantiate(scheme))
            }
            h::ExprKind::Global(global) => {
                let Some(scheme) = self.values.get(global).cloned() else {
                    return Err(failure(
                        module,
                        expression.span,
                        "global has no declared type",
                    ));
                };
                // A use owes the bounds the definition has.
                let (ty, replacements) = self.infer.instantiated(&scheme);
                self.oblige(module, expression.span, *global, &replacements);
                Ok(ty)
            }
            h::ExprKind::Associated(variable, member) => Err(failure(
                module,
                expression.span,
                format!(
                    "a member a bound gives is called: write `{}.{}()`",
                    self.symbols.text(*variable),
                    self.symbols.text(*member)
                ),
            )),
            h::ExprKind::Call(head, arguments)
                if matches!(head.kind, h::ExprKind::Associated(..)) =>
            {
                self.associated_call(module, expression.span, head, arguments, locals)
            }
            h::ExprKind::Constructor(constructor) => {
                let Some(scheme) = self.constructors.get(constructor).cloned() else {
                    return Err(failure(
                        module,
                        expression.span,
                        "constructor has no declared type",
                    ));
                };
                Ok(self.infer.instantiate(&scheme))
            }
            h::ExprKind::Try(value) => self.try_(module, expression.span, value, locals),
            // A tag alone is a value of a row holding it with no fields, or
            // where a function is wanted, the function building it from its
            // fields: `map_err(Wrap)`.
            h::ExprKind::Tag(label) => {
                let ty = self.infer.fresh();
                self.pending_bare.push(PendingBare {
                    module,
                    span: expression.span,
                    label: *label,
                    ty: ty.clone(),
                    resolved: false,
                });
                Ok(ty)
            }
            // A claimed word alone: a constructor as a function or a value,
            // or a tag with no fields, as its position decides.
            h::ExprKind::Dual(dual) => {
                Ok(self.defer_tag(module, expression.span, dual, None, Vec::new()))
            }
            h::ExprKind::Number(magnitude) => {
                let ty = self.infer.fresh();
                self.pending_numerals.push(PendingNumeral {
                    module,
                    span: expression.span,
                    magnitude: magnitude.clone(),
                    negative: false,
                    ty: ty.clone(),
                    resolved: false,
                });
                Ok(ty)
            }
            // Each splice is its value's `to_str`, and the pieces are joined.
            h::ExprKind::String(parts) => {
                for part in parts {
                    if let h::StringPart::Splice(splice) = part {
                        let value = self.expr(module, splice, locals)?;
                        let to_str = self.method_symbol(module, splice.span, "to_str")?;
                        let text = self.defer_method(
                            module,
                            splice_site(splice.span),
                            value,
                            to_str,
                            Vec::new(),
                            false,
                        );
                        let str_ = Ty::Named(self.prelude.str_, Vec::new());
                        self.unify_at(module, splice.span, &text, &str_)?;
                    }
                }
                if parts
                    .iter()
                    .all(|part| matches!(part, h::StringPart::Text(_)))
                {
                    let bytes = parts
                        .iter()
                        .flat_map(|part| match part {
                            h::StringPart::Text(text) => text.as_slice(),
                            h::StringPart::Splice(_) => unreachable!(),
                        })
                        .copied()
                        .collect::<Vec<_>>();
                    self.checked.literals.push(LiteralSite {
                        module,
                        span: expression.span,
                        ty: self.prelude.str_,
                        value: blessed::string(&bytes, self.prelude),
                    });
                }
                Ok(Ty::Named(self.prelude.str_, Vec::new()))
            }
            h::ExprKind::List(elements, rest) => {
                let element = self.infer.fresh();
                for expression in elements {
                    let actual = self.expr(module, expression, locals)?;
                    self.unify_at(module, expression.span, &actual, &element)?;
                }
                let list = self.list_type(element);
                if let Some(rest) = rest {
                    let actual = self.expr(module, rest, locals)?;
                    self.unify_at(module, rest.span, &actual, &list)?;
                }
                Ok(list)
            }
            h::ExprKind::Record(fields) => {
                let mut inferred = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    inferred.push((*name, self.expr(module, value, locals)?));
                }
                inferred.sort_by_key(|(name, _)| *name);
                Ok(Ty::Record(inferred, None))
            }
            h::ExprKind::Tuple(members) => {
                let mut inferred = Vec::with_capacity(members.len());
                for member in members {
                    inferred.push(self.expr(module, member, locals)?);
                }
                Ok(Ty::Tuple(inferred))
            }
            // An update replaces values; it adds no field and retypes none, so
            // the record must have each field named, at the value's type.
            h::ExprKind::Update(base, fields) => {
                let updated = self.expr(module, base, locals)?;
                let mut named = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    named.push((*name, self.expr(module, value, locals)?));
                }
                named.sort_by_key(|(name, _)| *name);
                let shape = Ty::Record(named, Some(Box::new(self.infer.fresh())));
                self.unify_at(module, expression.span, &updated, &shape)?;
                Ok(updated)
            }
            h::ExprKind::Lambda(patterns, body) => {
                let parameters: Vec<_> = patterns.iter().map(|_| self.infer.fresh()).collect();
                let mut bound = Vec::new();
                for (pattern, parameter) in patterns.iter().zip(&parameters) {
                    collect_pattern_locals(pattern, &mut bound);
                    self.pattern(module, pattern, parameter, locals, expression.span)?;
                }
                let answer = self.infer.fresh();
                self.answers.push(Some(answer.clone()));
                let result = self.expr(module, body, locals);
                self.answers.pop();
                let result = result?;
                self.unify_at(module, body.span, &result, &answer)?;
                for (pattern, parameter) in patterns.iter().zip(&parameters) {
                    self.pending_closings.push(PendingClosing {
                        module,
                        span: expression.span,
                        ty: parameter.clone(),
                        rows: vec![(pattern.clone(), false)],
                    });
                }
                for local in bound {
                    locals[local.index()] = None;
                }
                Ok(Ty::Function(parameters, Box::new(result)))
            }
            h::ExprKind::Call(head, arguments) if matches!(head.kind, h::ExprKind::Dual(_)) => {
                let h::ExprKind::Dual(dual) = &head.kind else {
                    unreachable!("guarded")
                };
                let mut fields = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    fields.push(self.expr(module, argument, locals)?);
                }
                let spans = arguments.iter().map(|argument| argument.span).collect();
                Ok(self.defer_tag(module, expression.span, dual, Some(fields), spans))
            }
            h::ExprKind::Call(head, arguments) if matches!(head.kind, h::ExprKind::Tag(_)) => {
                let h::ExprKind::Tag(label) = head.kind else {
                    unreachable!("guarded")
                };
                let mut fields = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    fields.push(self.expr(module, argument, locals)?);
                }
                Ok(self.tag(label, fields))
            }
            h::ExprKind::Call(head, arguments) => {
                let head_type = self.expr(module, head, locals)?;
                let mut argument_types = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    argument_types.push(self.expr(module, argument, locals)?);
                }
                let result = self.infer.fresh();
                let function = Ty::Function(argument_types, Box::new(result.clone()));
                self.unify_at(module, expression.span, &head_type, &function)?;
                Ok(result)
            }
            h::ExprKind::Member(receiver, member) => {
                let receiver = self.expr(module, receiver, locals)?;
                Ok(self.defer_method(module, expression.span, receiver, *member, Vec::new(), true))
            }
            h::ExprKind::Method(receiver, method, arguments) => self.method(
                module,
                expression.span,
                receiver,
                *method,
                arguments,
                locals,
            ),
            h::ExprKind::Unary(super::ast::UnaryOp::Negate, value)
                if matches!(value.kind, h::ExprKind::Number(_)) =>
            {
                let h::ExprKind::Number(magnitude) = &value.kind else {
                    unreachable!()
                };
                let ty = self.infer.fresh();
                self.pending_numerals.push(PendingNumeral {
                    module,
                    span: expression.span,
                    magnitude: magnitude.clone(),
                    negative: true,
                    ty: ty.clone(),
                    resolved: false,
                });
                Ok(ty)
            }
            h::ExprKind::Unary(operator, value) => {
                let name = match operator {
                    super::ast::UnaryOp::Negate => "neg",
                    super::ast::UnaryOp::Not => "not",
                };
                let method = self.method_symbol(module, expression.span, name)?;
                self.method(module, expression.span, value, method, &[], locals)
            }
            h::ExprKind::Binary(operator, left, right) => {
                let name = match operator {
                    super::ast::BinaryOp::Or => "or",
                    super::ast::BinaryOp::Xor => "xor",
                    super::ast::BinaryOp::And => "and",
                    super::ast::BinaryOp::Equal | super::ast::BinaryOp::NotEqual => "equals",
                    super::ast::BinaryOp::Less
                    | super::ast::BinaryOp::LessEqual
                    | super::ast::BinaryOp::Greater
                    | super::ast::BinaryOp::GreaterEqual => "cmp",
                    super::ast::BinaryOp::Add => "add",
                    super::ast::BinaryOp::Subtract => "sub",
                    super::ast::BinaryOp::Multiply => "mul",
                    super::ast::BinaryOp::Divide => "div",
                    super::ast::BinaryOp::Remainder => "mod",
                };
                let method = self.method_symbol(module, expression.span, name)?;
                let result = self.method(
                    module,
                    expression.span,
                    left,
                    method,
                    std::slice::from_ref(right),
                    locals,
                )?;
                if matches!(
                    operator,
                    super::ast::BinaryOp::Equal | super::ast::BinaryOp::NotEqual
                ) {
                    let bool_ = self.bool_type();
                    self.unify_at(module, expression.span, &result, &bool_)?;
                    Ok(bool_)
                } else if matches!(
                    operator,
                    super::ast::BinaryOp::Less
                        | super::ast::BinaryOp::LessEqual
                        | super::ast::BinaryOp::Greater
                        | super::ast::BinaryOp::GreaterEqual
                ) {
                    // Each ordering operator is a fixed view of one `cmp`.
                    let order = Ty::Named(self.prelude.order, Vec::new());
                    self.unify_at(module, expression.span, &result, &order)?;
                    Ok(self.bool_type())
                } else {
                    Ok(result)
                }
            }
        }
    }

    /// Close every open tag row the patterns take apart without a catch-all.
    ///
    /// A tag pattern only says the scrutinee holds that tag, so an unsigned
    /// `f(A) -> 1` and `f(B) -> 2` infer a row holding at least `A` and
    /// `B`. Left open, a caller could hand `f` a `C` no clause matches. Where
    /// every row matching here names a tag, and none takes whatever else
    /// comes, the row is exactly the tags there are clauses for. A guarded
    /// catch-all takes nothing, since its guard may fail. A rigid tail is a
    /// caller's to fill, so it cannot be closed: that match needs a
    /// catch-all.
    fn close_rows(&mut self, ty: &Ty, rows: Vec<(h::Pattern, bool)>) -> Result<(), String> {
        let rows: Vec<_> = rows
            .into_iter()
            .map(|(pattern, guarded)| (self.desugared(pattern), guarded))
            .collect();
        if rows.is_empty()
            || rows.iter().any(|(pattern, guarded)| {
                !guarded && matches!(pattern, h::Pattern::Wild | h::Pattern::Bind(_))
            })
        {
            return Ok(());
        }
        match self.infer.resolve(ty) {
            Ty::Variants(tags, tail) => {
                let tagged = rows
                    .iter()
                    .any(|(pattern, _)| matches!(pattern, h::Pattern::Tag(..)));
                match tail.as_deref() {
                    Some(Ty::Rigid(_)) if tagged => {
                        return Err(format!(
                            "`{}` may hold tags a caller adds, which no pattern here matches: write a catch-all",
                            show(&Ty::Variants(tags, tail.clone()), self.symbols)
                        ));
                    }
                    Some(_) if tagged => {
                        let resolved = Ty::Variants(tags.clone(), tail.clone());
                        self.infer
                            .unify(&resolved, &Ty::Variants(tags.clone(), None))
                            .map_err(|reason| reason.describe(self.symbols))?;
                    }
                    _ => {}
                }
                for (label, fields) in tags {
                    let taken: Vec<_> = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Tag(found, subs) if *found == label => {
                                Some((subs.clone(), *guarded))
                            }
                            _ => None,
                        })
                        .collect();
                    self.close_fields(&fields, &taken)?;
                }
            }
            Ty::Named(..) => {
                let mut constructors: Vec<Symbol> = Vec::new();
                for (pattern, _) in &rows {
                    if let h::Pattern::Constructor(constructor, _) = pattern
                        && !constructors.contains(constructor)
                    {
                        constructors.push(*constructor);
                    }
                }
                for constructor in constructors {
                    let Some(scheme) = self.constructors.get(&constructor).cloned() else {
                        continue;
                    };
                    let (fields, result) = match self.infer.instantiate(&scheme) {
                        Ty::Function(fields, result) => (fields, *result),
                        result => (Vec::new(), result),
                    };
                    self.infer
                        .unify(ty, &result)
                        .map_err(|reason| reason.describe(self.symbols))?;
                    let taken: Vec<_> = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Constructor(found, subs) if *found == constructor => {
                                Some((subs.clone(), *guarded))
                            }
                            _ => None,
                        })
                        .collect();
                    self.close_fields(&fields, &taken)?;
                }
            }
            Ty::Record(fields, _) => {
                for (name, field) in fields {
                    // A record pattern not naming the field takes any.
                    let column = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Record(held, _) => Some((
                                held.iter()
                                    .find(|(found, _)| *found == name)
                                    .map_or(h::Pattern::Wild, |(_, pattern)| pattern.clone()),
                                *guarded,
                            )),
                            _ => None,
                        })
                        .collect();
                    self.close_rows(&field, column)?;
                }
            }
            Ty::Tuple(members) => {
                for (at, member) in members.iter().enumerate() {
                    let column = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Tuple(held) => {
                                held.get(at).map(|pattern| (pattern.clone(), *guarded))
                            }
                            _ => None,
                        })
                        .collect();
                    self.close_rows(member, column)?;
                }
            }
            Ty::Var(_) | Ty::Rigid(_) | Ty::Function(..) => {}
        }
        Ok(())
    }

    /// [`Self::close_rows`] for each field of the rows one constructor or
    /// tag took apart.
    fn close_fields(
        &mut self,
        fields: &[Ty],
        taken: &[(Vec<h::Pattern>, bool)],
    ) -> Result<(), String> {
        for (at, field) in fields.iter().enumerate() {
            let column = taken
                .iter()
                .filter_map(|(subs, guarded)| subs.get(at).map(|sub| (sub.clone(), *guarded)))
                .collect();
            self.close_rows(field, column)?;
        }
        Ok(())
    }

    /// A pattern as what it matches: a list as the constructors it stands
    /// for, and a claimed word as the reading it took.
    fn desugared(&self, pattern: h::Pattern) -> h::Pattern {
        if let h::Pattern::Dual(dual, fields) = pattern {
            return match self.checked.readings.get(&dual.site) {
                Some(Reading::Constructor(constructor)) => {
                    h::Pattern::Constructor(*constructor, fields)
                }
                Some(Reading::Tag(label)) => h::Pattern::Tag(*label, fields),
                None => h::Pattern::Dual(dual, fields),
            };
        }
        let h::Pattern::List(elements, rest) = pattern else {
            return pattern;
        };
        let mut tail = rest.map_or_else(
            || h::Pattern::Constructor(self.prelude.list_nil, Vec::new()),
            |rest| *rest,
        );
        for element in elements.into_iter().rev() {
            tail = h::Pattern::Constructor(self.prelude.list_cons, vec![element, tail]);
        }
        tail
    }

    /// `a.zero()`: the member a `where` bound of the signed body being
    /// checked gives type `a`, named by the signature's name for it.
    fn associated_call(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        head: &h::Expr,
        arguments: &[h::Expr],
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        let h::ExprKind::Associated(variable, member) = head.kind else {
            unreachable!("guarded")
        };
        let spelled = |checker: &Self| {
            format!(
                "{}.{}",
                checker.symbols.text(variable),
                checker.symbols.text(member)
            )
        };
        let Some(owner) = self.current_names.get(&variable).cloned() else {
            return Err(failure(
                module,
                span,
                format!(
                    "`{}` names a type only in a signature's `where` bounds",
                    self.symbols.text(variable)
                ),
            ));
        };
        let Some(bound) = self
            .current
            .iter()
            .find(|bound| bound.associated && bound.member == member && bound.owner == owner)
            .cloned()
        else {
            return Err(failure(
                module,
                span,
                format!("no `where` bound gives `{}`", spelled(self)),
            ));
        };
        let Ty::Function(parameters, result) = bound.ty else {
            unreachable!("a bound's member is a function")
        };
        if parameters.len() != arguments.len() {
            return Err(failure(
                module,
                span,
                format!(
                    "`{}` takes {} arguments, but {} were given",
                    spelled(self),
                    parameters.len(),
                    arguments.len()
                ),
            ));
        }
        for (argument, parameter) in arguments.iter().zip(&parameters) {
            let given = self.expr(module, argument, locals)?;
            self.unify_at(module, argument.span, &given, parameter)?;
        }
        self.bound_sites.push((module, span, owner, member));
        Ok(*result)
    }

    /// `value?`: what an `Ok` holds, where the clause or lambda it is written
    /// in answers a `Result` whose error takes an `Err`'s, answered early.
    /// That is where failure rows join: each `?` adds its producer's tags to
    /// the answer's row, and a signature's row admits only its own.
    fn try_(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        value: &h::Expr,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        let taken = self.expr(module, value, locals)?;
        let (ok, error) = (self.infer.fresh(), self.infer.fresh());
        let result = Ty::Named(self.prelude.result, vec![ok.clone(), error.clone()]);
        self.unify_at(module, value.span, &taken, &result)?;
        let Some(Some(answer)) = self.answers.last().cloned() else {
            return Err(failure(
                module,
                span,
                "`?` answers early from its clause or lambda, and a guard answers nothing",
            ));
        };
        let answered_error = self.infer.fresh();
        let answered = Ty::Named(
            self.prelude.result,
            vec![self.infer.fresh(), answered_error.clone()],
        );
        self.infer.unify(&answer, &answered).map_err(|_| {
            failure(
                module,
                span,
                format!(
                    "`?` answers an `Err` early, but this answers {}",
                    show(&self.infer.resolve(&answer), self.symbols)
                ),
            )
        })?;
        self.infer
            .subsume(&error, &answered_error)
            .map_err(|reason| failure(module, span, reason.describe(self.symbols)))?;
        Ok(ok)
    }

    /// A claimed word at a position whose type will decide its reading.
    fn defer_tag(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        dual: &h::Dual,
        fields: Option<Vec<Ty>>,
        field_spans: Vec<super::ast::Span>,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_tags.push(PendingTag {
            module,
            span,
            dual: dual.clone(),
            fields,
            field_spans,
            result: result.clone(),
            resolved: false,
        });
        result
    }

    /// A pending word's field flowing into the type its reading gives it:
    /// widened where it is written in an expression and the reading's type
    /// is a row a caller may widen, unified otherwise.
    fn field_flows(
        &mut self,
        pending: &PendingTag,
        at: usize,
        field: &Ty,
        wanted: &Ty,
    ) -> Result<(), CheckError> {
        let Some(&span) = pending.field_spans.get(at) else {
            return self.unify_at(pending.module, pending.span, field, wanted);
        };
        let widened = self.infer.subsume(field, wanted).map_err(|reason| {
            failure(
                pending.module,
                span,
                match reason {
                    Mismatch::NotAmong { .. } => reason.describe(self.symbols),
                    _ => format!(
                        "type mismatch: {} and {} ({})",
                        show(&self.infer.resolve(field), self.symbols),
                        show(&self.infer.resolve(wanted), self.symbols),
                        reason.describe(self.symbols)
                    ),
                },
            )
        })?;
        if widened {
            self.widenings.push((pending.module, span, wanted.clone()));
        }
        Ok(())
    }

    /// A value of any row holding `label` with these fields: open, so it
    /// flows to whatever handles more.
    fn tag(&mut self, label: Symbol, fields: Vec<Ty>) -> Ty {
        Ty::Variants(vec![(label, fields)], Some(Box::new(self.infer.fresh())))
    }

    fn method(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        receiver: &h::Expr,
        name: Symbol,
        arguments: &[h::Expr],
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        let receiver = self.expr(module, receiver, locals)?;
        let mut argument_types = Vec::with_capacity(arguments.len());
        for argument in arguments {
            argument_types.push(self.expr(module, argument, locals)?);
        }
        Ok(self.defer_method(module, span, receiver, name, argument_types, false))
    }

    fn defer_method(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        receiver: Ty,
        name: Symbol,
        arguments: Vec<Ty>,
        member: bool,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_methods.push(PendingMethod {
            module,
            span,
            name,
            receiver,
            arguments,
            result: result.clone(),
            reach: if member { Reach::Bare } else { Reach::Called },
            resolved: false,
            obligation: false,
        });
        result
    }

    /// Owe, where `definition` is used, the bounds its scheme has, at the
    /// variables this use instantiated it with.
    fn oblige(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        definition: Symbol,
        replacements: &HashMap<u32, Ty>,
    ) {
        let Some(bounds) = self.bounds.get(&definition).cloned() else {
            return;
        };
        for bound in bounds {
            let bound = bound.substituted(replacements);
            let Ty::Function(parameters, result) = bound.ty else {
                continue;
            };
            let skipped = usize::from(!bound.associated);
            self.pending_methods.push(PendingMethod {
                module,
                span,
                name: bound.member,
                receiver: bound.owner,
                arguments: parameters.into_iter().skip(skipped).collect(),
                result: *result,
                reach: if bound.associated {
                    Reach::Type
                } else {
                    Reach::Called
                },
                resolved: false,
                obligation: true,
            });
        }
    }

    const fn marks(&self) -> Marks {
        Marks {
            methods: self.pending_methods.len(),
            numerals: self.pending_numerals.len(),
            tags: self.pending_tags.len(),
            closings: self.pending_closings.len(),
        }
    }

    fn finish_pending(&mut self, marks: Marks, finish: Finish<'_>) -> Result<(), CheckError> {
        let (method_start, numeral_start) = (marks.methods, marks.numerals);
        self.settle(marks)?;
        // A word nothing decided takes its one declared reading, before a
        // numeral does its default: `W(3)` builds a `W`, whatever `3` is.
        // One at a time, since reading one may prove another's position a
        // tag row.
        while let Some(index) = (marks.tags..self.pending_tags.len()).find(|&index| {
            let pending = &self.pending_tags[index];
            !pending.resolved && pending.dual.candidates.len() == 1
        }) {
            let pending = self.pending_tags[index].clone();
            self.settle_nominal(&pending)?;
            self.pending_tags[index].resolved = true;
            self.settle(marks)?;
        }
        if let Some(pending) = self.pending_tags[marks.tags..]
            .iter()
            .find(|pending| !pending.resolved)
        {
            return Err(self.ambiguous(pending));
        }
        if !matches!(finish, Finish::Binding) && self.settle_bare(true)? {
            self.settle(marks)?;
        }
        if matches!(finish, Finish::Binding) {
            return self.finish_binding(marks);
        }
        let generic = match finish {
            Finish::Unsigned(types, names) => {
                let generic = self.generic_variables(types, names);
                self.link_shapes(method_start, &generic);
                self.settle(marks)?;
                generic
            }
            _ => HashSet::new(),
        };
        let is_generic = |checker: &Self, ty: &Ty| matches!(checker.infer.resolve(ty), Ty::Var(variable) if generic.contains(&variable));
        // A numeral nothing typed takes its default one at a time, a
        // negative one first since only `Int` holds it, and what that
        // settles may type the rest: in `-2 < 1` the `1` is compared with an
        // `Int`, so it is one.
        loop {
            let undecided = |negative: bool| {
                (numeral_start..self.pending_numerals.len()).find(|&index| {
                    let numeral = &self.pending_numerals[index];
                    !numeral.resolved
                        && numeral.negative == negative
                        && matches!(self.infer.resolve(&numeral.ty), Ty::Var(_))
                        && !is_generic(self, &numeral.ty)
                })
            };
            let Some(index) = undecided(true).or_else(|| undecided(false)) else {
                break;
            };
            let numeral = self.pending_numerals[index].clone();
            let default = if numeral.negative {
                Ty::Named(self.prelude.int, Vec::new())
            } else {
                Ty::Named(self.prelude.nat, Vec::new())
            };
            self.unify_at(numeral.module, numeral.span, &numeral.ty, &default)?;
            self.settle(marks)?;
        }
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if !numeral.resolved && is_generic(self, &numeral.ty) {
                self.defer_numeral(&numeral)?;
                self.pending_numerals[index].resolved = true;
            }
        }
        self.settle_methods(method_start, true, &generic)?;
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved {
                continue;
            }
            self.elaborate(&numeral)?;
            self.pending_numerals[index].resolved = true;
        }
        let closings = self.pending_closings.split_off(marks.closings);
        for closing in closings {
            self.close_rows(&closing.ty, closing.rows)
                .map_err(|message| failure(closing.module, closing.span, message))?;
        }
        Ok(())
    }

    /// A numeral at the type its position gave it: a natural, or a call of
    /// the type's `of_nat`.
    fn elaborate(&mut self, numeral: &PendingNumeral) -> Result<(), CheckError> {
        let ty = self.infer.resolve(&numeral.ty);
        let (kind, symbol) = match ty {
            Ty::Named(name, ref arguments) if name == self.prelude.nat && arguments.is_empty() => {
                (NumeralType::Nat, self.prelude.nat)
            }
            Ty::Named(name, ref arguments) if name == self.prelude.int && arguments.is_empty() => {
                (NumeralType::Int, self.prelude.int)
            }
            Ty::Named(name, ref arguments)
                if arguments.is_empty()
                    && self.prelude.words.iter().any(|word| word.ty == name) =>
            {
                let word = self
                    .prelude
                    .words
                    .iter()
                    .find(|word| word.ty == name)
                    .expect("guarded");
                (NumeralType::Word(word), name)
            }
            // Only the prelude's integers are numerals, and no conversion
            // is inserted to make one fit anything else.
            other => {
                return Err(failure(
                    numeral.module,
                    numeral.span,
                    format!(
                        "a numeral cannot be a `{}`: a numeral is a `Nat`, `Int`, `U8`, `U16`, `U32`, or `U64`; convert a value with `of_nat`",
                        show(&other, self.symbols)
                    ),
                ));
            }
        };
        let value = blessed::numeral(
            numeral.magnitude.clone(),
            numeral.negative,
            kind,
            self.prelude,
        )
        .map_err(|error| failure(numeral.module, numeral.span, error.to_string()))?;
        self.checked.literals.push(LiteralSite {
            module: numeral.module,
            span: numeral.span,
            ty: symbol,
            value,
        });
        Ok(())
    }

    /// A binding settles what it can and leaves the rest to its definition,
    /// which may yet decide a numeral's type or a method's receiver.
    fn finish_binding(&mut self, marks: Marks) -> Result<(), CheckError> {
        for index in marks.numerals..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved || matches!(self.infer.resolve(&numeral.ty), Ty::Var(_)) {
                continue;
            }
            self.elaborate(&numeral)?;
            self.pending_numerals[index].resolved = true;
        }
        let closings = self.pending_closings.split_off(marks.closings);
        for closing in closings {
            self.close_rows(&closing.ty, closing.rows)
                .map_err(|message| failure(closing.module, closing.span, message))?;
        }
        Ok(())
    }

    /// The variables of a component's types that generalizing it will
    /// quantify: those nothing outside it holds.
    fn generic_variables(&self, types: &[Ty], names: &HashSet<Symbol>) -> HashSet<u32> {
        let mut generic: HashSet<u32> = types
            .iter()
            .flat_map(|ty| free_variables(&self.infer.resolve(ty)))
            .collect();
        for (name, scheme) in &self.values {
            if !names.contains(name) {
                for variable in free_scheme(scheme) {
                    generic.remove(&variable);
                }
            }
        }
        generic
    }

    /// Where every method a generic receiver could have shares a shape --
    /// every `mul` is `T T -> T`, every `equals` answers a `Bool` -- that
    /// shape is context for the call before any default: in
    /// `double(x) -> x.mul(2)` the `2` is whatever `x` is.
    fn link_shapes(&mut self, start: usize, generic: &HashSet<u32>) {
        for index in start..self.pending_methods.len() {
            let pending = self.pending_methods[index].clone();
            if pending.resolved || pending.reach != Reach::Called {
                continue;
            }
            let Ty::Var(receiver) = self.infer.resolve(&pending.receiver) else {
                continue;
            };
            if !generic.contains(&receiver) {
                continue;
            }
            let Some(implementations) = self.methods.get(&pending.name) else {
                continue;
            };
            let visible = &self.visible_methods[&pending.module];
            let shapes: Vec<_> = implementations
                .iter()
                .filter(|implementation| visible.contains(&implementation.target))
                .filter_map(|implementation| {
                    let mut trial = self.infer.clone();
                    match trial.instantiate(&implementation.scheme) {
                        Ty::Function(parameters, result)
                            if parameters.len() == pending.arguments.len() + 1 =>
                        {
                            let receiver = trial.resolve(&parameters[0]);
                            let shape = |ty: &Ty| {
                                let ty = trial.resolve(ty);
                                if ty == receiver {
                                    Some(None)
                                } else if free_variables(&ty).is_empty() {
                                    Some(Some(ty))
                                } else {
                                    None
                                }
                            };
                            Some((
                                parameters[1..].iter().map(shape).collect::<Vec<_>>(),
                                shape(&result),
                            ))
                        }
                        _ => None,
                    }
                })
                .collect();
            let Some((first_arguments, first_result)) = shapes.first().cloned() else {
                continue;
            };
            let shared = |position: &Option<Option<Ty>>, all: Vec<&Option<Option<Ty>>>| {
                position.is_some() && all.iter().all(|other| *other == position)
            };
            for (at, position) in first_arguments.iter().enumerate() {
                if shared(
                    position,
                    shapes.iter().map(|(arguments, _)| &arguments[at]).collect(),
                ) {
                    let linked = position.clone().flatten().unwrap_or(Ty::Var(receiver));
                    let _ = self.infer.unify(&pending.arguments[at], &linked);
                }
            }
            if shared(
                &first_result,
                shapes.iter().map(|(_, result)| result).collect(),
            ) {
                let linked = first_result.flatten().unwrap_or(Ty::Var(receiver));
                let _ = self.infer.unify(&pending.result, &linked);
            }
        }
    }

    /// A numeral of a generic type is built through that type's `of_nat`,
    /// and `neg` where it is negated, at each specialization: the component
    /// owes both as bounds, and the numeral waits for its type.
    fn defer_numeral(&mut self, numeral: &PendingNumeral) -> Result<(), CheckError> {
        let of_nat = self.method_symbol(numeral.module, numeral.span, "of_nat")?;
        let nat = Ty::Named(self.prelude.nat, Vec::new());
        self.pending_methods.push(PendingMethod {
            module: numeral.module,
            span: numeral.span,
            name: of_nat,
            receiver: numeral.ty.clone(),
            arguments: vec![nat],
            result: numeral.ty.clone(),
            reach: Reach::Type,
            resolved: false,
            obligation: true,
        });
        if numeral.negative {
            let neg = self.method_symbol(numeral.module, numeral.span, "neg")?;
            self.pending_methods.push(PendingMethod {
                module: numeral.module,
                span: numeral.span,
                name: neg,
                receiver: numeral.ty.clone(),
                arguments: Vec::new(),
                result: numeral.ty.clone(),
                reach: Reach::Called,
                resolved: false,
                obligation: true,
            });
        }
        self.deferred_numerals.push(DeferredNumeral {
            module: numeral.module,
            span: numeral.span,
            magnitude: numeral.magnitude.clone(),
            negative: numeral.negative,
        });
        Ok(())
    }

    /// What stays open on a component's generic variables after it is
    /// checked: each becomes a bound its definitions carry, and a call
    /// written through one is recorded as a call through a bound. The same
    /// member on the same variable twice is one bound, at one type.
    fn inferred_bounds(&mut self, marks: Marks) -> Result<Vec<Bound>, CheckError> {
        let mut bounds: Vec<Bound> = Vec::new();
        for index in marks.methods..self.pending_methods.len() {
            let pending = self.pending_methods[index].clone();
            if pending.resolved {
                continue;
            }
            let owner = self.infer.resolve(&pending.receiver);
            let mut parameters = pending.arguments.clone();
            if pending.reach != Reach::Type {
                parameters.insert(0, owner.clone());
            }
            let ty = Ty::Function(parameters, Box::new(pending.result.clone()));
            match bounds.iter().find(|bound| {
                bound.member == pending.name
                    && bound.associated == (pending.reach == Reach::Type)
                    && self.infer.resolve(&bound.owner) == owner
            }) {
                Some(existing) => {
                    let existing = existing.ty.clone();
                    self.unify_at(pending.module, pending.span, &ty, &existing)?;
                }
                None => bounds.push(Bound {
                    owner: owner.clone(),
                    member: pending.name,
                    ty,
                    associated: pending.reach == Reach::Type,
                }),
            }
            if !pending.obligation {
                self.bound_sites
                    .push((pending.module, pending.span, owner, pending.name));
            }
            self.pending_methods[index].resolved = true;
        }
        Ok(bounds)
    }

    /// Settle methods and claimed words together until neither moves: a
    /// method's answer can decide a word's position, and a word's reading
    /// a method's receiver.
    fn settle(&mut self, marks: Marks) -> Result<(), CheckError> {
        loop {
            self.settle_methods(marks.methods, false, &HashSet::new())?;
            if !self.settle_tags(marks.tags)? {
                return Ok(());
            }
        }
    }

    /// Give every pending word whose position has a type its reading there:
    /// a tag row takes the tag, anything else a declared constructor.
    /// Answers whether any did.
    fn settle_tags(&mut self, start: usize) -> Result<bool, CheckError> {
        let mut progress = self.settle_bare(false)?;
        for index in start..self.pending_tags.len() {
            if self.pending_tags[index].resolved {
                continue;
            }
            let pending = self.pending_tags[index].clone();
            match self.infer.resolve(&pending.result) {
                Ty::Var(_) => continue,
                Ty::Variants(tags, _) => {
                    let fields = pending.fields.clone().unwrap_or_default();
                    // Where the row already holds the tag, each field flows
                    // into what the row says it holds.
                    let fields = match tags
                        .iter()
                        .find(|(label, _)| *label == pending.dual.spelling)
                    {
                        Some((_, wanted)) if wanted.len() == fields.len() => {
                            for (at, (field, wanted)) in fields.iter().zip(wanted).enumerate() {
                                self.field_flows(&pending, at, field, wanted)?;
                            }
                            wanted.clone()
                        }
                        _ => fields,
                    };
                    let row = self.tag(pending.dual.spelling, fields);
                    self.unify_at(pending.module, pending.span, &pending.result, &row)?;
                    self.checked
                        .readings
                        .insert(pending.dual.site, Reading::Tag(pending.dual.spelling));
                }
                _ => self.settle_nominal(&pending)?,
            }
            self.pending_tags[index].resolved = true;
            progress = true;
        }
        Ok(progress)
    }

    /// Give each bare tag whose position has a type its reading there: a
    /// function's answer is the tag with the function's parameters as its
    /// fields, anything else the tag with none. Where nothing decided, and
    /// `default` says so, it is the tag with none.
    fn settle_bare(&mut self, default: bool) -> Result<bool, CheckError> {
        let mut progress = false;
        for index in 0..self.pending_bare.len() {
            let pending = self.pending_bare[index].clone();
            if pending.resolved {
                continue;
            }
            let wanted = match self.infer.resolve(&pending.ty) {
                Ty::Var(_) if !default => continue,
                Ty::Function(parameters, _) => {
                    let row = self.tag(pending.label, parameters.clone());
                    Ty::Function(parameters, Box::new(row))
                }
                _ => self.tag(pending.label, Vec::new()),
            };
            self.unify_at(pending.module, pending.span, &pending.ty, &wanted)?;
            self.pending_bare[index].resolved = true;
            progress = true;
        }
        Ok(progress)
    }

    /// Read a pending word as the declared constructor its position
    /// demands: its only claimant, or the one whose type the position has.
    fn settle_nominal(&mut self, pending: &PendingTag) -> Result<(), CheckError> {
        let chosen = match pending.dual.candidates.as_slice() {
            [only] => *only,
            candidates => {
                let head = match self.infer.resolve(&pending.result) {
                    Ty::Named(head, _) => Some(head),
                    Ty::Function(_, result) => match *result {
                        Ty::Named(head, _) => Some(head),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(head) = head else {
                    return Err(self.ambiguous(pending));
                };
                *candidates
                    .iter()
                    .find(|candidate| self.constructor_owner(**candidate) == Some(head))
                    .ok_or_else(|| {
                        failure(
                            pending.module,
                            pending.span,
                            format!(
                                "type `{}` has no constructor `{}`",
                                spelled(head, self.symbols),
                                self.symbols.text(pending.dual.spelling)
                            ),
                        )
                    })?
            }
        };
        if let Some(home) = pending.dual.home
            && home != chosen
        {
            let owner = self
                .constructor_owner(home)
                .map_or("", |owner| spelled(owner, self.symbols));
            let other = self
                .constructor_owner(chosen)
                .map_or("", |owner| spelled(owner, self.symbols));
            let word = self.symbols.text(pending.dual.spelling);
            return Err(failure(
                pending.module,
                pending.span,
                format!(
                    "inside `{owner}`'s block, the bare `{word}` reads as `{owner}`'s own constructor; this one is `{other}.{word}`, which is written qualified"
                ),
            ));
        }
        let scheme = self.constructors.get(&chosen).cloned().ok_or_else(|| {
            failure(
                pending.module,
                pending.span,
                "constructor has no declared type",
            )
        })?;
        let ty = self.infer.instantiate(&scheme);
        // Where the position already has a type, that the constructor
        // builds another is the whole of what is wrong.
        let builds = |checker: &mut Self, built: &Ty| {
            let wanted = checker.infer.resolve(&pending.result);
            checker.infer.unify(&pending.result, built).map_err(|_| {
                failure(
                    pending.module,
                    pending.span,
                    format!(
                        "`{}` builds {}, where {} is wanted",
                        checker.symbols.text(pending.dual.spelling),
                        show(&checker.infer.resolve(built), checker.symbols),
                        show(&wanted, checker.symbols)
                    ),
                )
            })
        };
        match &pending.fields {
            None => builds(self, &ty)?,
            Some(fields) => {
                let (parameters, result) = match ty {
                    Ty::Function(parameters, result) => (parameters, *result),
                    result => (Vec::new(), result),
                };
                if parameters.len() != fields.len() {
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "constructor `{}` takes {} fields, but is given {}",
                            self.symbols.text(pending.dual.spelling),
                            parameters.len(),
                            fields.len()
                        ),
                    ));
                }
                builds(self, &result)?;
                for (at, (field, parameter)) in fields.iter().zip(&parameters).enumerate() {
                    self.field_flows(pending, at, field, parameter)?;
                }
            }
        }
        self.checked
            .readings
            .insert(pending.dual.site, Reading::Constructor(chosen));
        Ok(())
    }

    /// The type a declared constructor builds.
    fn constructor_owner(&self, constructor: Symbol) -> Option<Symbol> {
        let scheme = self.constructors.get(&constructor)?;
        let result = match &scheme.ty {
            Ty::Function(_, result) => result.as_ref(),
            result => result,
        };
        match result {
            Ty::Named(owner, _) => Some(*owner),
            _ => None,
        }
    }

    /// The one honest ambiguity: several types claim the word, and nothing
    /// says which type its position has.
    fn ambiguous(&self, pending: &PendingTag) -> CheckError {
        let word = self.symbols.text(pending.dual.spelling);
        let readings: Vec<_> = pending
            .dual
            .candidates
            .iter()
            .filter_map(|candidate| self.constructor_owner(*candidate))
            .map(|owner| format!("`{}.{word}`", spelled(owner, self.symbols)))
            .collect();
        failure(
            pending.module,
            pending.span,
            format!(
                "constructor `{word}` is ambiguous here: nothing decides between {}; qualify it, or let a signature decide",
                readings.join(" and ")
            ),
        )
    }

    /// Resolve pending methods. On the final pass one still ambiguous is an
    /// error, except on a receiver in `generic`, which becomes a bound.
    fn settle_methods(
        &mut self,
        start: usize,
        final_pass: bool,
        generic: &HashSet<u32>,
    ) -> Result<(), CheckError> {
        let mut unresolved: Vec<_> = (start..self.pending_methods.len())
            .filter(|index| !self.pending_methods[*index].resolved)
            .collect();
        loop {
            let mut progress = false;
            let mut next = Vec::new();
            for index in unresolved {
                let pending = self.pending_methods[index].clone();
                let fields = self.field_candidates(&pending);
                if let [field] = fields.as_slice() {
                    self.apply_field(&pending, field)?;
                    self.pending_methods[index].resolved = true;
                    progress = true;
                    continue;
                }
                if fields.len() > 1 {
                    next.push(index);
                    continue;
                }
                match self.structural(&pending, final_pass)? {
                    Some(true) => {
                        self.pending_methods[index].resolved = true;
                        progress = true;
                        continue;
                    }
                    None => {
                        next.push(index);
                        continue;
                    }
                    Some(false) => {}
                }
                let owned = self.owned_methods(&pending);
                let candidates: Vec<_> = owned
                    .iter()
                    .filter(|implementation| self.fits(&pending, implementation))
                    .cloned()
                    .collect();
                match candidates.as_slice() {
                    // The one method the receiver has, with arguments it does
                    // not take: applying it says which argument is wrong.
                    [] if owned.len() == 1 => {
                        self.apply_method(&pending, &owned[0])?;
                        unreachable!("a method that does not fit fails to apply");
                    }
                    // A field of a receiver nothing else says anything of is
                    // a field of whatever record it turns out to be.
                    [] if pending.reach == Reach::Bare
                        && pending.arguments.is_empty()
                        && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_)) =>
                    {
                        if final_pass {
                            let projection = Self::projection(pending.name);
                            self.apply_field(&pending, &projection)?;
                            self.pending_methods[index].resolved = true;
                            progress = true;
                        } else {
                            next.push(index);
                        }
                    }
                    // A receiver not yet known may be one that has it, or a
                    // generic one owing it as a bound.
                    [] if match self.infer.resolve(&pending.receiver) {
                        Ty::Var(variable) => !final_pass || generic.contains(&variable),
                        _ => false,
                    } =>
                    {
                        next.push(index);
                    }
                    [] => {
                        return Err(failure(
                            pending.module,
                            pending.span,
                            format!(
                                "no type-compatible field or method `{}` is in scope",
                                self.symbols.text(pending.name)
                            ),
                        ));
                    }
                    [candidate] => {
                        self.apply_method(&pending, candidate)?;
                        self.pending_methods[index].resolved = true;
                        progress = true;
                    }
                    _ => next.push(index),
                }
            }
            if next.is_empty() {
                return Ok(());
            }
            if !progress {
                let waiting = next.iter().find(|index| {
                    !matches!(self.infer.resolve(&self.pending_methods[**index].receiver),
                        Ty::Var(variable) if generic.contains(&variable))
                });
                if final_pass && let Some(&index) = waiting {
                    let pending = &self.pending_methods[index];
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "method `{}` is ambiguous for the inferred receiver type",
                            self.symbols.text(pending.name)
                        ),
                    ));
                }
                return Ok(());
            }
            unresolved = next;
        }
    }

    fn field_candidates(&self, pending: &PendingMethod) -> Vec<Scheme> {
        if pending.reach != Reach::Bare || !pending.arguments.is_empty() {
            return Vec::new();
        }
        let receiver = self.infer.resolve(&pending.receiver);
        if let Ty::Record(..) = &receiver {
            return vec![Self::projection(pending.name)];
        }
        let Some(fields) = self.fields.get(&pending.name) else {
            return Vec::new();
        };
        fields
            .iter()
            .filter(|field| match &receiver {
                Ty::Named(owner, _) => field.owner == *owner,
                Ty::Var(_) => true,
                _ => false,
            })
            .filter(|field| {
                let mut trial = self.infer.clone();
                apply_signature(&mut trial, pending, &field.scheme, self.symbols).is_ok()
            })
            .map(|field| field.scheme.clone())
            .collect()
    }

    /// Reading field `name` of a record: `{name: t *} -> t`, which reads it
    /// from a record that has it and asks it of one that is open. Its two
    /// variables are the scheme's own, never linked, since a scheme is
    /// instantiated before it is used.
    fn projection(name: Symbol) -> Scheme {
        let (field, rest) = (u32::MAX, u32::MAX - 1);
        Scheme {
            variables: vec![field, rest],
            ty: Ty::Function(
                vec![Ty::Record(
                    vec![(name, Ty::Var(field))],
                    Some(Box::new(Ty::Var(rest))),
                )],
                Box::new(Ty::Var(field)),
            ),
        }
    }

    /// `equals` on a closed record or a tuple, and `cmp` on a tuple, which
    /// such values have with no declaration: each asks the same of every
    /// component, position by position for a tuple. A record has no `cmp`,
    /// having no order of its fields, and an open record has neither, its
    /// other fields being a caller's. Answers whether `pending` was one, or
    /// nothing while a record may yet be closed.
    fn structural(
        &mut self,
        pending: &PendingMethod,
        final_pass: bool,
    ) -> Result<Option<bool>, CheckError> {
        let receiver = self.infer.resolve(&pending.receiver);
        let components = match &receiver {
            Ty::Tuple(members) => members.clone(),
            Ty::Record(fields, _) => fields.iter().map(|(_, ty)| ty.clone()).collect(),
            _ => return Ok(Some(false)),
        };
        let spelled = self.symbols.text(pending.name);
        let answer = match (spelled, &receiver) {
            ("equals", _) => Ty::Named(self.prelude.bool_, Vec::new()),
            ("cmp", Ty::Tuple(_)) => Ty::Named(self.prelude.order, Vec::new()),
            _ => return Ok(Some(false)),
        };
        if let Ty::Record(_, Some(tail)) = &receiver {
            if !final_pass && matches!(**tail, Ty::Var(_)) {
                return Ok(None);
            }
            return Err(failure(
                pending.module,
                pending.span,
                "a record with `*` has no `equals`: its other fields are a caller's",
            ));
        }
        let [other] = pending.arguments.as_slice() else {
            return Ok(Some(false));
        };
        self.unify_at(pending.module, pending.span, other, &receiver)?;
        self.unify_at(pending.module, pending.span, &pending.result, &answer)?;
        for component in components {
            self.pending_methods.push(PendingMethod {
                module: pending.module,
                span: pending.span,
                name: pending.name,
                receiver: component.clone(),
                arguments: vec![component],
                result: answer.clone(),
                reach: Reach::Called,
                resolved: false,
                obligation: true,
            });
        }
        if !pending.obligation {
            self.checked.methods.push(MethodSite {
                module: pending.module,
                span: pending.span,
                target: pending.name,
            });
        }
        Ok(Some(true))
    }

    /// The visible methods named at `pending` that its receiver could have.
    fn owned_methods(&self, pending: &PendingMethod) -> Vec<MethodImpl> {
        let implementations = self.methods.get(&pending.name).cloned().unwrap_or_default();
        let receiver = self.infer.resolve(&pending.receiver);
        // A rigid receiver is a signed body's own variable: what it has is
        // what its bounds say. One not yet known may be such a variable too,
        // so a bound is as much a candidate for it as a declared method.
        let bounded = self
            .current
            .iter()
            .filter(|bound| {
                bound.member == pending.name
                    && bound.associated == (pending.reach == Reach::Type)
                    && match &receiver {
                        Ty::Rigid(_) => self.infer.resolve(&bound.owner) == receiver,
                        Ty::Var(_) => true,
                        _ => false,
                    }
            })
            .map(|bound| MethodImpl {
                owner: pending.name,
                target: pending.name,
                scheme: Scheme {
                    variables: Vec::new(),
                    ty: bound.ty.clone(),
                },
                bound: true,
            });
        if let Ty::Rigid(_) = receiver {
            return bounded.collect();
        }
        let visible = &self.visible_methods[&pending.module];
        implementations
            .iter()
            .filter(|implementation| visible.contains(&implementation.target))
            .filter(|implementation| match &receiver {
                Ty::Named(owner, _) => implementation.owner == *owner,
                Ty::Var(_) => true,
                _ => false,
            })
            .cloned()
            .chain(bounded)
            .collect()
    }

    /// Whether `implementation` takes the arguments given at `pending`.
    fn fits(&self, pending: &PendingMethod, implementation: &MethodImpl) -> bool {
        let mut trial = self.infer.clone();
        apply_signature(&mut trial, pending, &implementation.scheme, self.symbols).is_ok()
    }

    fn apply_field(&mut self, pending: &PendingMethod, scheme: &Scheme) -> Result<(), CheckError> {
        apply_signature(&mut self.infer, pending, scheme, self.symbols)
            .map_err(|message| failure(pending.module, pending.span, message))?;
        self.checked.projections.push(ProjectionSite {
            module: pending.module,
            span: pending.span,
            field: pending.name,
        });
        Ok(())
    }

    fn apply_method(
        &mut self,
        pending: &PendingMethod,
        implementation: &MethodImpl,
    ) -> Result<(), CheckError> {
        let replacements = apply_signature(
            &mut self.infer,
            pending,
            &implementation.scheme,
            self.symbols,
        )
        .map_err(|message| failure(pending.module, pending.span, message))?;
        // An obligation names nothing where it stands; a call through a
        // bound names its implementation only once it is specialized; a call
        // of an implementation owes that implementation's own bounds.
        if implementation.bound {
            if !pending.obligation {
                self.bound_sites.push((
                    pending.module,
                    pending.span,
                    pending.receiver.clone(),
                    pending.name,
                ));
            }
        } else {
            if !pending.obligation {
                self.checked.methods.push(MethodSite {
                    module: pending.module,
                    span: pending.span,
                    target: implementation.target,
                });
            }
            self.oblige(
                pending.module,
                pending.span,
                implementation.target,
                &replacements,
            );
        }
        Ok(())
    }

    fn method_symbol(
        &self,
        module: ModuleId,
        span: super::ast::Span,
        name: &str,
    ) -> Result<Symbol, CheckError> {
        self.symbols
            .find(name)
            .ok_or_else(|| failure(module, span, format!("no method `{name}` is in scope")))
    }

    fn unify_at(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        actual: &Ty,
        expected: &Ty,
    ) -> Result<(), CheckError> {
        self.infer.unify(actual, expected).map_err(|reason| {
            let message = match reason {
                // Which tag does not fit is the whole of it.
                Mismatch::NotAmong { .. } => reason.describe(self.symbols),
                _ => format!(
                    "type mismatch: {} and {} ({})",
                    show(&self.infer.resolve(actual), self.symbols),
                    show(&self.infer.resolve(expected), self.symbols),
                    reason.describe(self.symbols)
                ),
            };
            failure(module, span, message)
        })
    }

    const fn bool_type(&self) -> Ty {
        Ty::Named(self.prelude.bool_, Vec::new())
    }

    fn list_type(&self, element: Ty) -> Ty {
        Ty::Named(self.prelude.list, vec![element])
    }

    fn generalize(&self, ty: &Ty, excluded: Option<&HashSet<Symbol>>) -> Scheme {
        let ty = self.infer.resolve(ty);
        let mut variables: HashSet<_> = free_variables(&ty).into_iter().collect();
        for (name, scheme) in &self.values {
            if excluded.is_some_and(|excluded| excluded.contains(name)) {
                continue;
            }
            variables.retain(|variable| !free_scheme(scheme).contains(variable));
        }
        Scheme {
            variables: variables.into_iter().collect(),
            ty,
        }
    }

    fn generalize_local(&self, ty: &Ty, locals: &[Option<Scheme>], current: h::LocalId) -> Scheme {
        let ty = self.infer.resolve(ty);
        let mut variables: HashSet<_> = free_variables(&ty).into_iter().collect();
        for (index, scheme) in locals.iter().enumerate() {
            if index == current.index() {
                continue;
            }
            if let Some(scheme) = scheme {
                variables.retain(|variable| !free_scheme(scheme).contains(variable));
            }
        }
        for scheme in self.values.values() {
            variables.retain(|variable| !free_scheme(scheme).contains(variable));
        }
        // What a method, numeral or word still waiting will decide is not the
        // binding's to quantify.
        let waiting = self
            .pending_methods
            .iter()
            .filter(|pending| !pending.resolved)
            .flat_map(|pending| {
                std::iter::once(&pending.receiver)
                    .chain(&pending.arguments)
                    .chain(std::iter::once(&pending.result))
            })
            .chain(
                self.pending_numerals
                    .iter()
                    .filter(|numeral| !numeral.resolved)
                    .map(|numeral| &numeral.ty),
            )
            .chain(
                self.pending_tags
                    .iter()
                    .filter(|pending| !pending.resolved)
                    .map(|pending| &pending.result),
            )
            .chain(
                self.pending_bare
                    .iter()
                    .filter(|pending| !pending.resolved)
                    .map(|pending| &pending.ty),
            )
            .flat_map(|ty| free_variables(&self.infer.resolve(ty)));
        for variable in waiting {
            variables.remove(&variable);
        }
        Scheme {
            variables: variables.into_iter().collect(),
            ty,
        }
    }
}

/// Unify a field or method call with `scheme`. A mismatch says which
/// argument does not fit, as what was wanted and what was given.
fn apply_signature(
    infer: &mut Infer,
    pending: &PendingMethod,
    scheme: &Scheme,
    symbols: &Symbols,
) -> Result<HashMap<u32, Ty>, String> {
    let (instantiated, replacements) = infer.instantiated(scheme);
    let Ty::Function(parameters, result) = instantiated else {
        return Err("a method declaration is not a function".to_string());
    };
    // A member reached through its type takes no receiver; its answer is a
    // value of that type.
    let through_type = pending.reach == Reach::Type;
    let receiver = usize::from(!through_type);
    if parameters.len() != pending.arguments.len() + receiver {
        return Err(format!(
            "`{}` takes {} arguments, but {} were given",
            symbols.text(pending.name),
            parameters.len() - receiver,
            pending.arguments.len()
        ));
    }
    let given: Vec<&Ty> = if through_type {
        pending.arguments.iter().collect()
    } else {
        std::iter::once(&pending.receiver)
            .chain(&pending.arguments)
            .collect()
    };
    for (at, (argument, parameter)) in given.into_iter().zip(&parameters).enumerate() {
        let at = at + usize::from(through_type);
        infer.unify(argument, parameter).map_err(|_| {
            let which = if at == 0 {
                "the receiver".to_owned()
            } else {
                format!("argument {at}")
            };
            format!(
                "{which} of `{}` should be {}, but is {}",
                symbols.text(pending.name),
                show(&infer.resolve(parameter), symbols),
                show(&infer.resolve(argument), symbols)
            )
        })?;
    }
    let wanted = infer.resolve(&pending.result);
    infer
        .unify(&pending.result, &result)
        .map_err(|reason| match reason {
            Mismatch::NotAmong { .. } => reason.describe(symbols),
            _ => format!(
                "`{}` answers {}, where {} is wanted",
                symbols.text(pending.name),
                show(&infer.resolve(&result), symbols),
                show(&wanted, symbols)
            ),
        })?;
    Ok(replacements)
}

fn public_type(ty: &Ty) -> InferredType {
    match ty {
        Ty::Var(variable) => InferredType::Variable(TypeVariable {
            index: *variable,
            rigid: false,
        }),
        Ty::Rigid(variable) => InferredType::Variable(TypeVariable {
            index: *variable,
            rigid: true,
        }),
        Ty::Named(name, arguments) => {
            InferredType::Named(*name, arguments.iter().map(public_type).collect())
        }
        Ty::Function(parameters, result) => InferredType::Function(
            parameters.iter().map(public_type).collect(),
            Box::new(public_type(result)),
        ),
        Ty::Variants(tags, tail) => InferredType::Variants(
            tags.iter()
                .map(|(name, fields)| (*name, fields.iter().map(public_type).collect()))
                .collect(),
            tail.as_deref().map(|tail| Box::new(public_type(tail))),
        ),
        Ty::Record(fields, tail) => InferredType::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, public_type(ty)))
                .collect(),
            tail.as_deref().map(|tail| Box::new(public_type(tail))),
        ),
        Ty::Tuple(members) => InferredType::Tuple(members.iter().map(public_type).collect()),
    }
}

fn free_variables(ty: &Ty) -> Vec<u32> {
    fn collect(ty: &Ty, output: &mut Vec<u32>) {
        match ty {
            Ty::Var(variable) => {
                if !output.contains(variable) {
                    output.push(*variable);
                }
            }
            Ty::Rigid(_) => {}
            Ty::Named(_, arguments) => {
                for ty in arguments {
                    collect(ty, output);
                }
            }
            Ty::Function(parameters, result) => {
                for ty in parameters {
                    collect(ty, output);
                }
                collect(result, output);
            }
            Ty::Variants(tags, tail) => {
                for (_, fields) in tags {
                    for ty in fields {
                        collect(ty, output);
                    }
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Record(fields, tail) => {
                for (_, ty) in fields {
                    collect(ty, output);
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Tuple(members) => {
                for ty in members {
                    collect(ty, output);
                }
            }
        }
    }
    let mut output = Vec::new();
    collect(ty, &mut output);
    output
}

fn free_scheme(scheme: &Scheme) -> HashSet<u32> {
    free_variables(&scheme.ty)
        .into_iter()
        .filter(|variable| !scheme.variables.contains(variable))
        .collect()
}

fn validate_effects(program: &h::Program, symbols: &Symbols) -> Result<(), CheckError> {
    for module in &program.modules {
        for item in &module.items {
            match item {
                h::Item::Clause(clause) => validate_effect_clause(module.source, clause, symbols)?,
                h::Item::Data(data) => {
                    for method in &data.methods {
                        if let h::MethodItem::Clause(clause) = method {
                            validate_effect_clause(module.source, clause, symbols)?;
                        }
                    }
                }
                h::Item::Signature(_) => {}
            }
        }
    }
    Ok(())
}

fn validate_effect_clause(
    module: ModuleId,
    clause: &h::Clause,
    symbols: &Symbols,
) -> Result<(), CheckError> {
    let effectful = symbols.text(clause.name).ends_with('!');
    if let Some(guard) = &clause.guard {
        validate_effect_expr(module, guard, effectful, false, symbols)?;
    }
    for binding in &clause.body.bindings {
        validate_effect_expr(module, &binding.value, effectful, true, symbols)?;
    }
    validate_effect_expr(module, &clause.body.result, effectful, true, symbols)
}

fn validate_effect_expr(
    module: ModuleId,
    expression: &h::Expr,
    owner_effectful: bool,
    stands_alone: bool,
    symbols: &Symbols,
) -> Result<(), CheckError> {
    match &expression.kind {
        h::ExprKind::Global(name) if symbols.text(*name).ends_with('!') => Err(failure(
            module,
            expression.span,
            format!(
                "effect `{}` must be called and stand on its own",
                source_name(symbols, *name)
            ),
        )),
        // What `?` propagates stands where the `?` does.
        h::ExprKind::Try(value) => {
            validate_effect_expr(module, value, owner_effectful, stands_alone, symbols)
        }
        h::ExprKind::Call(head, arguments) => {
            let effect = match &head.kind {
                h::ExprKind::Global(name) if symbols.text(*name).ends_with('!') => Some(*name),
                _ => None,
            };
            if let Some(effect) = effect {
                validate_effect_call(
                    module,
                    expression.span,
                    effect,
                    owner_effectful,
                    stands_alone,
                    symbols,
                )?;
            } else {
                validate_effect_expr(module, head, owner_effectful, false, symbols)?;
            }
            for argument in arguments {
                validate_effect_expr(module, argument, owner_effectful, false, symbols)?;
            }
            Ok(())
        }
        h::ExprKind::Member(receiver, name) => {
            if symbols.text(*name).ends_with('!') {
                validate_effect_call(
                    module,
                    expression.span,
                    *name,
                    owner_effectful,
                    stands_alone,
                    symbols,
                )?;
            }
            validate_effect_expr(module, receiver, owner_effectful, false, symbols)
        }
        h::ExprKind::Method(receiver, name, arguments) => {
            if symbols.text(*name).ends_with('!') {
                validate_effect_call(
                    module,
                    expression.span,
                    *name,
                    owner_effectful,
                    stands_alone,
                    symbols,
                )?;
            }
            validate_effect_expr(module, receiver, owner_effectful, false, symbols)?;
            for argument in arguments {
                validate_effect_expr(module, argument, owner_effectful, false, symbols)?;
            }
            Ok(())
        }
        h::ExprKind::String(parts) => parts.iter().try_for_each(|part| match part {
            h::StringPart::Text(_) => Ok(()),
            h::StringPart::Splice(expression) => {
                validate_effect_expr(module, expression, owner_effectful, false, symbols)
            }
        }),
        h::ExprKind::List(elements, rest) => {
            for element in elements {
                validate_effect_expr(module, element, owner_effectful, false, symbols)?;
            }
            if let Some(rest) = rest {
                validate_effect_expr(module, rest, owner_effectful, false, symbols)?;
            }
            Ok(())
        }
        h::ExprKind::Record(fields) => fields.iter().try_for_each(|(_, value)| {
            validate_effect_expr(module, value, owner_effectful, false, symbols)
        }),
        h::ExprKind::Update(base, fields) => {
            validate_effect_expr(module, base, owner_effectful, false, symbols)?;
            fields.iter().try_for_each(|(_, value)| {
                validate_effect_expr(module, value, owner_effectful, false, symbols)
            })
        }
        h::ExprKind::Tuple(members) => members.iter().try_for_each(|member| {
            validate_effect_expr(module, member, owner_effectful, false, symbols)
        }),
        h::ExprKind::Lambda(_, body) => validate_effect_expr(module, body, false, false, symbols),
        h::ExprKind::Unary(_, value) => {
            validate_effect_expr(module, value, owner_effectful, false, symbols)
        }
        h::ExprKind::Binary(_, left, right) => {
            validate_effect_expr(module, left, owner_effectful, false, symbols)?;
            validate_effect_expr(module, right, owner_effectful, false, symbols)
        }
        h::ExprKind::Local(_)
        | h::ExprKind::Global(_)
        | h::ExprKind::Constructor(_)
        | h::ExprKind::Tag(_)
        | h::ExprKind::Dual(_)
        | h::ExprKind::Associated(..)
        | h::ExprKind::Number(_) => Ok(()),
    }
}

fn validate_effect_call(
    module: ModuleId,
    span: super::ast::Span,
    effect: Symbol,
    owner_effectful: bool,
    stands_alone: bool,
    symbols: &Symbols,
) -> Result<(), CheckError> {
    if !owner_effectful {
        return Err(failure(
            module,
            span,
            format!(
                "pure definitions cannot call effect `{}`",
                source_name(symbols, effect)
            ),
        ));
    }
    if !stands_alone {
        return Err(failure(
            module,
            span,
            format!(
                "effect `{}` must stand on its own",
                source_name(symbols, effect)
            ),
        ));
    }
    Ok(())
}

fn source_name(symbols: &Symbols, symbol: Symbol) -> &str {
    symbols
        .text(symbol)
        .rsplit("$$")
        .next()
        .expect("split always has one item")
        .rsplit('.')
        .next()
        .expect("split always has one item")
}

fn definitions(program: &h::Program) -> HashMap<Symbol, Vec<(ModuleId, &h::Clause)>> {
    let mut definitions: HashMap<_, Vec<_>> = HashMap::new();
    for module in &program.modules {
        for item in &module.items {
            match item {
                h::Item::Clause(clause) => {
                    definitions
                        .entry(clause.name)
                        .or_default()
                        .push((module.source, clause));
                }
                h::Item::Data(data) => {
                    for method in &data.methods {
                        if let h::MethodItem::Clause(clause) = method {
                            definitions
                                .entry(clause.name)
                                .or_default()
                                .push((module.source, clause));
                        }
                    }
                }
                h::Item::Signature(_) => {}
            }
        }
    }
    definitions
}

fn graph_visit(node: usize, edges: &[Vec<usize>], seen: &mut [bool], order: &mut Vec<usize>) {
    if std::mem::replace(&mut seen[node], true) {
        return;
    }
    for &next in &edges[node] {
        graph_visit(next, edges, seen, order);
    }
    order.push(node);
}

fn graph_gather(node: usize, edges: &[Vec<usize>], seen: &mut [bool], output: &mut Vec<usize>) {
    if std::mem::replace(&mut seen[node], true) {
        return;
    }
    output.push(node);
    for &next in &edges[node] {
        graph_gather(next, edges, seen, output);
    }
}

fn components(
    definitions: &HashMap<Symbol, Vec<(ModuleId, &h::Clause)>>,
    unsigned: &HashSet<Symbol>,
) -> Vec<Vec<Symbol>> {
    let names: Vec<_> = unsigned.iter().copied().collect();
    let index: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(index, name)| (*name, index))
        .collect();
    let mut edges = vec![Vec::new(); names.len()];
    for (name, &from) in &index {
        let mut dependencies = HashSet::new();
        for (_, clause) in &definitions[name] {
            clause_globals(clause, &mut dependencies);
        }
        edges[from].extend(
            dependencies
                .into_iter()
                .filter_map(|dependency| index.get(&dependency).copied()),
        );
    }
    let mut reverse = vec![Vec::new(); names.len()];
    for (from, targets) in edges.iter().enumerate() {
        for target in targets {
            reverse[*target].push(from);
        }
    }
    let mut order = Vec::new();
    let mut seen = vec![false; names.len()];
    for node in 0..names.len() {
        graph_visit(node, &edges, &mut seen, &mut order);
    }
    seen.fill(false);
    let mut result = Vec::new();
    while let Some(node) = order.pop() {
        if seen[node] {
            continue;
        }
        let mut component = Vec::new();
        graph_gather(node, &reverse, &mut seen, &mut component);
        result.push(component.into_iter().map(|index| names[index]).collect());
    }
    result.reverse();
    result
}

fn clause_globals(clause: &h::Clause, output: &mut HashSet<Symbol>) {
    if let Some(guard) = &clause.guard {
        expr_globals(guard, output);
    }
    for binding in &clause.body.bindings {
        expr_globals(&binding.value, output);
    }
    expr_globals(&clause.body.result, output);
}

fn expr_globals(expression: &h::Expr, output: &mut HashSet<Symbol>) {
    match &expression.kind {
        h::ExprKind::Global(global) => {
            output.insert(*global);
        }
        h::ExprKind::String(parts) => {
            for part in parts {
                if let h::StringPart::Splice(expression) = part {
                    expr_globals(expression, output);
                }
            }
        }
        h::ExprKind::List(elements, rest) => {
            for expression in elements {
                expr_globals(expression, output);
            }
            if let Some(rest) = rest {
                expr_globals(rest, output);
            }
        }
        h::ExprKind::Record(fields) => {
            for (_, value) in fields {
                expr_globals(value, output);
            }
        }
        h::ExprKind::Update(base, fields) => {
            expr_globals(base, output);
            for (_, value) in fields {
                expr_globals(value, output);
            }
        }
        h::ExprKind::Tuple(members) => {
            for member in members {
                expr_globals(member, output);
            }
        }
        h::ExprKind::Lambda(_, body) | h::ExprKind::Unary(_, body) | h::ExprKind::Try(body) => {
            expr_globals(body, output);
        }
        h::ExprKind::Call(head, arguments) | h::ExprKind::Method(head, _, arguments) => {
            expr_globals(head, output);
            for argument in arguments {
                expr_globals(argument, output);
            }
        }
        h::ExprKind::Member(head, _) => expr_globals(head, output),
        h::ExprKind::Binary(_, left, right) => {
            expr_globals(left, output);
            expr_globals(right, output);
        }
        h::ExprKind::Local(_)
        | h::ExprKind::Constructor(_)
        | h::ExprKind::Tag(_)
        | h::ExprKind::Dual(_)
        | h::ExprKind::Associated(..)
        | h::ExprKind::Number(_) => {}
    }
}

fn collect_pattern_locals(pattern: &h::Pattern, output: &mut Vec<h::LocalId>) {
    match pattern {
        h::Pattern::Bind(local) => output.push(*local),
        h::Pattern::Constructor(_, fields)
        | h::Pattern::Tag(_, fields)
        | h::Pattern::Dual(_, fields)
        | h::Pattern::List(fields, None) => {
            for field in fields {
                collect_pattern_locals(field, output);
            }
        }
        h::Pattern::List(fields, rest) => {
            for field in fields {
                collect_pattern_locals(field, output);
            }
            if let Some(rest) = rest {
                collect_pattern_locals(rest, output);
            }
        }
        h::Pattern::Record(fields, _) => {
            for (_, pattern) in fields {
                collect_pattern_locals(pattern, output);
            }
        }
        h::Pattern::Tuple(members) => {
            for member in members {
                collect_pattern_locals(member, output);
            }
        }
        h::Pattern::Wild
        | h::Pattern::Number { .. }
        | h::Pattern::Range(..)
        | h::Pattern::String(_) => {}
    }
}

fn component_name_set(monotypes: &HashMap<Symbol, Ty>) -> HashSet<Symbol> {
    monotypes.keys().copied().collect()
}

/// A name as the program wrote it: resolution prefixes a global with the
/// module it belongs to, separated by `$$`.
fn spelled(name: Symbol, symbols: &Symbols) -> &str {
    let canonical = symbols.text(name);
    canonical
        .rsplit_once("$$")
        .map_or(canonical, |(_, spelling)| spelling)
}

fn show(ty: &Ty, symbols: &Symbols) -> String {
    match ty {
        Ty::Var(variable) => format!("?{variable}"),
        Ty::Rigid(variable) => format!("'a{variable}"),
        Ty::Named(name, arguments) if arguments.is_empty() => spelled(*name, symbols).to_owned(),
        Ty::Named(name, arguments) => format!(
            "{}({})",
            spelled(*name, symbols),
            arguments
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Ty::Function(parameters, result) => format!(
            "{} -> {}",
            parameters
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(" "),
            show(result, symbols)
        ),
        // An open row shows its rest as `*`: the tags a caller may add.
        Ty::Variants(tags, tail) => {
            let mut shown: Vec<_> = tags
                .iter()
                .map(|(name, fields)| {
                    if fields.is_empty() {
                        spelled(*name, symbols).to_owned()
                    } else {
                        let fields: Vec<_> = fields.iter().map(|ty| show(ty, symbols)).collect();
                        format!("{}({})", spelled(*name, symbols), fields.join(" "))
                    }
                })
                .collect();
            // A rigid rest is a caller's: where it shows, in the body it
            // belongs to, the row is exactly its tags.
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("[{}]", shown.join(" "))
        }
        Ty::Record(fields, tail) => {
            let mut shown: Vec<_> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", symbols.text(*name), show(ty, symbols)))
                .collect();
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("{{{}}}", shown.join(" "))
        }
        Ty::Tuple(members) => format!(
            "({})",
            members
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

/// Where the `to_str` a splice is read through is recorded: before the
/// splice, empty, which no expression's place is, so it cannot be taken
/// for a method call written as the splice itself.
pub(crate) const fn splice_site(splice: super::ast::Span) -> super::ast::Span {
    super::ast::Span {
        start: splice.start,
        end: splice.start,
    }
}

fn failure(module: ModuleId, span: super::ast::Span, message: impl Into<String>) -> CheckError {
    CheckError {
        module,
        span,
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{blessed::PreludeIds, modules, resolve};
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let root = std::env::temp_dir().join(format!("faun-check-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).unwrap();
            path
        }

        fn load(&self, entry_source: &str) -> (PreludeIds, ResolvedProgram) {
            self.write("bool.fn", "exports {Bool.*}\nBool : [False True].(not : Bool -> Bool not(False) -> True not(True) -> False and : Bool Bool -> Bool and(True True) -> True and(_ _) -> False)\n");
            self.write("nat.fn", "exports {Nat.*}\nNat : [Zero Succ(Nat)].(add : Nat Nat -> Nat add(0 y) -> y add(Succ(n) y) -> Succ(n.add(y)))\n");
            self.write(
                "int.fn",
                "exports {Int.*}\nInt : [Pos(Nat) NegSucc(Nat)].(of_nat : Nat -> Int of_nat(n) -> Pos(n) neg : Int -> Int neg(i) -> i)\n",
            );
            self.write("u8.fn", "exports {U8}\nU8 : Nat\n");
            self.write(
                "list.fn",
                "exports {List.*}\nList(a) : [Nil Cons(a List(a))]\n",
            );
            self.write(
                "str.fn",
                "exports {Str}\nStr : List(U8).(concat : Str Str -> Str concat(left _) -> left equals : Str Str -> Bool equals(_ _) -> False)\n",
            );
            self.write(
                "result.fn",
                "exports {Result.*}\nResult(a e) : [Ok(a) Err(e)]\n",
            );
            self.write(
            "order.fn",
            "exports {Order.*}\nOrder : [Lt Eq Gt].(lt : Order -> Bool lt(Lt) -> True lt(_) -> False le : Order -> Bool le(Gt) -> False le(_) -> True gt : Order -> Bool gt(Gt) -> True gt(_) -> False ge : Order -> Bool ge(Lt) -> False ge(_) -> True then : Order Order -> Order then(Eq next) -> next then(decided _) -> decided)\n",
        );
            let standard = self.write(
                "standard.fn",
                "package {}\nimport bool {Bool.*}\nimport order {Order.*}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport result {Result.*}\nimport str {Str}\nexports {Bool.* Order.* Nat.* Int.* U8 List.* Result.* Str}\n",
            );
            let entry = self.write("main.fn", entry_source);
            let host = self.write("host.fn", "exports {Host}\nHost : {argc: Nat}\n");
            let loaded = modules::load_program(&entry, &standard, &host).unwrap();
            let prelude = PreludeIds::find_in(&loaded).unwrap();
            let resolved = resolve::resolve_names(loaded).unwrap();
            (prelude, resolved)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn context_selects_nat_int_and_str_elaboration() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "natural : Nat\nnatural() -> 42\ninteger : Int\ninteger() -> -42\ntext : Str\ntext() -> \"é\"\n",
        );
        let checked = type_check(resolved, prelude.clone()).unwrap();
        let entry = checked.resolved.program.modules.last().unwrap().source;
        let entry_sites: Vec<_> = checked
            .types
            .literals
            .iter()
            .filter(|site| site.module == entry)
            .collect();
        assert_eq!(entry_sites.len(), 3);
        assert!(entry_sites.iter().any(|site| site.ty == prelude.str_));
        assert!(entry_sites.iter().any(|site| site.ty == prelude.nat));
        assert!(entry_sites.iter().any(|site| site.ty == prelude.int));
    }

    #[test]
    fn never_is_an_ordinary_constructor_name() {
        let fixture = Fixture::new();
        let (prelude, resolved) =
            fixture.load("Outcome : [Never]\nvalue : Outcome\nvalue() -> Never\n");
        type_check(resolved, prelude).unwrap();
    }

    #[test]
    fn polymorphic_functions_are_instantiated_at_each_call() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "id : a -> a\nid(x) -> x\nnatural : Nat\nnatural() -> id(1)\ninteger : Int\ninteger() -> id(-1)\n",
        );
        let id = resolved
            .program
            .modules
            .last()
            .unwrap()
            .items
            .iter()
            .find_map(|item| {
                if let h::Item::Signature(signature) = item {
                    Some(signature.name)
                } else {
                    None
                }
            })
            .unwrap();
        let checked = type_check(resolved, prelude).unwrap();
        let scheme = &checked.types.values[&id];
        assert_eq!(scheme.variables.len(), 1);
        let InferredType::Function(parameters, result) = &scheme.ty else {
            panic!("id function type")
        };
        assert_eq!(parameters, std::slice::from_ref(result.as_ref()));
    }

    #[test]
    fn a_polymorphic_signature_cannot_be_implemented_by_one_concrete_type() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("constant : a -> a\nconstant(_) -> 1\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(failure.message.contains("numeral") || failure.message.contains("mismatch"));
    }

    #[test]
    fn unsigned_definitions_are_generalized_between_components() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "id(x) -> x\nnatural : Nat\nnatural() -> id(1)\ninteger : Int\ninteger() -> id(-1)\n",
        );
        type_check(resolved, prelude).unwrap();
    }

    /// A function is passed into a call; bound to a name, it would be a
    /// value a program holds.
    #[test]
    fn a_function_is_not_bound() {
        let fixture = Fixture::new();
        let (prelude, resolved) =
            fixture.load("id : a -> a\nid(x) -> x\nlocal : Int\nlocal() ->\n  f = id\n  f(-1)\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(
            failure.message.contains("cannot be bound"),
            "{}",
            failure.message
        );
    }

    #[test]
    fn receiver_type_selects_a_method() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "increment : Nat -> Nat\nincrement(n) -> n.add(1)\ntruth : Bool -> Bool\ntruth(b) -> b.not()\n",
        );
        let checked = type_check(resolved, prelude.clone()).unwrap();
        let targets: Vec<_> = checked
            .types
            .methods
            .iter()
            .map(|site| site.target)
            .collect();
        assert!(targets.contains(&prelude.bool_not));
        assert!(
            targets.iter().any(|target| checked
                .resolved
                .symbols
                .text(*target)
                .ends_with("Nat.add"))
        );
    }

    /// A method several types have, called on a value nothing else says the
    /// type of, is a bound the definition carries: `flip` is generic over
    /// every type with a `not`.
    #[test]
    fn a_method_several_types_have_is_a_bound() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "Flip : [Off On].(not : Flip -> Flip not(Off) -> On not(On) -> Off)\nflip(x) -> x.not()\n",
        );
        let checked = type_check(resolved, prelude).unwrap();
        let resolved = &checked.resolved;
        let scheme = checked
            .types
            .values
            .iter()
            .find(|(name, _)| resolved.symbols.text(**name).ends_with("$$flip"))
            .map(|(_, scheme)| scheme)
            .unwrap();
        assert_eq!(scheme.bounds.len(), 1);
        assert_eq!(resolved.symbols.text(scheme.bounds[0].member), "not");
    }

    #[test]
    fn methods_of_unexposed_types_are_not_candidates() {
        let fixture = Fixture::new();
        fixture.write(
            "hidden.fn",
            "exports {helper}\nSecret : [Hidden].(not : Secret -> Secret not(Hidden) -> Hidden)\nhelper : Nat\nhelper() -> 0\n",
        );
        let (prelude, resolved) = fixture.load("import hidden {helper}\nchoose(x) -> x.not()\n");
        let checked = type_check(resolved, prelude.clone()).unwrap();
        assert!(
            checked
                .types
                .methods
                .iter()
                .any(|site| site.target == prelude.bool_not)
        );
    }

    #[test]
    fn repository_bootstrap_checks_polymorphic_utilities() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/utilities.fn");
        let loaded = modules::load_program(&entry, &root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = resolve::resolve_names(loaded).unwrap();
        let checked = type_check(resolved, prelude).unwrap();
        assert!(!checked.types.methods.is_empty());
    }

    #[test]
    fn repository_bootstrap_exposes_arithmetic_for_nat_int_and_u8() {
        let fixture = Fixture::new();
        let entry = fixture.write(
            "arithmetic.fn",
            "nat_ops : Nat Nat -> Nat\n\
             nat_ops(a b) -> ((((a + b) - b) * b) / b) % b\n\
             int_ops : Int Int -> Int\n\
             int_ops(a b) -> ((((a + b) - b) * b) / b) % b\n\
             u8_ops : U8 U8 -> U8\n\
             u8_ops(a b) -> ((((a + b) - b) * b) / b) % b\n",
        );
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
        let loaded = modules::load_program(&entry, &root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = resolve::resolve_names(loaded).unwrap();
        let checked = type_check(resolved, prelude).unwrap();
        let methods: HashSet<_> = checked
            .types
            .methods
            .iter()
            .map(|site| checked.resolved.symbols.text(site.target))
            .collect();
        for ty in ["Nat", "Int", "U8"] {
            for operation in ["add", "sub", "mul", "div", "mod"] {
                assert!(
                    methods
                        .iter()
                        .any(|name| name.ends_with(&format!("{ty}.{operation}"))),
                    "missing {ty}.{operation}"
                );
            }
        }
    }

    #[test]
    fn pure_definitions_and_nested_expressions_cannot_hide_effects() {
        let fixture = Fixture::new();
        let (prelude, resolved) =
            fixture.load("stop! : Nat -> Nat\nbad : Nat\nbad() -> stop!(0)\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(
            failure
                .message
                .contains("pure definitions cannot call effect")
        );

        let (prelude, resolved) = fixture.load(
            "stop! : Nat -> Nat\nid : Nat -> Nat\nid(n) -> n\nbad! : Nat\nbad!() -> id(stop!(0))\n",
        );
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(failure.message.contains("must stand on its own"));
    }

    /// A constructor handed where its position wants another type says what
    /// it builds and what is wanted, rather than that there is no method.
    #[test]
    fn a_constructor_where_another_type_is_wanted_says_both() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad() -> Zero.add(True)\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert_eq!(failure.message, "`True` builds Bool, where Nat is wanted");
    }

    #[test]
    fn a_negative_nat_is_rejected() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad() -> -1\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(failure.message.contains("negative numeral"));
    }
}
