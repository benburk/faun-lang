//! Polymorphic type inference and receiver-directed method resolution.
//!
//! Explicit signatures are universally quantified. Unsigned definitions use
//! Algorithm W over call-graph components, keeping recursive groups
//! monomorphic until the whole group has been checked. Method calls are held
//! until ordinary unification (and numeral defaulting) identifies a receiver.
//! A bodyless `equals`, `cmp` or `to_str` in a type's block has its clauses
//! written first (`derive`), and is checked as a written body is.
//!
//! Tag rows unify as Rémy's rows: shared tags unify their fields and an open
//! side's tail takes what only the other holds. A signature's result rows get
//! a tail its scheme quantifies; skolemized for the body, that tail is rigid,
//! so the body answers only the written tags and callers may widen them. A
//! closed row answered where such a row is wanted is subsumed, and the
//! expression is recorded as widened; what an answer or a `?` waits on is
//! settled first, so a row a call or a field hands back meets it as its own. Clauses taking a row apart without a
//! catch-all close it. A word a declaration claims waits, as a method does,
//! for its position's type to choose between the tag and the constructor.
//!
//! `where` bounds are structural. A signed body meets its written bounds at
//! its rigid variables; a use of a bounded definition owes its bounds, met
//! where the use's types are known or owed in turn. An unsigned component's
//! methods still open on a variable it generalizes become its bounds, as do
//! its field reads off one, met by a record or a declared type having the
//! field, and its numerals of a generic type, through `of_nat`.
//! Specialization calls each concrete type's own member, or reads its field.

#![allow(clippy::too_many_lines)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use super::blessed::{self, LiteralExpr, NumeralType, PreludeIds};
use super::diagnostic::{Advice, Advised, Diagnostic};
use super::hir as h;
use super::resolve::ResolvedProgram;
use super::{ModuleId, Symbol, Symbols};
use crate::declarations as n;

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
    /// Named on a value with no call, `x.name`: met by a field of that
    /// name where the owner has one, and otherwise by a method taking
    /// nothing else.
    pub bare: bool,
}

/// Typed HIR and its source owners; inference's temporary tables are gone.
#[derive(Clone, Debug)]
pub struct CheckedProgram {
    pub resolved: ResolvedProgram<crate::typed::Program>,
    /// The standard identities its literals and patterns were checked against.
    pub prelude: PreludeIds,
}

/// Which reading a word some declaration claims took, by its site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reading {
    /// The declared constructor its position demanded, or its one declared
    /// reading, where nothing decided.
    Constructor(Symbol),
    /// The structural tag it spells, where its position is a tag row.
    Tag(Symbol),
}

// Inference's temporary facts. Finishing checking consumes these into typed HIR;
// no downstream pass joins syntax to side tables.
#[derive(Default)]
struct Facts {
    values: HashMap<Symbol, InferredScheme>,
    expressions: HashMap<h::SiteId, InferredType>,
    clauses: HashMap<h::SiteId, (crate::typed::Signature, Vec<InferredBound>)>,
    literals: HashMap<h::SiteId, LiteralExpr>,
    methods: HashMap<h::SiteId, Symbol>,
    projections: HashMap<h::SiteId, Symbol>,
    widenings: HashMap<h::SiteId, InferredType>,
    readings: HashMap<h::SiteId, Reading>,
    bound_sites: HashMap<h::SiteId, (InferredType, Symbol)>,
    deferred_numerals: HashMap<h::SiteId, crate::typed::Numeral>,
    /// Each method written without a signature, by its owner and spelling,
    /// as a signature names a signed one's.
    unsigned_members: HashMap<(Symbol, Symbol), Symbol>,
}

mod elaborate;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub message: String,
    pub advice: Advice,
}

impl Advised for CheckError {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
}

impl CheckError {
    /// Told as a diagnostic, at its place in `resolved`'s sources.
    pub(crate) fn told<P>(self, resolved: &ResolvedProgram<P>) -> Diagnostic {
        let diagnostic = resolved.diagnostic(self.module, self.span, self.message);
        diagnostic.advised(self.advice)
    }
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
/// after the group closes. Consume resolved syntax into typed HIR, with each
/// elaboration decision on its expression. `where` calls remain explicit until
/// specialization selects their concrete implementations.
///
/// # Errors
///
/// Reports type, arity, ambiguous-method, unsupported-constraint, and literal
/// protocol failures, and clauses that leave a case unmatched.
pub fn type_check(
    mut resolved: ResolvedProgram<n::Program>,
    prelude: PreludeIds,
) -> Result<CheckedProgram, Diagnostic> {
    crate::derive::requested(&mut resolved, &prelude)?;
    let facts = validate_effects(&resolved.program, &resolved.symbols)
        .and_then(|()| {
            Checker::new(&resolved.program, &resolved.symbols, &prelude)?.check(&resolved.program)
        })
        .map_err(|error| error.told(&resolved))?;
    let resolved =
        resolved.map(|program, sites| elaborate::finish(program, facts, &prelude, sites));
    crate::exhaustive::exhaustive(&resolved.program, &resolved.symbols, &prelude)
        .map_err(|error| error.told(&resolved))?;
    Ok(CheckedProgram { resolved, prelude })
}

/// Validate the selected host ABI and the application's `main!` signature.
///
/// # Errors
///
/// Rejects host declarations or an entry whose checked type differs from the
/// canonical `Host` and `U8` identities or the structural empty variant type.
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
        .functions
        .iter()
        .find(|function| function.name == main.symbol)
        .map_or_else(super::ast::Span::default, |function| function.span);
    // `Host` wraps the record of startup values its target produces.
    let carries = resolved
        .program
        .data
        .get(&host.host)
        .and_then(|data| data.wrapper.as_ref());
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
                    InferredType::Named(checked.prelude.u8_, Vec::new()),
                ],
                Box::new(InferredType::Variants(Vec::new(), None)),
            ),
            "exit! : (Host, U8) -> []",
        ),
    ] {
        let Some(function) = resolved
            .program
            .functions
            .iter()
            .find(|function| function.name == name)
        else {
            return Err(failure(
                module,
                span,
                &format!("the application ABI requires `{written}`"),
            ));
        };
        if !function.scheme.variables.is_empty() || function.scheme.ty != expected {
            return Err(failure(
                module,
                span,
                &format!("the application ABI requires `{written}`"),
            ));
        }
    }
    Ok(())
}

/// A type as inference holds it. Its parts are shared, not owned: cloning
/// one is a count, not a copy, and resolving one rebuilds only the parts a
/// binding changed.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Var(u32),
    Rigid(u32),
    Named(Symbol, Rc<[Self]>),
    Function(Rc<[Self]>, Rc<Self>),
    /// A tag row: the tags it holds, and where it is open, a tail standing
    /// for the rest. A tail is a variable, which unification may widen, or
    /// rigid: a signed definition's own result row, which its body may not
    /// widen and each caller may.
    Variants(Rc<[(Symbol, Rc<[Self]>)]>, Option<Rc<Self>>),
    /// A record's fields, in one order, and where it is open, a tail
    /// standing for the fields a caller's record has besides.
    Record(Rc<[(Symbol, Self)]>, Option<Rc<Self>>),
    /// A positional product of two or more, which never unifies with a
    /// record.
    Tuple(Rc<[Self]>),
}

/// Something a type holds a list of: a type, or a named field or tag.
trait Entry {
    type Part;
    fn part(&self) -> &Self::Part;
    #[must_use]
    fn with(&self, part: Self::Part) -> Self;
}

impl Entry for Ty {
    type Part = Self;
    fn part(&self) -> &Self {
        self
    }
    fn with(&self, part: Self) -> Self {
        part
    }
}

impl<P> Entry for (Symbol, P) {
    type Part = P;
    fn part(&self) -> &P {
        &self.1
    }
    fn with(&self, part: P) -> Self {
        (self.0, part)
    }
}

/// Each entry of `entries` with what `part` resolves it to, or nothing
/// where it resolves none: the ones before the first it does are
/// cloned only once one does.
fn resolved_entries<T: Clone + Entry>(
    entries: &[T],
    part: impl Fn(&T::Part) -> Option<T::Part>,
) -> Option<Vec<T>> {
    let mut resolved: Option<Vec<T>> = None;
    for (at, entry) in entries.iter().enumerate() {
        match part(entry.part()) {
            Some(new) => resolved
                .get_or_insert_with(|| entries[..at].to_vec())
                .push(entry.with(new)),
            None => {
                if let Some(resolved) = &mut resolved {
                    resolved.push(entry.clone());
                }
            }
        }
    }
    resolved
}

/// A row's own tail, where it has one.
fn ty_tail(ty: &Ty) -> Option<Rc<Ty>> {
    match ty {
        Ty::Variants(_, tail) | Ty::Record(_, tail) => tail.clone(),
        _ => None,
    }
}

/// A tag of a row, with its fields; or a record's field, as a one-type
/// tag, where a row unification treats both alike.
type Tag = (Symbol, Rc<[Ty]>);

/// The tags of a row, each with its fields.
type Tags = Vec<Tag>;

/// Which kind of row a row unification builds: a tag row, whose entries
/// are tags and their fields, or a record, whose entries are fields each
/// held as a one-type entry.
#[derive(Clone, Copy, Debug)]
enum Former {
    Tags,
    Fields,
}

impl Former {
    fn build(self, entries: Tags, tail: Option<Rc<Ty>>) -> Ty {
        match self {
            Self::Tags => Ty::Variants(entries.into(), tail),
            Self::Fields => Ty::Record(
                entries
                    .into_iter()
                    .map(|(name, held)| (name, held[0].clone()))
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
        .map(|(name, ty)| (*name, Rc::from([ty.clone()])))
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

/// A method a type's block defines without a signature.
#[derive(Clone, Copy, Debug)]
struct UnsignedMethod {
    name: Symbol,
    owner: Symbol,
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
    /// Whether the member is reached through the type, `a.zero` or
    /// `a.of_nat(n)`, rather than as a method of a value of it, which is
    /// its type's first parameter.
    associated: bool,
    /// Whether the member is named on a value with no call, `x.name`: a
    /// field, or a method taking nothing else.
    bare: bool,
    /// The alias whose application wrote it, where one of one parameter did.
    through: Option<Symbol>,
}

impl Bound {
    fn substituted(&self, replacements: &HashMap<u32, Ty>) -> Self {
        Self {
            owner: substitute(&self.owner, replacements),
            member: self.member,
            ty: substitute(&self.ty, replacements),
            associated: self.associated,
            bare: self.bare,
            through: self.through,
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
    /// A call to elaborate, or no site for a bound owed by another operation.
    site: Option<h::SiteId>,
    module: ModuleId,
    span: super::ast::Span,
    name: Symbol,
    receiver: Ty,
    arguments: Vec<Ty>,
    result: Ty,
    reach: Reach,
    resolved: bool,
    /// The definition whose bound this is, and the alias that wrote it,
    /// where it is owed by a use rather than written.
    owed: Option<(Symbol, Option<Symbol>)>,
}

/// How a member is reached.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reach {
    /// Called on a value, `x.add(y)`.
    Called,
    /// Named on a value with no call, `x.name`: a field, or a method of no
    /// other arguments.
    Bare,
    /// Through the type, `a.zero`: a value of the type rather than a
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
    field_sites: Vec<(h::SiteId, super::ast::Span)>,
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
    /// Record elaboration for an expression, but only validate a pattern numeral.
    site: Option<h::SiteId>,
    module: ModuleId,
    span: super::ast::Span,
    magnitude: num_bigint::BigUint,
    negative: bool,
    /// For a decimal, the power of ten `magnitude` is over: a float's
    /// numeral, where the others are integers'.
    scale: Option<u32>,
    ty: Ty,
    resolved: bool,
}

#[derive(Debug, Default)]
struct Infer {
    /// What each variable is bound to. Resolving one stores back what it
    /// resolved to, so a chain of variables is walked once: interior, as
    /// resolving only reads what inference holds.
    links: RefCell<Vec<Option<Ty>>>,
    next_rigid: u32,
    /// The variables bound since the outermost open probe began, which it
    /// unbinds when it ends.
    trail: Vec<u32>,
    probing: bool,
}

impl Infer {
    /// What `trial` answers, with every variable it made or bound undone:
    /// a probe costs what it does, not what inference holds.
    fn probe<T>(&mut self, trial: impl FnOnce(&mut Self) -> T) -> T {
        let variables = self.links.get_mut().len();
        let (bound, outer) = (self.trail.len(), self.probing);
        self.probing = true;
        let answer = trial(self);
        for id in self.trail.drain(bound..) {
            self.links.get_mut()[usize::try_from(id).expect("u32 fits usize")] = None;
        }
        self.links.get_mut().truncate(variables);
        self.probing = outer;
        answer
    }

    /// `trial`, kept where it succeeds and undone where it fails, so a
    /// refusal leaves inference as it found it.
    fn attempt<T, E>(&mut self, trial: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E> {
        let variables = self.links.get_mut().len();
        let (bound, outer) = (self.trail.len(), self.probing);
        self.probing = true;
        let answer = trial(self);
        if answer.is_err() {
            for id in self.trail.drain(bound..) {
                self.links.get_mut()[usize::try_from(id).expect("u32 fits usize")] = None;
            }
            self.links.get_mut().truncate(variables);
        } else if !outer {
            self.trail.truncate(bound);
        }
        self.probing = outer;
        answer
    }

    fn bind(&mut self, id: u32, ty: Ty) {
        if self.probing {
            self.trail.push(id);
        }
        self.links.get_mut()[usize::try_from(id).expect("u32 fits usize")] = Some(ty);
    }

    fn fresh(&mut self) -> Ty {
        let links = self.links.get_mut();
        let id = u32::try_from(links.len()).expect("fewer than 2^32 inference variables");
        links.push(None);
        Ty::Var(id)
    }

    /// `ty` with every bound variable in it replaced by what it is bound
    /// to, rows flattened and records' fields in order. The parts no
    /// binding reaches are `ty`'s own, shared rather than rebuilt.
    fn resolve(&self, ty: &Ty) -> Ty {
        self.resolved(ty).unwrap_or_else(|| ty.clone())
    }

    /// `ty` resolved, or nothing where it already is.
    fn resolved(&self, ty: &Ty) -> Option<Ty> {
        match ty {
            Ty::Var(id) => {
                let at = usize::try_from(*id).expect("u32 fits usize");
                let link = self.links.borrow()[at].clone()?;
                let resolved = self.resolve(&link);
                // A probe's bindings are undone, so what it resolves is
                // not kept.
                if !self.probing {
                    self.links.borrow_mut()[at] = Some(resolved.clone());
                }
                Some(resolved)
            }
            Ty::Rigid(_) => None,
            Ty::Named(name, arguments) => {
                let arguments = self.resolved_all(arguments)?;
                Some(Ty::Named(*name, arguments))
            }
            Ty::Function(parameters, result) => {
                let resolved_parameters = self.resolved_all(parameters);
                let resolved_result = self.resolved(result);
                if resolved_parameters.is_none() && resolved_result.is_none() {
                    return None;
                }
                let parameters = resolved_parameters.unwrap_or_else(|| parameters.clone());
                let result = resolved_result.map_or_else(|| result.clone(), Rc::new);
                Some(Ty::Function(parameters, result))
            }
            // A row is resolved flat: a tail bound to a row gives up its
            // tags, so what comes back ends in an unbound tail or none.
            Ty::Variants(tags, tail) => {
                let fields = resolved_entries(tags, |fields| self.resolved_all(fields));
                let tail = tail.as_deref().and_then(|tail| self.resolved(tail));
                if fields.is_none() && tail.is_none() {
                    return None;
                }
                let mut tags = fields.unwrap_or_else(|| tags.to_vec());
                let tail = match tail {
                    Some(Ty::Variants(more, rest)) => {
                        tags.extend(more.iter().cloned());
                        rest
                    }
                    Some(other) => Some(Rc::new(other)),
                    None => ty_tail(ty),
                };
                Some(Ty::Variants(tags.into(), tail))
            }
            Ty::Record(fields, tail) => {
                let resolved = resolved_entries(fields, |field| self.resolved(field));
                let tail = tail.as_deref().and_then(|tail| self.resolved(tail));
                let sorted = fields.is_sorted_by_key(|(name, _)| *name);
                if resolved.is_none() && tail.is_none() && sorted {
                    return None;
                }
                let mut fields = resolved.unwrap_or_else(|| fields.to_vec());
                let tail = match tail {
                    Some(Ty::Record(more, rest)) => {
                        fields.extend(more.iter().cloned());
                        rest
                    }
                    Some(other) => Some(Rc::new(other)),
                    None => ty_tail(ty),
                };
                fields.sort_by_key(|(name, _)| *name);
                Some(Ty::Record(fields.into(), tail))
            }
            Ty::Tuple(members) => Some(Ty::Tuple(self.resolved_all(members)?)),
        }
    }

    /// `types` resolved, or nothing where each already is.
    fn resolved_all(&self, types: &Rc<[Ty]>) -> Option<Rc<[Ty]>> {
        resolved_entries(types, |ty| self.resolved(ty)).map(Rc::from)
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
                    self.bind(*id, other.clone());
                    Ok(())
                }
            }
            (Ty::Named(a, aa), Ty::Named(b, ba)) if a == b && aa.len() == ba.len() => {
                for (a, b) in aa.iter().zip(ba.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (Ty::Function(ap, ar), Ty::Function(bp, br)) if ap.len() == bp.len() => {
                for (a, b) in ap.iter().zip(bp.iter()) {
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
                for (a, b) in a.iter().zip(b.iter()) {
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
                for (a, b) in aa.iter().zip(ba.iter()) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                let mut widened = false;
                for (a, b) in a.iter().zip(b.iter()) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Record(a, a_tail), Ty::Record(b, b_tail)) => {
                let mut widened = false;
                for (name, field) in a.iter() {
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
                            let ty = shared.map_or_else(|| ty.clone(), |(_, ty)| ty.clone());
                            (*name, Rc::from([ty]))
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
                for (name, fields) in a.iter() {
                    if let Some((_, other)) = b.iter().find(|(found, _)| found == name) {
                        if fields.len() != other.len() {
                            return Err(Mismatch::Fields(fields.len(), other.len()));
                        }
                        for (field, other) in fields.iter().zip(other.iter()) {
                            widened |= self.subsume(field, other)?;
                        }
                    }
                }
                // The shared tags' fields are settled; what remains is which
                // tags each row holds.
                let settled = |tags: &[Tag], other: &[Tag]| -> Tags {
                    tags.iter()
                        .map(|(name, fields)| {
                            let shared = other.iter().any(|(found, _)| found == name);
                            (
                                *name,
                                if shared {
                                    Rc::default()
                                } else {
                                    fields.clone()
                                },
                            )
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
                    // A closed row answered where the row is still being
                    // worked out joins it, as Ori's rows join: the open
                    // row takes the tags only this one holds, and this
                    // value is rebuilt in it where it is answered.
                    Err(_) if a_tail.is_none() && matches!(b_tail.as_deref(), Some(Ty::Var(_))) => {
                        let open = self.fresh();
                        self.unify_rows(
                            Former::Tags,
                            (&left, Some(&open)),
                            (&right, b_tail.as_deref()),
                        )?;
                        Ok(true)
                    }
                    // A closed row holding tags the signature's lacks is
                    // refused for those tags, which is the whole of it.
                    Err(_)
                        if a_tail.is_none() && matches!(b_tail.as_deref(), Some(Ty::Rigid(_))) =>
                    {
                        Err(Mismatch::NotAmong {
                            tags: a
                                .iter()
                                .filter(|(name, _)| !b.iter().any(|(found, _)| found == name))
                                .map(|(name, _)| *name)
                                .collect(),
                            row: expected.clone(),
                        })
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
        (left, left_tail): (&[Tag], Option<&Ty>),
        (right, right_tail): (&[Tag], Option<&Ty>),
    ) -> Result<(), Mismatch> {
        for (name, fields) in left {
            if let Some((_, other)) = right.iter().find(|(found, _)| found == name) {
                if fields.len() != other.len() {
                    return Err(Mismatch::Fields(fields.len(), other.len()));
                }
                for (a, b) in fields.iter().zip(other.iter()) {
                    self.unify(a, b)?;
                }
            }
        }
        let only = |from: &[Tag], other: &[Tag]| -> Tags {
            from.iter()
                .filter(|(name, _)| !other.iter().any(|(found, _)| found == name))
                .cloned()
                .collect()
        };
        let (only_left, only_right) = (only(left, right), only(right, left));
        let not_among = |extra: &Tags, tags: &[Tag], tail: Option<&Ty>| Mismatch::NotAmong {
            tags: extra.iter().map(|(name, _)| *name).collect(),
            row: former.build(tags.to_vec(), tail.cloned().map(Rc::new)),
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
                let rest = Rc::new(self.fresh());
                self.unify(&Ty::Var(*v), &former.build(only_right, Some(rest.clone())))?;
                self.unify(&Ty::Var(*w), &former.build(only_left, Some(rest)))
            }
            (Some(Ty::Var(v)), Some(rigid @ Ty::Rigid(_))) => {
                if !only_left.is_empty() {
                    return Err(not_among(&only_left, right, right_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_right, Some(Rc::new(rigid.clone()))),
                )
            }
            (Some(rigid @ Ty::Rigid(_)), Some(Ty::Var(v))) => {
                if !only_right.is_empty() {
                    return Err(not_among(&only_right, left, left_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_left, Some(Rc::new(rigid.clone()))),
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
        h::Type::Variable(_) | h::Type::Hole => true,
        h::Type::Named(_, arguments) => arguments.iter().all(first_order),
        h::Type::Variants(tags) => tags.iter().flat_map(|tag| &tag.fields).all(first_order),
        h::Type::Record(fields, _) => fields.iter().all(|(_, field)| first_order(field)),
        h::Type::Tuple(members) => members.iter().all(first_order),
    }
}

/// Whether a written type leaves some part of itself to be worked out.
fn has_hole(ty: &h::Type) -> bool {
    match ty {
        h::Type::Hole => true,
        h::Type::Variable(_) => false,
        h::Type::Named(_, types) | h::Type::Tuple(types) => types.iter().any(has_hole),
        h::Type::Function(parameters, result) => {
            parameters.iter().any(has_hole) || has_hole(result)
        }
        h::Type::Variants(tags) => tags.iter().flat_map(|tag| &tag.fields).any(has_hole),
        h::Type::Record(fields, _) => fields.iter().any(|(_, field)| has_hole(field)),
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
                .flat_map(|(_, fields)| fields.iter())
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
    replaced(ty, &|leaf| match leaf {
        Ty::Var(id) => replacements.get(id).cloned(),
        _ => None,
    })
}

/// `ty` with each variable, flexible or rigid, that `leaf` answers for
/// replaced by what it answers.
fn replaced(ty: &Ty, leaf: &impl Fn(&Ty) -> Option<Ty>) -> Ty {
    match ty {
        Ty::Var(_) | Ty::Rigid(_) => leaf(ty).unwrap_or_else(|| ty.clone()),
        Ty::Named(name, arguments) => Ty::Named(
            *name,
            arguments.iter().map(|ty| replaced(ty, leaf)).collect(),
        ),
        Ty::Function(parameters, result) => Ty::Function(
            parameters.iter().map(|ty| replaced(ty, leaf)).collect(),
            Rc::new(replaced(result, leaf)),
        ),
        Ty::Variants(tags, tail) => Ty::Variants(
            tags.iter()
                .map(|(name, fields)| (*name, fields.iter().map(|ty| replaced(ty, leaf)).collect()))
                .collect(),
            tail.as_deref().map(|tail| Rc::new(replaced(tail, leaf))),
        ),
        Ty::Record(fields, tail) => Ty::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, replaced(ty, leaf)))
                .collect(),
            tail.as_deref().map(|tail| Rc::new(replaced(tail, leaf))),
        ),
        Ty::Tuple(members) => Ty::Tuple(members.iter().map(|ty| replaced(ty, leaf)).collect()),
    }
}

struct Checker<'a> {
    symbols: &'a Symbols,
    prelude: &'a PreludeIds,
    infer: Infer,
    values: HashMap<Symbol, Scheme>,
    /// The names in `values` whose schemes hold a free variable: all that a
    /// generalization must keep clear of. A closed scheme stays closed, as
    /// its variables are renamed wherever it is used, so the rest need no
    /// looking at.
    open: HashSet<Symbol>,
    constructors: HashMap<Symbol, Scheme>,
    methods: HashMap<Symbol, Vec<MethodImpl>>,
    fields: HashMap<Symbol, Vec<FieldImpl>>,
    visible_methods: &'a HashMap<ModuleId, HashSet<Symbol>>,
    pending_methods: Vec<PendingMethod>,
    pending_numerals: Vec<PendingNumeral>,
    pending_tags: Vec<PendingTag>,
    pending_bare: Vec<PendingBare>,
    pending_closings: Vec<PendingClosing>,
    /// Each definition's bounds, over its scheme's variables.
    bounds: HashMap<Symbol, Vec<Bound>>,
    /// Each signed definition's type variables, by the names it writes them.
    variable_names: HashMap<Symbol, HashMap<Symbol, u32>>,
    /// The signatures that write `_` somewhere: each definition is worked
    /// out as an unsigned one is, from the type written rather than from
    /// nothing, so what it writes holds and what it leaves is inferred.
    partial: HashMap<Symbol, h::SignatureDecl>,
    /// The bounds of the signed body being checked, and its variables by
    /// name, rigid as its body sees them.
    current: Vec<Bound>,
    current_names: HashMap<Symbol, Ty>,
    bound_sites: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty, Symbol)>,
    /// What the clause or lambda being checked answers, innermost last,
    /// which is what a `?` in it answers early with. A guard answers
    /// nothing.
    answers: Vec<Option<Ty>>,
    /// Where the pending lists stood when the clause being checked began:
    /// what an answer, or a `?`, settles before its row meets the
    /// signature's.
    clause_marks: Option<Marks>,
    /// In the clause being checked, each local a name bound again in a
    /// branch is after it, and the name.
    merges: HashMap<h::LocalId, Symbol>,
    /// Prefix operators read otherwise than they may look, with what to say
    /// where their operand has no method for them.
    prefix_helps: HashMap<h::SiteId, &'static str>,
    /// The types of the names each loop around the expression being checked
    /// carries, innermost last.
    loops: Vec<Vec<Ty>>,
    expression_types: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty)>,
    clause_types: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty, Vec<Bound>)>,
    widenings: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty)>,
    checked: Facts,
}

impl<'a> Checker<'a> {
    fn new(
        program: &'a n::Program,
        symbols: &'a Symbols,
        prelude: &'a PreludeIds,
    ) -> Result<Self, CheckError> {
        let mut checker = Self {
            symbols,
            prelude,
            infer: Infer::default(),
            values: HashMap::new(),
            open: HashSet::new(),
            constructors: HashMap::new(),
            methods: HashMap::new(),
            fields: HashMap::new(),
            visible_methods: &program.visible_methods,
            pending_methods: Vec::new(),
            pending_numerals: Vec::new(),
            pending_tags: Vec::new(),
            pending_bare: Vec::new(),
            pending_closings: Vec::new(),
            answers: Vec::new(),
            clause_marks: None,
            merges: HashMap::new(),
            prefix_helps: HashMap::new(),
            loops: Vec::new(),
            bounds: HashMap::new(),
            variable_names: HashMap::new(),
            partial: HashMap::new(),
            current: Vec::new(),
            current_names: HashMap::new(),
            bound_sites: Vec::new(),
            expression_types: Vec::new(),
            clause_types: Vec::new(),
            widenings: Vec::new(),
            checked: Facts::default(),
        };
        for data in program.data.values() {
            checker.add_data(data.module, data)?;
        }
        for function in &program.functions {
            if let Some(signature) = &function.signature {
                checker.add_signature(function.module, signature, function.owner)?;
            }
        }
        checker.validate_literal_protocols(program)?;
        Ok(checker)
    }

    fn add_data(&mut self, module: ModuleId, data: &n::Data) -> Result<(), CheckError> {
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
                let message = format!(
                    "constructor `{}` holds a function",
                    spelled(constructor, self.symbols)
                );
                return Err(failure(module, data.span, message)
                    .note("data may not store functions; a function is passed into a call"));
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
        let result = Ty::Named(data.name, arguments.into());
        for constructor in &data.constructors {
            let fields: Vec<_> = constructor
                .fields
                .iter()
                .map(|field| self.surface_type(field, &mut variables))
                .collect();
            let ty = if fields.is_empty() {
                result.clone()
            } else {
                Ty::Function(fields.into(), Rc::new(result.clone()))
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
                return Err(
                    failure(module, data.span, "a declared type's record is closed")
                        .help("write a record with `*` where it is taken, in a signature"),
                );
            }
            if let Ty::Record(fields, _) = &field {
                for (name, field_ty) in fields.iter() {
                    let ty = Ty::Function(Rc::from([result.clone()]), Rc::new(field_ty.clone()));
                    self.fields.entry(*name).or_default().push(FieldImpl {
                        owner: data.name,
                        scheme: Scheme {
                            variables: free_variables(&ty),
                            ty,
                        },
                    });
                }
            }
            let ty = Ty::Function(Rc::from([field]), Rc::new(result));
            self.constructors.insert(
                wrapper.constructor,
                Scheme {
                    variables: free_variables(&ty),
                    ty,
                },
            );
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
            let message = format!(
                "`{}` holds a function other than as a parameter",
                self.symbols.text(signature.spelling)
            );
            return Err(failure(module, signature.span, message)
                .note("a function is passed into a call, never answered or stored"));
        }
        if signature
            .parameters
            .iter()
            .chain([&signature.result])
            .any(has_hole)
        {
            if !signature.constraints.is_empty() {
                let note = format!(
                    "`{}` writes `_`, so its type is worked out from its clauses",
                    self.symbols.text(signature.spelling)
                );
                let message = "a signature that writes `_` takes no `where` bounds";
                return Err(failure(module, signature.span, message).note(note));
            }
            self.partial.insert(signature.name, signature.clone());
            return Ok(());
        }
        let mut variables = HashMap::new();
        let ty = self.signed_type(signature, &mut variables);
        let ty = self.open_result_rows(&ty, true);
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
        self.set_value(signature.name, scheme.clone());
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

    /// The function type `signature` writes, over `variables`.
    fn signed_type(
        &mut self,
        signature: &h::SignatureDecl,
        variables: &mut HashMap<Symbol, Ty>,
    ) -> Ty {
        let parameters = signature
            .parameters
            .iter()
            .map(|ty| self.surface_type(ty, variables))
            .collect();
        let result = self.surface_type(&signature.result, variables);
        Ty::Function(parameters, Rc::new(result))
    }

    /// The methods a type's block defines without a signature, by the
    /// spelling a dot calls them by.
    fn unsigned_methods(
        &self,
        program: &n::Program,
        unsigned: &HashSet<Symbol>,
    ) -> HashMap<Symbol, Vec<UnsignedMethod>> {
        let mut methods: HashMap<Symbol, Vec<UnsignedMethod>> = HashMap::new();
        for function in &program.functions {
            let Some(owner) = function.owner else {
                continue;
            };
            if !unsigned.contains(&function.name) {
                continue;
            }
            let canonical = self.symbols.text(function.name);
            let Some(spelling) = canonical
                .rsplit_once('.')
                .and_then(|(_, spelled)| self.symbols.find(spelled))
            else {
                continue;
            };
            methods.entry(spelling).or_default().push(UnsignedMethod {
                name: function.name,
                owner,
            });
        }
        methods
    }

    /// `name`, where it is a method written without a signature, callable
    /// with a dot at `scheme`: its type while its own component is being
    /// worked out, and what that settled on after.
    fn register_unsigned(
        &mut self,
        methods: &HashMap<Symbol, Vec<UnsignedMethod>>,
        name: Symbol,
        scheme: Scheme,
    ) {
        let Some((&spelling, method)) = methods.iter().find_map(|(spelling, methods)| {
            methods
                .iter()
                .find(|method| method.name == name)
                .map(|method| (spelling, method))
        }) else {
            return;
        };
        let implementations = self.methods.entry(spelling).or_default();
        implementations.retain(|implementation| implementation.target != name);
        implementations.push(MethodImpl {
            owner: method.owner,
            target: name,
            scheme,
            bound: false,
        });
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
                let (variable, member, ty, through) = match constraint {
                    h::Constraint::Member {
                        variable,
                        member,
                        ty,
                        through,
                    } => (*variable, *member, ty, *through),
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
                    bare: false,
                    through,
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
    /// A signature's `Result(a, [Empty])` says what this definition fails
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
                Rc::new(self.open_result_rows(result, positive)),
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
                    None if positive && !tags.is_empty() => Some(Rc::new(self.infer.fresh())),
                    other => other.clone(),
                };
                Ty::Variants(tags.into(), tail)
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
            // Whatever the clauses make it: a variable no scheme quantifies
            // until they have.
            h::Type::Hole => self.infer.fresh(),
            h::Type::Function(parameters, result) => Ty::Function(
                parameters
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
                Rc::new(self.surface_type(result, variables)),
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
                open.then(|| Rc::new(self.infer.fresh())),
            ),
            h::Type::Tuple(members) => Ty::Tuple(
                members
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
            ),
        }
    }

    fn validate_literal_protocols(&self, program: &n::Program) -> Result<(), CheckError> {
        let Some(module) = program.functions.first().map(|function| function.module) else {
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
                    .map(|name| Ty::Named(name, Rc::default()))
                    .collect(),
                Rc::new(Ty::Named(result, Rc::default())),
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

    fn check(mut self, program: &n::Program) -> Result<Facts, CheckError> {
        let definitions: HashMap<_, _> = program
            .functions
            .iter()
            .filter(|function| !function.clauses.is_empty())
            .map(|function| (function.name, function))
            .collect();
        let unsigned: HashSet<_> = definitions
            .keys()
            .filter(|name| !self.values.contains_key(name))
            .copied()
            .collect();
        let methods = self.unsigned_methods(program, &unsigned);

        for component in components(&definitions, &unsigned, &methods, self.symbols) {
            let marks = self.marks();
            let mut monotypes = HashMap::new();
            for name in &component {
                let function = definitions[name];
                let clauses = &function.clauses;
                let arity = clauses.first().map_or(0, |clause| clause.patterns.len());
                if clauses.iter().any(|clause| clause.patterns.len() != arity) {
                    let (module, clause) = (function.module, &clauses[0]);
                    return Err(failure(
                        module,
                        clause.span,
                        "clauses of one function have different arities",
                    ));
                }
                let ty = if let Some(signature) = self.partial.get(name).cloned() {
                    if signature.parameters.len() != arity {
                        return Err(failure(
                            function.module,
                            clauses[0].span,
                            format!(
                                "clause takes {arity} patterns but its signature takes {} parameters",
                                signature.parameters.len()
                            ),
                        ));
                    }
                    self.signed_type(&signature, &mut HashMap::new())
                } else {
                    let parameters = (0..arity).map(|_| self.infer.fresh()).collect();
                    Ty::Function(parameters, Rc::new(self.infer.fresh()))
                };
                self.set_value(
                    *name,
                    Scheme {
                        variables: Vec::new(),
                        ty: ty.clone(),
                    },
                );
                monotypes.insert(*name, ty.clone());
                self.register_unsigned(
                    &methods,
                    *name,
                    Scheme {
                        variables: Vec::new(),
                        ty,
                    },
                );
            }
            for name in &component {
                for clause in &definitions[name].clauses {
                    self.check_clause(definitions[name].module, clause, &monotypes[name])?;
                }
            }
            let types: Vec<Ty> = monotypes.values().cloned().collect();
            let names = component_name_set(&monotypes);
            self.finish_pending(marks, Finish::Unsigned(&types, &names))?;
            for name in &component {
                let Ty::Function(parameters, _) = self.infer.resolve(&monotypes[name]) else {
                    continue;
                };
                let function = definitions[name];
                let clauses = &function.clauses;
                for (column, parameter) in parameters.iter().enumerate() {
                    let rows = clauses
                        .iter()
                        .map(|clause| (clause.patterns[column].clone(), clause.guard.is_some()))
                        .collect();
                    let (module, clause) = (function.module, &clauses[0]);
                    self.close_rows(parameter, rows)
                        .map_err(|message| failure(module, clause.span, message))?;
                }
            }
            for name in &component {
                if let Ty::Function(_, result) = self.infer.resolve(&monotypes[name])
                    && matches!(*result, Ty::Function(..))
                {
                    let (module, clause) =
                        (definitions[name].module, &definitions[name].clauses[0]);
                    let message = format!("`{}` answers a function", spelled(*name, self.symbols));
                    return Err(failure(module, clause.span, message)
                        .note("a function is passed into a call, never answered"));
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
                for clause in &definitions[name].clauses {
                    if let Some(site) = self
                        .clause_types
                        .iter_mut()
                        .find(|(_, _, site, _, _)| *site == clause.site)
                    {
                        site.4.clone_from(&bounds);
                    }
                }
            }
            let fixed = self.fixed(&names);
            for name in component {
                let ty = self.infer.resolve(&monotypes[&name]);
                let mut scheme = self.generalize(&ty, &fixed);
                // A variable only a bound mentions is quantified too.
                let mentioned = bounds
                    .iter()
                    .flat_map(|bound| free_variables(&self.infer.resolve(&bound.ty)));
                for variable in mentioned {
                    if !fixed.contains(&variable) && !scheme.variables.contains(&variable) {
                        scheme.variables.push(variable);
                    }
                }
                self.bounds.insert(name, bounds.clone());
                self.register_unsigned(&methods, name, scheme.clone());
                self.set_value(name, scheme);
            }
        }

        for (name, function) in &definitions {
            let Some(scheme) = self.values.get(name).cloned() else {
                continue;
            };
            if unsigned.contains(name) {
                continue;
            }
            let module = function.module;
            for clause in &function.clauses {
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
            .map(|(_, _, site, ty)| (*site, public_type(&self.infer.resolve(ty))))
            .collect();
        self.checked.widenings = self
            .widenings
            .iter()
            .map(|(_, _, site, ty)| (*site, public_type(&self.infer.resolve(ty))))
            .collect();
        self.checked.clauses = self
            .clause_types
            .iter()
            .map(|(_, _, site, ty, bounds)| {
                let InferredType::Function(parameters, result) =
                    public_type(&self.infer.resolve(ty))
                else {
                    unreachable!("a checked clause has a function type")
                };
                (
                    *site,
                    (
                        crate::typed::Signature {
                            parameters,
                            result: *result,
                        },
                        bounds
                            .iter()
                            .map(|bound| self.public_bound(bound))
                            .collect(),
                    ),
                )
            })
            .collect();
        self.checked.bound_sites = self
            .bound_sites
            .iter()
            .map(|(_, _, site, owner, member)| {
                (*site, (public_type(&self.infer.resolve(owner)), *member))
            })
            .collect();
        self.checked.unsigned_members = methods
            .iter()
            .flat_map(|(spelling, methods)| {
                methods
                    .iter()
                    .map(|method| ((method.owner, *spelling), method.name))
            })
            .collect();
        Ok(self.checked)
    }

    fn public_bound(&self, bound: &Bound) -> InferredBound {
        InferredBound {
            owner: public_type(&self.infer.resolve(&bound.owner)),
            member: bound.member,
            ty: public_type(&self.infer.resolve(&bound.ty)),
            associated: bound.associated,
            bare: bound.bare,
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
        let marks = self.marks();
        let outer = self.clause_marks.replace(marks);
        let checked = self.check_clause_within(module, clause, function, marks);
        self.clause_marks = outer;
        checked
    }

    fn check_clause_within(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        function: &Ty,
        marks: Marks,
    ) -> Result<(), CheckError> {
        self.clause_types.push((
            module,
            clause.span,
            clause.site,
            function.clone(),
            self.current.clone(),
        ));
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
        self.merges = clause.merged.iter().copied().collect();
        for (pattern, parameter) in clause.patterns.iter().zip(parameters.iter()) {
            self.pattern(module, pattern, parameter, &mut locals, clause.span)?;
        }
        if let Some(guard) = &clause.guard {
            self.answers.push(None);
            let actual = self.expr(module, guard, &mut locals);
            self.answers.pop();
            let actual = actual?;
            self.unify_at(module, guard.span, &actual, &self.bool_type())?;
        }
        self.answers.push(Some((*result).clone()));
        let checked = self.clause_body(module, clause, &mut locals, (&result, marks));
        self.answers.pop();
        checked
    }

    /// A body's bindings, each value checked and its pattern bound before
    /// the next, and what each waits on settled at its line.
    fn bindings(
        &mut self,
        module: ModuleId,
        bindings: &[h::Binding],
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<(), CheckError> {
        for binding in bindings {
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
                let message = "a function may only be passed straight into a call";
                return Err(failure(module, binding.value.span, message)
                    .label("bound here")
                    .note("a function cannot be bound, answered, or stored"));
            }
            for local in bound {
                let ty = locals[local.index()]
                    .as_ref()
                    .expect("pattern binding installs its local")
                    .ty
                    .clone();
                // A local holds one value, built once at one type, so it
                // is not generalized: a use at another type, a wider row
                // most of all, would read that value as something it is not.
                locals[local.index()] = Some(Scheme {
                    variables: Vec::new(),
                    ty,
                });
            }
        }
        Ok(())
    }

    /// A clause's bindings and answer, with what it answers on top of
    /// [`Self::answers`], and the marks of what the clause left pending.
    fn clause_body(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        locals: &mut Vec<Option<Scheme>>,
        (result, marks): (&Ty, Marks),
    ) -> Result<(), CheckError> {
        self.bindings(module, &clause.body.bindings, locals)?;
        let actual = self.expr(module, &clause.body.result, locals)?;
        // What the answer's type waits on -- a method's receiver, a
        // constructor's pattern, a field read -- is settled first, so a
        // closed row it holds meets the signature's as that row, and is
        // widened, rather than the signature's row being taken for it.
        self.settle(marks)?;
        let span = clause.body.result.span;
        let widened = self
            .infer
            .subsume(&actual, result)
            .map_err(|reason| self.mismatch(module, span, &actual, result, &reason))?;
        if widened {
            self.widenings
                .push((module, span, clause.body.result.site, (*result).clone()));
        }
        Ok(())
    }

    /// A loop: each carried name one type going in, within a round and
    /// after; the condition a `Bool`, or the pattern an element of the
    /// list; the body; and what follows it, whose answer the loop's is.
    fn looped(
        &mut self,
        module: ModuleId,
        looped: &h::Loop,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        let mut carried = Vec::with_capacity(looped.carried.len());
        for (initial, within, after) in &looped.carried {
            let ty = self.expr(module, initial, locals)?;
            for local in [within, after] {
                locals[local.index()] = Some(Scheme {
                    variables: Vec::new(),
                    ty: ty.clone(),
                });
            }
            carried.push(ty);
        }
        match &looped.head {
            h::LoopHead::While(condition) => {
                let asked = self.expr(module, condition, locals)?;
                let bool_ = self.bool_type();
                self.unify_at(module, condition.span, &asked, &bool_)?;
            }
            h::LoopHead::For(pattern, list) => {
                let walked = self.expr(module, list, locals)?;
                let element = self.infer.fresh();
                let list_ty = self.list_type(element.clone());
                self.unify_at(module, list.span, &walked, &list_ty)?;
                self.tested_pattern(module, pattern, &element, locals, list.span)?;
            }
        }
        self.loops.push(carried);
        let round = self
            .bindings(module, &looped.body.bindings, locals)
            .and_then(|()| self.expr(module, &looped.body.result, locals));
        self.loops.pop();
        round?;
        self.bindings(module, &looped.rest.bindings, locals)?;
        self.expr(module, &looped.rest.result, locals)
    }

    /// A test's pattern at the type of what it tests, each name it binds
    /// at one type, as a binding's names are.
    fn tested_pattern(
        &mut self,
        module: ModuleId,
        pattern: &h::Pattern,
        tested: &Ty,
        locals: &mut [Option<Scheme>],
        span: super::ast::Span,
    ) -> Result<(), CheckError> {
        self.pattern(module, pattern, tested, locals, span)?;
        let mut bound = Vec::new();
        collect_pattern_locals(pattern, &mut bound);
        for local in bound {
            let ty = locals[local.index()]
                .as_ref()
                .expect("pattern binding installs its local")
                .ty
                .clone();
            locals[local.index()] = Some(Scheme {
                variables: Vec::new(),
                ty,
            });
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
                let str_ = Ty::Named(self.prelude.str_, Rc::default());
                self.unify_pattern_at(module, span, expected, &str_)
            }
            // Every alternative of an `|` binds the same local, at one type.
            h::Pattern::Bind(local) => {
                if let Some(bound) = &locals[local.index()] {
                    let bound = bound.ty.clone();
                    let merged = self.merges.get(local).copied();
                    return self.infer.unify(expected, &bound).map_err(|_| {
                        let first = show(&self.infer.resolve(&bound), self.symbols);
                        let other = show(&self.infer.resolve(expected), self.symbols);
                        if let Some(name) = merged {
                            let name = self.symbols.text(name);
                            return failure(
                                module,
                                span,
                                format!("`{name}` is read where the branches meet, so it has one type there"),
                            )
                            .label(format!("a `{first}` one way through, and a `{other}` another"))
                            .help("give the value a name of its own in the branch");
                        }
                        let message = "the alternatives of this `|` bind a name at different types";
                        failure(module, span, message).label(format!(
                            "bound as `{first}` by one alternative and as `{other}` by another"
                        ))
                    });
                }
                locals[local.index()] = Some(Scheme {
                    variables: Vec::new(),
                    ty: expected.clone(),
                });
                Ok(())
            }
            h::Pattern::Or(alternatives) => {
                for alternative in alternatives {
                    self.pattern(module, alternative, expected, locals, span)?;
                }
                Ok(())
            }
            h::Pattern::As(local, pattern) => {
                self.pattern(module, &h::Pattern::Bind(*local), expected, locals, span)?;
                self.pattern(module, pattern, expected, locals, span)
            }
            h::Pattern::Constructor(constructor, fields) => {
                let Some(scheme) = self.constructors.get(constructor).cloned() else {
                    return Err(failure(module, span, "constructor has no declared type"));
                };
                let ty = self.infer.instantiate(&scheme);
                let (parameters, result) = match ty {
                    Ty::Function(parameters, result) => (parameters, Rc::unwrap_or_clone(result)),
                    result => (Rc::default(), result),
                };
                if fields.len() != parameters.len() {
                    return Err(failure(
                        module,
                        span,
                        "constructor pattern has the wrong number of fields",
                    ));
                }
                self.unify_pattern_at(module, span, expected, &result)?;
                for (field, parameter) in fields.iter().zip(parameters.iter()) {
                    self.pattern(module, field, parameter, locals, span)?;
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
                    field_sites: Vec::new(),
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
                    Rc::from([(*label, field_types.clone().into())]),
                    Some(Rc::new(self.infer.fresh())),
                );
                self.unify_pattern_at(module, span, expected, &row)?;
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
                    site: None,
                    module,
                    span,
                    magnitude: magnitude.clone(),
                    negative: *negative,
                    scale: None,
                    ty: expected.clone(),
                    resolved: false,
                });
                Ok(())
            }
            h::Pattern::Range(start, end) => {
                for bound in start.iter().chain(end) {
                    self.pending_numerals.push(PendingNumeral {
                        site: None,
                        module,
                        span,
                        magnitude: bound.magnitude.clone(),
                        negative: bound.negative,
                        scale: None,
                        ty: expected.clone(),
                        resolved: false,
                    });
                }
                Ok(())
            }
            h::Pattern::List(elements, rest) => {
                let element = self.infer.fresh();
                self.unify_pattern_at(module, span, expected, &self.list_type(element.clone()))?;
                for pattern in elements {
                    self.pattern(module, pattern, &element, locals, span)?;
                }
                if let Some(rest) = rest {
                    self.pattern(module, rest, expected, locals, span)?;
                }
                Ok(())
            }
            h::Pattern::Ending(front, last) => {
                let element = self.infer.fresh();
                self.unify_pattern_at(module, span, expected, &self.list_type(element.clone()))?;
                self.pattern(module, front, expected, locals, span)?;
                for pattern in last {
                    self.pattern(module, pattern, &element, locals, span)?;
                }
                Ok(())
            }
            // `{x, *}` names some fields and takes a record with any others.
            h::Pattern::Record(fields, open) => {
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|(name, _)| (*name, self.infer.fresh()))
                    .collect();
                let rest = open.then(|| Rc::new(self.infer.fresh()));
                self.unify_pattern_at(
                    module,
                    span,
                    expected,
                    &Ty::Record(field_types.clone().into(), rest),
                )?;
                for ((_, pattern), (_, ty)) in fields.iter().zip(field_types) {
                    self.pattern(module, pattern, &ty, locals, span)?;
                }
                Ok(())
            }
            h::Pattern::Tuple(members) => {
                let member_types: Vec<_> = members.iter().map(|_| self.infer.fresh()).collect();
                self.unify_pattern_at(
                    module,
                    span,
                    expected,
                    &Ty::Tuple(member_types.clone().into()),
                )?;
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
            .push((module, expression.span, expression.site, ty.clone()));
        Ok(ty)
    }

    fn infer_expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, CheckError> {
        match &expression.kind {
            h::ExprKind::Block(body) => {
                self.bindings(module, &body.bindings, locals)?;
                self.expr(module, &body.result, locals)
            }
            h::ExprKind::Loop(looped) => self.looped(module, looped, locals),
            // What a `continue` or a `break` hands on has the types of the
            // names the loop carries; the leave itself is worth whatever its
            // place asks.
            h::ExprKind::Continue(values) | h::ExprKind::Break(values) => {
                let carried = self.loops.last().cloned().unwrap_or_default();
                for (value, ty) in values.iter().zip(&carried) {
                    let handed = self.expr(module, value, locals)?;
                    self.unify_at(module, value.span, &handed, ty)
                        .map_err(|error| {
                            error.note("a name read in a loop's next round or after it has one type across its rounds")
                        })?;
                }
                Ok(self.infer.fresh())
            }
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
            h::ExprKind::Associated(..) => self.associated_call(
                module,
                (expression.site, expression.span),
                expression,
                None,
                locals,
            ),
            h::ExprKind::Call(head, arguments)
                if matches!(head.kind, h::ExprKind::Associated(..)) =>
            {
                self.associated_call(
                    module,
                    (expression.site, expression.span),
                    head,
                    Some(arguments),
                    locals,
                )
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
            // What a `return` answers is its clause's or lambda's answer;
            // the `return` itself is worth whatever its place asks.
            h::ExprKind::Return(value) => {
                let answered = self.expr(module, value, locals)?;
                let Some(Some(answer)) = self.answers.last().cloned() else {
                    return Err(failure(
                        module,
                        expression.span,
                        "`return` answers its clause or lambda, and a guard answers nothing",
                    ));
                };
                self.unify_at(module, value.span, &answered, &answer)?;
                Ok(self.infer.fresh())
            }
            // A test answers a `Bool`; its pattern types what it binds,
            // each at one type, as a binding's names are.
            h::ExprKind::Is(value, pattern) => {
                if let h::ExprKind::Unary(super::ast::UnaryOp::Not, _) = value.kind {
                    self.prefix_helps.insert(
                        value.site,
                        "`!` takes only the operand it touches, which `is` then tests: to negate the test, `!(x is P)`",
                    );
                }
                let tested = self.expr(module, value, locals)?;
                self.tested_pattern(module, pattern, &tested, locals, value.span)?;
                Ok(self.bool_type())
            }
            // Every arm's pattern is the value's, its guard a `Bool`, and its
            // body answers the one type the `is` does.
            h::ExprKind::Match(value, arms) => {
                let tested = self.expr(module, value, locals)?;
                let answer = self.infer.fresh();
                for arm in arms {
                    self.tested_pattern(module, &arm.pattern, &tested, locals, value.span)?;
                    if let Some(guard) = &arm.guard {
                        let asked = self.expr(module, guard, locals)?;
                        let bool_ = self.bool_type();
                        self.unify_at(module, guard.span, &asked, &bool_)?;
                    }
                    let answered = self.expr(module, &arm.body, locals)?;
                    self.unify_at(module, arm.body.span, &answered, &answer)
                        .map_err(|error| error.note("every arm of an `is` answers one type"))?;
                }
                Ok(answer)
            }
            // Its branches answer one type, the one the `if` answers.
            h::ExprKind::If(condition, yes, no) => {
                let asked = self.expr(module, condition, locals)?;
                let bool_ = self.bool_type();
                self.unify_at(module, condition.span, &asked, &bool_)?;
                let answer = self.expr(module, yes, locals)?;
                let other = self.expr(module, no, locals)?;
                self.unify_at(module, no.span, &other, &answer)
                    .map_err(|error| error.note("both branches of an `if` answer one type"))?;
                Ok(answer)
            }
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
                    site: Some(expression.site),
                    module,
                    span: expression.span,
                    magnitude: magnitude.clone(),
                    negative: false,
                    scale: None,
                    ty: ty.clone(),
                    resolved: false,
                });
                Ok(ty)
            }
            h::ExprKind::Decimal(digits, scale) => {
                let ty = self.infer.fresh();
                self.pending_numerals.push(PendingNumeral {
                    site: Some(expression.site),
                    module,
                    span: expression.span,
                    magnitude: digits.clone(),
                    negative: false,
                    scale: Some(*scale),
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
                        let str_ = Ty::Named(self.prelude.str_, Rc::default());
                        self.unify_at(module, splice.span, &value, &str_)?;
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
                    self.checked
                        .literals
                        .insert(expression.site, blessed::string(&bytes, self.prelude));
                }
                Ok(Ty::Named(self.prelude.str_, Rc::default()))
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
                Ok(Ty::Record(inferred.into(), None))
            }
            h::ExprKind::Tuple(members) => {
                let mut inferred = Vec::with_capacity(members.len());
                for member in members {
                    inferred.push(self.expr(module, member, locals)?);
                }
                Ok(Ty::Tuple(inferred.into()))
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
                let shape = Ty::Record(named.into(), Some(Rc::new(self.infer.fresh())));
                self.unify_at(module, expression.span, &updated, &shape)?;
                Ok(updated)
            }
            h::ExprKind::Lambda(patterns, body) => {
                // A lambda has one clause and no guard to make a test with.
                if let Some(test) = patterns.iter().find_map(test_in) {
                    let message = format!("a lambda's parameter cannot test a {test}");
                    return Err(failure(module, expression.span, message)
                        .note(format!(
                            "a {test} pattern is a test, which only a clause makes"
                        ))
                        .help("test it in a clause of a named definition"));
                }
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
                Ok(Ty::Function(parameters.into(), Rc::new(result)))
            }
            h::ExprKind::Call(head, arguments) if matches!(head.kind, h::ExprKind::Dual(_)) => {
                let h::ExprKind::Dual(dual) = &head.kind else {
                    unreachable!("guarded")
                };
                let mut fields = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    fields.push(self.expr(module, argument, locals)?);
                }
                let sites = arguments
                    .iter()
                    .map(|argument| (argument.site, argument.span))
                    .collect();
                Ok(self.defer_tag(module, expression.span, dual, Some(fields), sites))
            }
            h::ExprKind::Call(head, arguments) if matches!(head.kind, h::ExprKind::Tag(_)) => {
                let h::ExprKind::Tag(label) = head.kind else {
                    unreachable!("guarded")
                };
                let mut fields = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    fields.push(self.expr(module, argument, locals)?);
                }
                Ok(self.tag(label, fields.into()))
            }
            h::ExprKind::Call(head, arguments) => {
                let head_type = self.expr(module, head, locals)?;
                let mut argument_types = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    argument_types.push(self.expr(module, argument, locals)?);
                }
                // A known function is held to its arguments one at a time,
                // so what does not fit is told where it is written.
                if let Ty::Function(parameters, result) = self.infer.resolve(&head_type)
                    && parameters.len() == arguments.len()
                {
                    let given = arguments.iter().zip(&argument_types);
                    for ((argument, ty), parameter) in given.zip(parameters.iter()) {
                        self.unify_at(module, argument.span, ty, parameter)?;
                    }
                    return Ok(Rc::unwrap_or_clone(result));
                }
                let result = self.infer.fresh();
                let function = Ty::Function(argument_types.into(), Rc::new(result.clone()));
                self.unify_at(module, expression.span, &function, &head_type)?;
                Ok(result)
            }
            h::ExprKind::Member(receiver, member) => {
                let receiver = self.expr(module, receiver, locals)?;
                Ok(self.defer_method(
                    module,
                    (expression.site, expression.span),
                    receiver,
                    *member,
                    Vec::new(),
                    true,
                ))
            }
            h::ExprKind::Method(receiver, method, arguments) => self.method(
                module,
                (expression.site, expression.span),
                receiver,
                *method,
                arguments,
                locals,
            ),
            h::ExprKind::Unary(super::ast::UnaryOp::Negate, value)
                if matches!(
                    value.kind,
                    h::ExprKind::Number(_) | h::ExprKind::Decimal(..)
                ) =>
            {
                let (magnitude, scale) = match &value.kind {
                    h::ExprKind::Number(magnitude) => (magnitude.clone(), None),
                    h::ExprKind::Decimal(digits, scale) => (digits.clone(), Some(*scale)),
                    _ => unreachable!("guarded"),
                };
                let ty = self.infer.fresh();
                self.pending_numerals.push(PendingNumeral {
                    site: Some(expression.site),
                    module,
                    span: expression.span,
                    magnitude,
                    negative: true,
                    scale,
                    ty: ty.clone(),
                    resolved: false,
                });
                Ok(ty)
            }
            // A prefix takes its operand's postfixes with it: `-x.abs()` is
            // `-(x.abs())`, as in most languages, which a reader may not expect.
            h::ExprKind::Unary(operator, value) => {
                let name = unary_member(*operator);
                let method = self.method_symbol(module, expression.span, name)?;
                if matches!(
                    value.kind,
                    h::ExprKind::Method(..)
                        | h::ExprKind::Call(..)
                        | h::ExprKind::Member(..)
                        | h::ExprKind::Try(..)
                ) {
                    self.prefix_helps.entry(expression.site).or_insert(
                        "a prefix takes the whole call, field or `?` after it, which binds tighter: `(-x).abs()` applies it first",
                    );
                }
                self.method(
                    module,
                    (expression.site, expression.span),
                    value,
                    method,
                    &[],
                    locals,
                )
            }
            h::ExprKind::Binary(operator, left, right) => {
                let name = binary_member(*operator);
                let method = self.method_symbol(module, expression.span, name)?;
                let result = self.method(
                    module,
                    (expression.site, expression.span),
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
                    let order = Ty::Named(self.prelude.order, Rc::default());
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
            .flat_map(|(pattern, guarded)| {
                pattern
                    .choices()
                    .into_iter()
                    .map(move |choice| (choice, guarded))
            })
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
                for (label, fields) in tags.iter() {
                    let taken: Vec<_> = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Tag(found, subs) if found == label => {
                                Some((subs.clone(), *guarded))
                            }
                            _ => None,
                        })
                        .collect();
                    self.close_fields(fields, &taken)?;
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
                        Ty::Function(fields, result) => (fields, Rc::unwrap_or_clone(result)),
                        result => (Rc::default(), result),
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
                for (name, field) in fields.iter() {
                    // A record pattern not naming the field takes any.
                    let column = rows
                        .iter()
                        .filter_map(|(pattern, guarded)| match pattern {
                            h::Pattern::Record(held, _) => Some((
                                held.iter()
                                    .find(|(found, _)| found == name)
                                    .map_or(h::Pattern::Wild, |(_, pattern)| pattern.clone()),
                                *guarded,
                            )),
                            _ => None,
                        })
                        .collect();
                    self.close_rows(field, column)?;
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
        if let h::Pattern::As(_, pattern) = pattern {
            return self.desugared(*pattern);
        }
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

    /// `a.zero`, or `a.parse(text)`: the member a `where` bound of the
    /// signed body being checked gives type `a`, named by the signature's
    /// name for it. A member taking no parameters is a value, written with
    /// no arguments, `None`; any other is called.
    fn associated_call(
        &mut self,
        module: ModuleId,
        (site, span): (h::SiteId, super::ast::Span),
        head: &h::Expr,
        arguments: Option<&[h::Expr]>,
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
        let arguments = match arguments {
            None if parameters.is_empty() => &[][..],
            Some([]) if parameters.is_empty() => {
                return Err(failure(
                    module,
                    span,
                    format!(
                        "`{}` is a value, not a function: write `{}`",
                        spelled(self),
                        spelled(self)
                    ),
                ));
            }
            None => {
                return Err(failure(
                    module,
                    span,
                    format!(
                        "a member a bound gives is called: write `{}(…)`",
                        spelled(self)
                    ),
                ));
            }
            Some(arguments) => arguments,
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
        for (argument, parameter) in arguments.iter().zip(parameters.iter()) {
            let given = self.expr(module, argument, locals)?;
            self.unify_at(module, argument.span, &given, parameter)?;
        }
        self.bound_sites.push((module, span, site, owner, member));
        Ok(Rc::unwrap_or_clone(result))
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
        let marks = self.clause_marks.unwrap_or_else(|| self.marks());
        let taken = self.expr(module, value, locals)?;
        let (ok, error) = (self.infer.fresh(), self.infer.fresh());
        let result = Ty::Named(self.prelude.result, Rc::from([ok.clone(), error.clone()]));
        self.unify_at(module, value.span, &taken, &result)?;
        // As for a clause's answer: the producer's own row, once what it
        // waits on is settled, is what joins the answer's.
        self.settle(marks)?;
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
            Rc::from([self.infer.fresh(), answered_error.clone()]),
        );
        self.infer.unify(&answer, &answered).map_err(|_| {
            failure(
                module,
                span,
                format!(
                    "`?` answers an `Err` early, but this answers `{}`",
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
        field_sites: Vec<(h::SiteId, super::ast::Span)>,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_tags.push(PendingTag {
            module,
            span,
            dual: dual.clone(),
            fields,
            field_sites,
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
        let Some(&(site, span)) = pending.field_sites.get(at) else {
            return self.unify_at(pending.module, pending.span, field, wanted);
        };
        let widened = self
            .infer
            .subsume(field, wanted)
            .map_err(|reason| self.mismatch(pending.module, span, field, wanted, &reason))?;
        if widened {
            self.widenings
                .push((pending.module, span, site, wanted.clone()));
        }
        Ok(())
    }

    /// A value of any row holding `label` with these fields: open, so it
    /// flows to whatever handles more.
    fn tag(&mut self, label: Symbol, fields: Rc<[Ty]>) -> Ty {
        Ty::Variants(
            Rc::from([(label, fields)]),
            Some(Rc::new(self.infer.fresh())),
        )
    }

    fn method(
        &mut self,
        module: ModuleId,
        (site, span): (h::SiteId, super::ast::Span),
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
        Ok(self.defer_method(module, (site, span), receiver, name, argument_types, false))
    }

    fn defer_method(
        &mut self,
        module: ModuleId,
        (site, span): (h::SiteId, super::ast::Span),
        receiver: Ty,
        name: Symbol,
        arguments: Vec<Ty>,
        member: bool,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_methods.push(PendingMethod {
            site: Some(site),
            module,
            span,
            name,
            receiver,
            arguments,
            result: result.clone(),
            reach: if member { Reach::Bare } else { Reach::Called },
            resolved: false,
            owed: None,
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
                site: None,
                module,
                span,
                name: bound.member,
                receiver: bound.owner,
                arguments: parameters.iter().skip(skipped).cloned().collect(),
                result: Rc::unwrap_or_clone(result),
                reach: if bound.associated {
                    Reach::Type
                } else if bound.bare {
                    Reach::Bare
                } else {
                    Reach::Called
                },
                resolved: false,
                owed: Some((definition, bound.through)),
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
            let default = match (numeral.scale, self.prelude.floats.first()) {
                (Some(_), Some(float)) => Ty::Named(float.ty, Rc::default()),
                (Some(_), None) => {
                    return Err(failure(
                        numeral.module,
                        numeral.span,
                        "a decimal numeral is a float, and no float is in the prelude",
                    ));
                }
                (None, _) if numeral.negative => Ty::Named(self.prelude.int, Rc::default()),
                (None, _) => Ty::Named(self.prelude.nat, Rc::default()),
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
    /// the type's `of_nat`, or for a decimal its float's `of_decimal`.
    fn elaborate(&mut self, numeral: &PendingNumeral) -> Result<(), CheckError> {
        let ty = self.infer.resolve(&numeral.ty);
        let float = match &ty {
            Ty::Named(name, arguments) if arguments.is_empty() => {
                self.prelude.floats.iter().find(|float| float.ty == *name)
            }
            _ => None,
        };
        match (numeral.scale, float) {
            (Some(scale), Some(float)) => {
                if let Some(site) = numeral.site {
                    self.checked.literals.insert(
                        site,
                        blessed::decimal(numeral.magnitude.clone(), scale, numeral.negative, float),
                    );
                }
                return Ok(());
            }
            (Some(_), None) => {
                return Err(failure(
                    numeral.module,
                    numeral.span,
                    format!(
                        "a decimal numeral cannot be a `{}`: it is a float, an `F32` or an `F64`",
                        show(&ty, self.symbols)
                    ),
                ));
            }
            (None, Some(float)) => {
                return Err(failure(
                    numeral.module,
                    numeral.span,
                    format!(
                        "a numeral with no point is not a float: write the `{}` with one, as `3.0`",
                        float.name
                    ),
                ));
            }
            (None, None) => {}
        }
        let kind = match ty {
            Ty::Named(name, ref arguments) if name == self.prelude.nat && arguments.is_empty() => {
                NumeralType::Nat
            }
            Ty::Named(name, ref arguments) if name == self.prelude.int && arguments.is_empty() => {
                NumeralType::Int
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
                NumeralType::Word(word)
            }
            // Only the prelude's integers are numerals, and no conversion
            // is inserted to make one fit anything else.
            other => {
                let shown = show(&other, self.symbols);
                let message = format!("a numeral cannot be a `{shown}`");
                return Err(failure(numeral.module, numeral.span, message)
                    .label(format!("expected `{shown}`, found a numeral"))
                    .note("a numeral is a `Nat`, `Int`, `U8`, `U16`, `U32`, or `U64`")
                    .help("convert a value with `of_nat`"));
            }
        };
        let value = blessed::numeral(
            numeral.magnitude.clone(),
            numeral.negative,
            kind,
            self.prelude,
        )
        .map_err(|error| {
            let refused = failure(numeral.module, numeral.span, error.to_string());
            match error.note() {
                Some(note) => refused.note(note),
                None => refused,
            }
        })?;
        if let Some(site) = numeral.site {
            self.checked.literals.insert(site, value);
        }
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
        let fixed = self.fixed(names);
        generic.retain(|variable| !fixed.contains(variable));
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
                    self.infer
                        .probe(|trial| match trial.instantiate(&implementation.scheme) {
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
                        })
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
        let builder = if numeral.scale.is_some() {
            "of_decimal"
        } else {
            "of_nat"
        };
        let builder = self.method_symbol(numeral.module, numeral.span, builder)?;
        let nat = Ty::Named(self.prelude.nat, Rc::default());
        let arguments = if numeral.scale.is_some() {
            vec![nat.clone(), nat]
        } else {
            vec![nat]
        };
        self.pending_methods.push(PendingMethod {
            site: None,
            module: numeral.module,
            span: numeral.span,
            name: builder,
            receiver: numeral.ty.clone(),
            arguments,
            result: numeral.ty.clone(),
            reach: Reach::Type,
            resolved: false,
            owed: None,
        });
        if numeral.negative {
            let neg = self.method_symbol(numeral.module, numeral.span, "neg")?;
            self.pending_methods.push(PendingMethod {
                site: None,
                module: numeral.module,
                span: numeral.span,
                name: neg,
                receiver: numeral.ty.clone(),
                arguments: Vec::new(),
                result: numeral.ty.clone(),
                reach: Reach::Called,
                resolved: false,
                owed: None,
            });
        }
        if let Some(site) = numeral.site {
            self.checked.deferred_numerals.insert(
                site,
                crate::typed::Numeral {
                    magnitude: numeral.magnitude.clone(),
                    negative: numeral.negative,
                    scale: numeral.scale,
                },
            );
        }
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
            let ty = Ty::Function(parameters.into(), Rc::new(pending.result.clone()));
            match bounds.iter().find(|bound| {
                bound.member == pending.name
                    && bound.associated == (pending.reach == Reach::Type)
                    && bound.bare == (pending.reach == Reach::Bare)
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
                    bare: pending.reach == Reach::Bare,
                    through: None,
                }),
            }
            if let Some(site) = pending.site {
                self.bound_sites
                    .push((pending.module, pending.span, site, owner, pending.name));
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
                            for (at, (field, wanted)) in
                                fields.iter().zip(wanted.iter()).enumerate()
                            {
                                self.field_flows(&pending, at, field, wanted)?;
                            }
                            wanted.clone()
                        }
                        _ => fields.into(),
                    };
                    let row = self.tag(pending.dual.spelling, fields);
                    self.unify_at(pending.module, pending.span, &row, &pending.result)?;
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
                    Ty::Function(parameters, Rc::new(row))
                }
                _ => self.tag(pending.label, Rc::default()),
            };
            // The position wants its type; the tag is what is there.
            self.unify_at(pending.module, pending.span, &wanted, &pending.ty)?;
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
            let message = format!("the bare `{word}` reads as `{owner}.{word}` here");
            return Err(failure(pending.module, pending.span, message)
                .note(format!(
                    "inside `{owner}`'s block, a bare constructor is `{owner}`'s own"
                ))
                .help(format!("write `{other}.{word}` for `{other}`'s")));
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
                let built = show(&checker.infer.resolve(built), checker.symbols);
                let wanted = show(&wanted, checker.symbols);
                failure(pending.module, pending.span, "mismatched types")
                    .label(format!("expected `{wanted}`, found `{built}`"))
                    .note(format!(
                        "`{}` builds `{built}`",
                        checker.symbols.text(pending.dual.spelling)
                    ))
            })
        };
        match &pending.fields {
            None => builds(self, &ty)?,
            Some(fields) => {
                let (parameters, result) = match ty {
                    Ty::Function(parameters, result) => (parameters, Rc::unwrap_or_clone(result)),
                    result => (Rc::default(), result),
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
                for (at, (field, parameter)) in fields.iter().zip(parameters.iter()).enumerate() {
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
        let message = format!("constructor `{word}` is ambiguous here");
        failure(pending.module, pending.span, message)
            .note(format!(
                "nothing decides between {}",
                readings.join(" and ")
            ))
            .help("qualify it, or let a signature decide")
    }

    /// Resolve pending methods. On the final pass one still ambiguous is an
    /// error, except on a receiver in `generic`, which becomes a bound.
    fn settle_methods(
        &mut self,
        start: usize,
        final_pass: bool,
        generic: &HashSet<u32>,
    ) -> Result<(), CheckError> {
        let mut generic = generic.clone();
        let mut unresolved: Vec<_> = (start..self.pending_methods.len())
            .filter(|index| !self.pending_methods[*index].resolved)
            .collect();
        loop {
            if final_pass {
                self.spread_generic(start, &mut generic);
            }
            let mut progress = false;
            let mut next = Vec::new();
            let pushed = self.pending_methods.len();
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
                // A bare word with nothing handed it, on a receiver nothing
                // has said anything of yet, is a field of whatever it turns
                // out to be, as Ori reads `.name` without parentheses: it
                // waits for the receiver, and is no guess at a method.
                let may_be_field = pending.reach == Reach::Bare
                    && pending.arguments.is_empty()
                    && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_));
                // The one method the receiver has is applied whether or not
                // it fits, which says why where it does not; on a receiver
                // not yet known, only once nothing else will say it, as the
                // call that answers it may have no such method itself.
                let unknown = matches!(self.infer.resolve(&pending.receiver), Ty::Var(_));
                let candidates: Vec<_> = if may_be_field {
                    Vec::new()
                } else if let [only] = owned.as_slice()
                    && (final_pass || !unknown)
                {
                    vec![only.clone()]
                } else {
                    owned
                        .iter()
                        .filter(|implementation| self.fits(&pending, implementation))
                        .cloned()
                        .collect()
                };
                match candidates.as_slice() {
                    // A field of a receiver nothing else says anything of is
                    // a field of whatever record it turns out to be, unless
                    // the receiver is generic: then it is a bound, met by
                    // any record or declared type having the field.
                    [] if pending.reach == Reach::Bare
                        && pending.arguments.is_empty()
                        && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_)) =>
                    {
                        let generic_receiver = matches!(
                            self.infer.resolve(&pending.receiver),
                            Ty::Var(variable) if generic.contains(&variable)
                        );
                        if final_pass && !generic_receiver {
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
                    // Said on the final pass, when what the call answers is
                    // known too, so the bound the refusal suggests is whole.
                    [] if !final_pass => next.push(index),
                    [] => {
                        let name = self.symbols.text(pending.name);
                        let refused = match self.infer.resolve(&pending.receiver) {
                            Ty::Var(_) => {
                                let message = format!("no field or method `{name}` is in scope");
                                failure(pending.module, pending.span, message)
                            }
                            // A signature's variable has only what its bounds give.
                            Ty::Rigid(_) => self.unbounded(&pending),
                            receiver => {
                                let message = format!(
                                    "`{}` has no field or method `{name}`",
                                    show(&receiver, self.symbols)
                                );
                                let refused = failure(pending.module, pending.span, message);
                                match pending.site.and_then(|site| self.prefix_helps.get(&site)) {
                                    Some(help) => refused.help(*help),
                                    None => refused,
                                }
                            }
                        };
                        return Err(refused);
                    }
                    [candidate] => {
                        self.apply_method(&pending, candidate)?;
                        self.pending_methods[index].resolved = true;
                        progress = true;
                    }
                    _ => next.push(index),
                }
            }
            // What resolving these owes, and the calls a structural member
            // makes of its components, are asked in the next round.
            next.extend(pushed..self.pending_methods.len());
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

    /// Why a signed body's own variable has no `pending`: its signature
    /// gives it none. Where a definition used here asks it, that says so,
    /// and the alias it asks through is what to write.
    fn unbounded(&self, pending: &PendingMethod) -> CheckError {
        let member = self.symbols.text(pending.name);
        let receiver = self.infer.resolve(&pending.receiver);
        let variable = self
            .current_names
            .iter()
            .find(|(_, ty)| self.infer.resolve(ty) == receiver)
            .map(|(name, _)| self.symbols.text(*name));
        let message = variable.map_or_else(
            || format!("a type variable has no field or method `{member}`"),
            |variable| format!("the type variable `{variable}` has no field or method `{member}`"),
        );
        let refused = failure(pending.module, pending.span, message);
        let written = variable.and_then(|variable| self.written_bound(pending, variable));
        let help = written.map_or_else(
            || format!("give it `{member}` with a `where` bound in the signature"),
            |bound| format!("write `{bound}` in the signature's `where`"),
        );
        let Some((definition, through)) = pending.owed else {
            return refused.help(help);
        };
        let definition = spelled(definition, self.symbols);
        let refused = refused.note(format!("`{definition}`, used here, asks for `{member}`"));
        match (through, variable) {
            (Some(alias), Some(variable)) => refused.help(format!(
                "write `{}({variable})` in the signature's `where`, as `{definition}` does",
                spelled(alias, self.symbols)
            )),
            _ => refused.help(help),
        }
    }

    /// The bound that would give `variable` what `pending` calls on it, as
    /// a signature writes it, where every type in it is known.
    fn written_bound(&self, pending: &PendingMethod, variable: &str) -> Option<String> {
        if pending.reach != Reach::Called {
            return None;
        }
        let names: HashMap<u32, Symbol> = self
            .current_names
            .iter()
            .filter_map(|(name, ty)| match self.infer.resolve(ty) {
                Ty::Rigid(variable) => Some((variable, *name)),
                _ => None,
            })
            .collect();
        let parameters: Rc<[Ty]> = std::iter::once(&pending.receiver)
            .chain(&pending.arguments)
            .map(|ty| self.infer.resolve(ty))
            .collect();
        let ty = Ty::Function(parameters, Rc::new(self.infer.resolve(&pending.result)));
        let known = replaced(&ty, &|leaf| match leaf {
            Ty::Rigid(variable) => names
                .get(variable)
                .map(|name| Ty::Named(*name, Rc::default())),
            _ => None,
        });
        let shown = show(&known, self.symbols);
        let member = self.symbols.text(pending.name);
        (!shown.contains(['_', '\''])).then(|| format!("{variable}.{member} : {shown}"))
    }

    fn field_candidates(&mut self, pending: &PendingMethod) -> Vec<Scheme> {
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
        // A receiver not yet known waits to be known, and is at the last
        // a record having the field: which declared types have a field of
        // that name says nothing of it, and one declared anywhere would
        // otherwise change what an unrelated projection means.
        let Ty::Named(owner, _) = receiver else {
            return Vec::new();
        };
        fields
            .iter()
            .filter(|field| field.owner == owner)
            .filter(|field| {
                self.infer.probe(|trial| {
                    apply_signature(trial, pending, &field.scheme, self.symbols).is_ok()
                })
            })
            .map(|field| field.scheme.clone())
            .collect()
    }

    /// Add to `generic` what a member of a receiver holding a generic
    /// variable reads and answers: a field read off a generic record, or
    /// what a generic value's member takes and answers, is as generic as
    /// the value, and a bound on it will say so. Until nothing more joins.
    fn spread_generic(&self, start: usize, generic: &mut HashSet<u32>) {
        loop {
            let before = generic.len();
            // A generic variable since bound to a record holds what the
            // record does.
            let bound: Vec<u32> = generic
                .iter()
                .flat_map(|&variable| free_variables(&self.infer.resolve(&Ty::Var(variable))))
                .collect();
            generic.extend(bound);
            for pending in &self.pending_methods[start..] {
                let receiver = free_variables(&self.infer.resolve(&pending.receiver));
                if receiver.iter().any(|variable| generic.contains(variable)) {
                    generic.extend(receiver);
                    for ty in pending.arguments.iter().chain([&pending.result]) {
                        generic.extend(free_variables(&self.infer.resolve(ty)));
                    }
                }
            }
            if generic.len() == before {
                return;
            }
        }
    }

    /// Reading field `name` of a record: `{name: t, *} -> t`, which reads it
    /// from a record that has it and asks it of one that is open. Its two
    /// variables are the scheme's own, never linked, since a scheme is
    /// instantiated before it is used.
    fn projection(name: Symbol) -> Scheme {
        let (field, rest) = (u32::MAX, u32::MAX - 1);
        Scheme {
            variables: vec![field, rest],
            ty: Ty::Function(
                Rc::from([Ty::Record(
                    Rc::from([(name, Ty::Var(field))]),
                    Some(Rc::new(Ty::Var(rest))),
                )]),
                Rc::new(Ty::Var(field)),
            ),
        }
    }

    /// `equals` and `to_str` on a closed record, a tuple or a tag row, `cmp`
    /// on a tuple, and `hash_into` on a record or a tuple, which such values have with no
    /// declaration: each asks the same of every component, position by
    /// position for a tuple and field by field of each tag for a row. A
    /// record and a row have no `cmp`, having no order of their fields or
    /// tags, and an open record has neither, its other fields being a
    /// caller's, as a row a caller may add tags to has neither `equals` nor
    /// `to_str`. Answers whether `pending` was one, or nothing while a record
    /// or row may yet be closed.
    fn structural(
        &mut self,
        pending: &PendingMethod,
        final_pass: bool,
    ) -> Result<Option<bool>, CheckError> {
        let receiver = self.infer.resolve(&pending.receiver);
        let components = match &receiver {
            Ty::Tuple(members) => members.clone(),
            Ty::Record(fields, _) => fields.iter().map(|(_, ty)| ty.clone()).collect(),
            Ty::Variants(tags, _) => tags
                .iter()
                .flat_map(|(_, fields)| fields.iter().cloned())
                .collect(),
            _ => return Ok(Some(false)),
        };
        let spelled = self.symbols.text(pending.name);
        // `hash_into` feeds each component to a hasher and answers it fed:
        // what it answers is whatever hasher it was handed.
        let hashing = spelled == "hash_into"
            && matches!(receiver, Ty::Tuple(_) | Ty::Record(..))
            && pending.arguments.len() == 1;
        let answer = match (spelled, &receiver) {
            ("equals", _) => Ty::Named(self.prelude.bool_, Rc::default()),
            ("cmp", Ty::Tuple(_)) => Ty::Named(self.prelude.order, Rc::default()),
            ("to_str", _) => Ty::Named(self.prelude.str_, Rc::default()),
            _ if hashing => pending.arguments[0].clone(),
            _ => return Ok(Some(false)),
        };
        if let Ty::Record(_, Some(tail)) = &receiver {
            if !final_pass && matches!(**tail, Ty::Var(_)) {
                return Ok(None);
            }
            return Err(failure(
                pending.module,
                pending.span,
                format!("a record with `*` has no `{spelled}`: its other fields are a caller's"),
            ));
        }
        // A row's rest nothing else fills closes to nothing, but may be
        // filled yet until checking is done.
        if let Ty::Variants(_, Some(tail)) = &receiver {
            match &**tail {
                Ty::Var(_) if !final_pass => return Ok(None),
                Ty::Var(_) => {}
                _ => {
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "`{}` may hold tags a caller adds, which it cannot say `{spelled}` of",
                            show(&receiver, self.symbols)
                        ),
                    ));
                }
            }
        }
        // `to_str` takes the value alone, `hash_into` a hasher, and the
        // others a second like it.
        let unary = spelled == "to_str";
        match pending.arguments.as_slice() {
            [] if unary => {}
            [_] if hashing => {}
            [other] if !unary => self.unify_at(pending.module, pending.span, other, &receiver)?,
            _ => return Ok(Some(false)),
        }
        self.unify_at(pending.module, pending.span, &answer, &pending.result)?;
        for component in components.iter() {
            let arguments = if unary {
                Vec::new()
            } else if hashing {
                vec![answer.clone()]
            } else {
                vec![component.clone()]
            };
            self.pending_methods.push(PendingMethod {
                site: None,
                module: pending.module,
                span: pending.span,
                name: pending.name,
                receiver: component.clone(),
                arguments,
                result: answer.clone(),
                reach: Reach::Called,
                resolved: false,
                owed: None,
            });
        }
        if let Some(site) = pending.site {
            self.checked.methods.insert(site, pending.name);
        }
        Ok(Some(true))
    }

    /// The visible methods named at `pending` that its receiver could have.
    fn owned_methods(&self, pending: &PendingMethod) -> Vec<MethodImpl> {
        let implementations = self
            .methods
            .get(&pending.name)
            .map_or(&[][..], Vec::as_slice);
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
        // A value's own type's methods are its, wherever the value went and
        // whether or not its type was imported; one not yet known may have
        // only those in scope, which are what inference chooses among.
        let visible = &self.visible_methods[&pending.module];
        implementations
            .iter()
            .filter(|implementation| match &receiver {
                Ty::Named(owner, _) => implementation.owner == *owner,
                Ty::Var(_) => visible.contains(&implementation.target),
                _ => false,
            })
            .cloned()
            .chain(bounded)
            .collect()
    }

    /// Whether `implementation` takes the arguments given at `pending`.
    fn fits(&mut self, pending: &PendingMethod, implementation: &MethodImpl) -> bool {
        let symbols = self.symbols;
        self.infer
            .probe(|trial| apply_signature(trial, pending, &implementation.scheme, symbols).is_ok())
    }

    fn apply_field(&mut self, pending: &PendingMethod, scheme: &Scheme) -> Result<(), CheckError> {
        apply_signature(&mut self.infer, pending, scheme, self.symbols)
            .map_err(|message| failure(pending.module, pending.span, message))?;
        // A bound a use owes, met by a field, names nothing where it stands.
        if let Some(site) = pending.site {
            self.checked.projections.insert(site, pending.name);
        }
        Ok(())
    }

    fn apply_method(
        &mut self,
        pending: &PendingMethod,
        implementation: &MethodImpl,
    ) -> Result<(), CheckError> {
        let symbols = self.symbols;
        let replacements = self
            .infer
            .attempt(|infer| apply_signature(infer, pending, &implementation.scheme, symbols))
            .map_err(|message| {
                let refused = failure(pending.module, pending.span, message);
                match self.elsewhere(pending, implementation) {
                    Some(help) => refused.help(help),
                    None => refused,
                }
            })?;
        // An obligation names nothing where it stands; a call through a
        // bound names its implementation only once it is specialized; a call
        // of an implementation owes that implementation's own bounds.
        if implementation.bound {
            if let Some(site) = pending.site {
                self.bound_sites.push((
                    pending.module,
                    pending.span,
                    site,
                    pending.receiver.clone(),
                    pending.name,
                ));
            }
        } else {
            if let Some(site) = pending.site {
                self.checked.methods.insert(site, implementation.target);
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

    /// Another type's method of the name `tried` has, which takes the
    /// receiver and the arguments as they are, as `Str.join` takes a list:
    /// how to call it, where there is one.
    fn elsewhere(&mut self, pending: &PendingMethod, tried: &MethodImpl) -> Option<String> {
        if pending.reach == Reach::Type {
            return None;
        }
        let others: Vec<MethodImpl> = self
            .methods
            .get(&pending.name)?
            .iter()
            .filter(|other| other.owner != tried.owner && !other.bound)
            .cloned()
            .collect();
        let fitting: Vec<_> = others
            .iter()
            .filter(|other| self.fits(pending, other))
            .collect();
        let [other] = fitting.as_slice() else {
            return None;
        };
        let called = format!(
            "{}.{}",
            spelled(other.owner, self.symbols),
            spelled(pending.name, self.symbols)
        );
        Some(format!(
            "`{called}` fits, taking what stands before the `.` first: `{called}(value, …)`"
        ))
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
        self.infer
            .unify(actual, expected)
            .map_err(|reason| self.mismatch(module, span, actual, expected, &reason))
    }

    /// A pattern at `span` whose shape is `pattern` matching a value of
    /// type `matched`: the value's type is the one expected.
    fn unify_pattern_at(
        &mut self,
        module: ModuleId,
        span: super::ast::Span,
        matched: &Ty,
        pattern: &Ty,
    ) -> Result<(), CheckError> {
        self.unify_at(module, span, pattern, matched)
    }

    /// Why a value of type `actual` at `span` is not the `expected` one.
    fn mismatch(
        &self,
        module: ModuleId,
        span: super::ast::Span,
        actual: &Ty,
        expected: &Ty,
        reason: &Mismatch,
    ) -> CheckError {
        // Which tag or field does not fit is the whole of it.
        if let Mismatch::NotAmong { .. } = reason {
            return failure(module, span, reason.describe(self.symbols));
        }
        let expected = show(&self.infer.resolve(expected), self.symbols);
        let actual = show(&self.infer.resolve(actual), self.symbols);
        let error = failure(module, span, "mismatched types");
        let error = error.label(format!("expected `{expected}`, found `{actual}`"));
        match reason {
            Mismatch::Reason("incompatible types") => error,
            _ => error.note(reason.describe(self.symbols)),
        }
    }

    fn bool_type(&self) -> Ty {
        Ty::Named(self.prelude.bool_, Rc::default())
    }

    fn list_type(&self, element: Ty) -> Ty {
        Ty::Named(self.prelude.list, Rc::from([element]))
    }

    /// `ty`'s scheme, quantifying every variable in it but those `fixed`.
    fn generalize(&self, ty: &Ty, fixed: &HashSet<u32>) -> Scheme {
        let ty = self.infer.resolve(ty);
        let mut variables = free_variables(&ty);
        variables.retain(|variable| !fixed.contains(variable));
        Scheme { variables, ty }
    }

    /// Bind `name` to `scheme`, keeping `open` to the names whose schemes
    /// hold a free variable.
    fn set_value(&mut self, name: Symbol, scheme: Scheme) {
        if free_scheme(&scheme).is_empty() {
            self.open.remove(&name);
        } else {
            self.open.insert(name);
        }
        self.values.insert(name, scheme);
    }

    /// The variables free in the schemes of names other than `excluded`,
    /// which generalizing a definition of those names must leave free.
    fn fixed(&self, excluded: &HashSet<Symbol>) -> HashSet<u32> {
        self.open
            .iter()
            .filter(|name| !excluded.contains(name))
            .flat_map(|name| free_scheme(&self.values[name]))
            .collect()
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
    for (at, (argument, parameter)) in given.into_iter().zip(parameters.iter()).enumerate() {
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
                for ty in arguments.iter() {
                    collect(ty, output);
                }
            }
            Ty::Function(parameters, result) => {
                for ty in parameters.iter() {
                    collect(ty, output);
                }
                collect(result, output);
            }
            Ty::Variants(tags, tail) => {
                for (_, fields) in tags.iter() {
                    for ty in fields.iter() {
                        collect(ty, output);
                    }
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Record(fields, tail) => {
                for (_, ty) in fields.iter() {
                    collect(ty, output);
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Tuple(members) => {
                for ty in members.iter() {
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

fn validate_effects(program: &n::Program, symbols: &Symbols) -> Result<(), CheckError> {
    for function in &program.functions {
        for clause in &function.clauses {
            validate_effect_clause(function.module, clause, symbols)?;
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
        // What `?` propagates, or `return` answers, stands where it does;
        // what `is` tests is worked out first, once, so it stands there too.
        h::ExprKind::Try(value) | h::ExprKind::Return(value) | h::ExprKind::Is(value, _) => {
            validate_effect_expr(module, value, owner_effectful, stands_alone, symbols)
        }
        // A block's lines stand on their own, and its answer where the
        // block does.
        h::ExprKind::Block(body) => {
            for binding in &body.bindings {
                validate_effect_expr(module, &binding.value, owner_effectful, true, symbols)?;
            }
            validate_effect_expr(module, &body.result, owner_effectful, stands_alone, symbols)
        }
        // A loop's round is a block's lines, and what follows it stands
        // where the loop does.
        h::ExprKind::Loop(looped) => {
            for (initial, _, _) in &looped.carried {
                validate_effect_expr(module, initial, owner_effectful, false, symbols)?;
            }
            // A loop's head is worked out first, once a round or once in
            // all, before anything else the loop does.
            let head = match &looped.head {
                h::LoopHead::While(condition) => condition,
                h::LoopHead::For(_, list) => list,
            };
            validate_effect_expr(module, head, owner_effectful, true, symbols)?;
            for binding in &looped.body.bindings {
                validate_effect_expr(module, &binding.value, owner_effectful, true, symbols)?;
            }
            validate_effect_expr(module, &looped.body.result, owner_effectful, true, symbols)?;
            for binding in &looped.rest.bindings {
                validate_effect_expr(module, &binding.value, owner_effectful, true, symbols)?;
            }
            validate_effect_expr(
                module,
                &looped.rest.result,
                owner_effectful,
                stands_alone,
                symbols,
            )
        }
        h::ExprKind::Continue(values) | h::ExprKind::Break(values) => {
            values.iter().try_for_each(|value| {
                validate_effect_expr(module, value, owner_effectful, false, symbols)
            })
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
        // An arm stands where the `is` does, as a branch does.
        h::ExprKind::Match(value, arms) => {
            validate_effect_expr(module, value, owner_effectful, stands_alone, symbols)?;
            arms.iter().try_for_each(|arm| {
                if let Some(guard) = &arm.guard {
                    validate_effect_expr(module, guard, owner_effectful, false, symbols)?;
                }
                validate_effect_expr(module, &arm.body, owner_effectful, stands_alone, symbols)
            })
        }
        // A condition is worked out first, once, and a branch is taken
        // after it: each stands where the `if` does.
        h::ExprKind::If(condition, yes, no) => {
            validate_effect_expr(module, condition, owner_effectful, stands_alone, symbols)?;
            validate_effect_expr(module, yes, owner_effectful, stands_alone, symbols)?;
            validate_effect_expr(module, no, owner_effectful, stands_alone, symbols)
        }
        h::ExprKind::Local(_)
        | h::ExprKind::Global(_)
        | h::ExprKind::Constructor(_)
        | h::ExprKind::Tag(_)
        | h::ExprKind::Dual(_)
        | h::ExprKind::Associated(..)
        | h::ExprKind::Number(_)
        | h::ExprKind::Decimal(..) => Ok(()),
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
    // An effect inside an expression would happen in an order the line's
    // reader must work out; standing alone, it happens where its line is.
    if !stands_alone {
        return Err(failure(
            module,
            span,
            format!(
                "effect `{}` must stand on its own",
                source_name(symbols, effect)
            ),
        )
        .label("inside an expression")
        .help("bind what it answers to a name on a line of its own, and use the name here"));
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
    definitions: &HashMap<Symbol, &n::Function>,
    unsigned: &HashSet<Symbol>,
    methods: &HashMap<Symbol, Vec<UnsignedMethod>>,
    symbols: &Symbols,
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
        for clause in &definitions[name].clauses {
            clause_globals(clause, symbols, &mut dependencies);
        }
        // A member spelled as an unsigned method may be it, which is
        // settled before whatever calls it.
        let spelled: Vec<Symbol> = dependencies
            .iter()
            .filter_map(|dependency| methods.get(dependency))
            .flatten()
            .map(|method| method.name)
            .collect();
        edges[from].extend(
            dependencies
                .into_iter()
                .chain(spelled)
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

/// The member an operator is spelled as, called on its left operand.
const fn binary_member(operator: super::ast::BinaryOp) -> &'static str {
    match operator {
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
    }
}

const fn unary_member(operator: super::ast::UnaryOp) -> &'static str {
    match operator {
        super::ast::UnaryOp::Negate => "neg",
        super::ast::UnaryOp::Not => "not",
    }
}

fn clause_globals(clause: &h::Clause, symbols: &Symbols, output: &mut HashSet<Symbol>) {
    if let Some(guard) = &clause.guard {
        expr_globals(guard, symbols, output);
    }
    for binding in &clause.body.bindings {
        expr_globals(&binding.value, symbols, output);
    }
    expr_globals(&clause.body.result, symbols, output);
}

fn expr_globals(expression: &h::Expr, symbols: &Symbols, output: &mut HashSet<Symbol>) {
    match &expression.kind {
        h::ExprKind::Loop(looped) => {
            for (initial, _, _) in &looped.carried {
                expr_globals(initial, symbols, output);
            }
            match &looped.head {
                h::LoopHead::While(condition) => expr_globals(condition, symbols, output),
                h::LoopHead::For(_, list) => expr_globals(list, symbols, output),
            }
            for body in [&looped.body, &looped.rest] {
                for binding in &body.bindings {
                    expr_globals(&binding.value, symbols, output);
                }
                expr_globals(&body.result, symbols, output);
            }
        }
        h::ExprKind::Continue(values) | h::ExprKind::Break(values) => {
            for value in values {
                expr_globals(value, symbols, output);
            }
        }
        h::ExprKind::Block(body) => {
            for binding in &body.bindings {
                expr_globals(&binding.value, symbols, output);
            }
            expr_globals(&body.result, symbols, output);
        }
        h::ExprKind::Global(global) => {
            output.insert(*global);
        }
        h::ExprKind::String(parts) => {
            for part in parts {
                if let h::StringPart::Splice(expression) = part {
                    expr_globals(expression, symbols, output);
                }
            }
        }
        h::ExprKind::List(elements, rest) => {
            for expression in elements {
                expr_globals(expression, symbols, output);
            }
            if let Some(rest) = rest {
                expr_globals(rest, symbols, output);
            }
        }
        h::ExprKind::Record(fields) => {
            for (_, value) in fields {
                expr_globals(value, symbols, output);
            }
        }
        h::ExprKind::Update(base, fields) => {
            expr_globals(base, symbols, output);
            for (_, value) in fields {
                expr_globals(value, symbols, output);
            }
        }
        h::ExprKind::Tuple(members) => {
            for member in members {
                expr_globals(member, symbols, output);
            }
        }
        h::ExprKind::Lambda(_, body) | h::ExprKind::Try(body) | h::ExprKind::Return(body) => {
            expr_globals(body, symbols, output);
        }
        h::ExprKind::If(condition, yes, no) => {
            for each in [condition, yes, no] {
                expr_globals(each, symbols, output);
            }
        }
        h::ExprKind::Is(value, _) => expr_globals(value, symbols, output),
        h::ExprKind::Match(value, arms) => {
            expr_globals(value, symbols, output);
            for arm in arms {
                for each in arm.guard.iter().chain([&arm.body]) {
                    expr_globals(each, symbols, output);
                }
            }
        }
        // An operator is its member's spelling, as a dot call is.
        h::ExprKind::Unary(operator, value) => {
            output.extend(symbols.find(unary_member(*operator)));
            expr_globals(value, symbols, output);
        }
        h::ExprKind::Call(head, arguments) => {
            expr_globals(head, symbols, output);
            for argument in arguments {
                expr_globals(argument, symbols, output);
            }
        }
        // A member's spelling too, which names every method spelled so
        // that a definition without a signature may be.
        h::ExprKind::Method(head, member, arguments) => {
            output.insert(*member);
            expr_globals(head, symbols, output);
            for argument in arguments {
                expr_globals(argument, symbols, output);
            }
        }
        h::ExprKind::Member(head, member) => {
            output.insert(*member);
            expr_globals(head, symbols, output);
        }
        h::ExprKind::Binary(operator, left, right) => {
            output.extend(symbols.find(binary_member(*operator)));
            expr_globals(left, symbols, output);
            expr_globals(right, symbols, output);
        }
        h::ExprKind::Local(_)
        | h::ExprKind::Constructor(_)
        | h::ExprKind::Tag(_)
        | h::ExprKind::Dual(_)
        | h::ExprKind::Associated(..)
        | h::ExprKind::Number(_)
        | h::ExprKind::Decimal(..) => {}
    }
}

fn collect_pattern_locals(pattern: &h::Pattern, output: &mut Vec<h::LocalId>) {
    match pattern {
        h::Pattern::Bind(local) => output.push(*local),
        h::Pattern::As(local, pattern) => {
            output.push(*local);
            collect_pattern_locals(pattern, output);
        }
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
        h::Pattern::Ending(front, last) => {
            collect_pattern_locals(front, output);
            for element in last {
                collect_pattern_locals(element, output);
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
        // Every alternative binds the same locals.
        h::Pattern::Or(alternatives) => collect_pattern_locals(&alternatives[0], output),
        h::Pattern::Wild
        | h::Pattern::Number { .. }
        | h::Pattern::Range(..)
        | h::Pattern::String(_) => {}
    }
}

/// The test a pattern makes that only a clause can, `range`, `string` or
/// `list's end`, wherever in it one is.
fn test_in(pattern: &h::Pattern) -> Option<&'static str> {
    match pattern {
        h::Pattern::Range(..) => Some("range"),
        h::Pattern::String(_) => Some("string"),
        h::Pattern::Ending(..) => Some("list's end"),
        h::Pattern::Constructor(_, fields)
        | h::Pattern::Tag(_, fields)
        | h::Pattern::Dual(_, fields)
        | h::Pattern::Tuple(fields)
        | h::Pattern::Or(fields) => fields.iter().find_map(test_in),
        h::Pattern::List(fields, rest) => fields.iter().chain(rest.as_deref()).find_map(test_in),
        h::Pattern::Record(fields, _) => fields.iter().find_map(|(_, field)| test_in(field)),
        h::Pattern::As(_, pattern) => test_in(pattern),
        h::Pattern::Wild | h::Pattern::Bind(_) | h::Pattern::Number { .. } => None,
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
        // A type not yet known is shown as a signature writes one to be
        // inferred: its number is the checker's, and says nothing.
        Ty::Var(_) => "_".to_owned(),
        Ty::Rigid(variable) => format!("'a{variable}"),
        Ty::Named(name, arguments) if arguments.is_empty() => spelled(*name, symbols).to_owned(),
        Ty::Named(name, arguments) => format!(
            "{}({})",
            spelled(*name, symbols),
            arguments
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        // One parameter needs no parentheses, unless it is a tuple or a
        // function, whose own would be read as the list's.
        Ty::Function(parameters, result) => match &**parameters {
            [one] if !matches!(one, Ty::Tuple(_) | Ty::Function(..)) => {
                format!("{} -> {}", show(one, symbols), show(result, symbols))
            }
            _ => format!(
                "({}) -> {}",
                parameters
                    .iter()
                    .map(|ty| show(ty, symbols))
                    .collect::<Vec<_>>()
                    .join(", "),
                show(result, symbols)
            ),
        },
        // An open row shows its rest as `*`: the tags a caller may add.
        Ty::Variants(tags, tail) => {
            let mut shown: Vec<_> = tags
                .iter()
                .map(|(name, fields)| {
                    if fields.is_empty() {
                        spelled(*name, symbols).to_owned()
                    } else {
                        let fields: Vec<_> = fields.iter().map(|ty| show(ty, symbols)).collect();
                        format!("{}({})", spelled(*name, symbols), fields.join(", "))
                    }
                })
                .collect();
            // A rigid rest is a caller's: where it shows, in the body it
            // belongs to, the row is exactly its tags.
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("[{}]", shown.join(", "))
        }
        Ty::Record(fields, tail) => {
            let mut shown: Vec<_> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", symbols.text(*name), show(ty, symbols)))
                .collect();
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("{{{}}}", shown.join(", "))
        }
        Ty::Tuple(members) => format!(
            "({})",
            members
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(crate) fn failure(
    module: ModuleId,
    span: super::ast::Span,
    message: impl Into<String>,
) -> CheckError {
    CheckError {
        module,
        span,
        message: message.into(),
        advice: Advice::default(),
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
            self.write("bool.fn", "export {Bool.*}\nBool : [False, True].(not : Bool -> Bool\nnot(False) -> True\nnot(True) -> False\nand : (Bool, Bool) -> Bool\nand(True, True) -> True\nand(_, _) -> False\nor : (Bool, Bool) -> Bool\nor(False, False) -> False\nor(_, _) -> True)\n");
            self.write("nat.fn", "export {Nat.*}\nNat : [Zero, Succ(Nat)].(add : (Nat, Nat) -> Nat\nadd(0, y) -> y\nadd(Succ(n), y) -> Succ(n.add(y)))\n");
            self.write(
                "int.fn",
                "export {Int.*}\nInt : [Pos(Nat), NegSucc(Nat)].(of_nat : Nat -> Int\nof_nat(n) -> Pos(n)\nneg : Int -> Int\nneg(i) -> i)\n",
            );
            self.write("u8.fn", "export {U8}\nU8 : Nat\n");
            self.write(
                "list.fn",
                "export {List.*}\nList(a) : [Nil, Cons(a, List(a))].(len : List(a) -> Nat\nlen(_) -> 0\ntake : (List(a), Nat) -> List(a)\ntake(values, _) -> values\ndrop : (List(a), Nat) -> List(a)\ndrop(values, _) -> values)\n",
            );
            self.write(
                "str.fn",
                "export {Str}\nStr : List(U8).(concat : (Str, Str) -> Str\nconcat(left, _) -> left\nequals : (Str, Str) -> Bool\nequals(_, _) -> False)\n",
            );
            self.write(
                "result.fn",
                "export {Result.*}\nResult(a, e) : [Ok(a), Err(e)]\n",
            );
            self.write(
            "order.fn",
            "export {Order.*}\nOrder : [Lt, Eq, Gt].(lt : Order -> Bool\nlt(Lt) -> True\nlt(_) -> False\nle : Order -> Bool\nle(Gt) -> False\nle(_) -> True\ngt : Order -> Bool\ngt(Gt) -> True\ngt(_) -> False\nge : Order -> Bool\nge(Lt) -> False\nge(_) -> True\neq : Order -> Bool\neq(Eq) -> True\neq(_) -> False\nor : (Order, Order) -> Order\nor(Eq, next) -> next\nor(decided, _) -> decided)\n",
        );
            let standard = self.write(
                "standard.fn",
                "package {}\nimport bool {Bool.*}\nimport order {Order.*}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport result {Result.*}\nimport str {Str}\nexport {Bool.*, Order.*, Nat.*, Int.*, U8, List.*, Result.*, Str}\n",
            );
            let entry = self.write("main.fn", entry_source);
            let host = self.write("host.fn", "export {Host}\nHost : {argc: Nat}\n");
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

    fn expressions(checked: &CheckedProgram) -> Vec<&crate::typed::Expr> {
        use crate::typed::{Definition, ExprKind};
        let mut waiting = Vec::new();
        for function in &checked.resolved.program.functions {
            if let Definition::Body(clauses) = &function.definition {
                for clause in clauses {
                    waiting.extend(clause.guard.iter());
                    waiting.extend(clause.body.bindings.iter().map(|b| &b.value));
                    waiting.push(&clause.body.result);
                }
            }
        }
        let mut expressions = Vec::new();
        while let Some(expr) = waiting.pop() {
            expressions.push(expr);
            match &expr.kind {
                ExprKind::Construct(_, fields)
                | ExprKind::Tuple(fields)
                | ExprKind::Method(_, fields) => waiting.extend(fields),
                ExprKind::Record(fields) => waiting.extend(fields.iter().map(|(_, e)| e)),
                ExprKind::Update(base, fields) => {
                    waiting.push(base);
                    waiting.extend(fields.iter().map(|(_, e)| e));
                }
                ExprKind::Call(head, args) => {
                    waiting.push(head);
                    waiting.extend(args);
                }
                ExprKind::Lambda(_, value)
                | ExprKind::Is(value, _)
                | ExprKind::Project(value, _)
                | ExprKind::Widen(value)
                | ExprKind::Try(value)
                | ExprKind::Return(value) => waiting.push(value),
                ExprKind::If(condition, yes, no) => {
                    waiting.extend([condition, yes, no].map(|e| &**e));
                }
                ExprKind::Match(value, arms) => {
                    waiting.push(value);
                    for arm in arms {
                        waiting.extend(arm.guard.iter().chain([&arm.body]));
                    }
                }
                ExprKind::Loop(looped) => {
                    waiting.extend(looped.carried.iter().map(|(initial, _, _)| initial));
                    waiting.push(match &looped.head {
                        crate::typed::LoopHead::While(condition) => condition,
                        crate::typed::LoopHead::For(_, list) => list,
                    });
                    for body in [&looped.body, &looped.rest] {
                        waiting.extend(body.bindings.iter().map(|b| &b.value));
                        waiting.push(&body.result);
                    }
                }
                ExprKind::Continue(values) | ExprKind::Break(values) => waiting.extend(values),
                ExprKind::Block(body) => {
                    waiting.extend(body.bindings.iter().map(|b| &b.value));
                    waiting.push(&body.result);
                }
                ExprKind::Local(_)
                | ExprKind::Function(_)
                | ExprKind::Constructor(_)
                | ExprKind::Literal(_)
                | ExprKind::Numeral(_) => {}
            }
        }
        expressions
    }

    fn methods(checked: &CheckedProgram) -> Vec<Symbol> {
        expressions(checked)
            .into_iter()
            .filter_map(|expr| match expr.kind {
                crate::typed::ExprKind::Method(crate::typed::Target::Direct(target), _) => {
                    Some(target)
                }
                _ => None,
            })
            .collect()
    }

    #[test]
    fn declarations_group_clauses_and_lift_unsigned_methods() {
        let fixture = Fixture::new();
        let (_, resolved) = fixture.load(
            "pick : Nat -> Nat\npick(0) -> 1\npick(_) -> 2\n\
             external : Nat -> Nat\n\
             Switch : [Off, On].(flip(Off) -> On\nflip(On) -> Off)\n",
        );
        let resolved = n::normalize(resolved);
        let named = |suffix| {
            resolved
                .program
                .functions
                .iter()
                .find(|function| resolved.symbols.text(function.name).ends_with(suffix))
                .unwrap()
        };
        let pick = named("$$pick");
        assert!(pick.signature.is_some());
        assert_eq!(pick.clauses.len(), 2);
        for (clause, expected) in pick.clauses.iter().zip([1u32, 2]) {
            assert_eq!(
                clause.body.result.kind,
                h::ExprKind::Number(expected.into())
            );
        }
        assert!(named("$$external").clauses.is_empty());
        assert!(named("$$external").signature.is_some());
        let method = named("Switch.flip");
        assert!(method.signature.is_none());
        assert_eq!(method.clauses.len(), 2);
        assert!(resolved.program.data.contains_key(&method.owner.unwrap()));
    }

    #[test]
    fn context_selects_nat_int_and_str_elaboration() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "natural : Nat\nnatural = 42\ninteger : Int\ninteger = -42\ntext : Str\ntext = \"é\"\n",
        );
        let checked = type_check(n::normalize(resolved), prelude.clone()).unwrap();
        let entry = *checked.resolved.package.last().unwrap();
        let expressions: Vec<_> = checked
            .resolved
            .program
            .functions
            .iter()
            .filter(|function| function.module == entry)
            .flat_map(|function| match &function.definition {
                crate::typed::Definition::Body(clauses) => clauses.as_slice(),
                crate::typed::Definition::External(_) => &[],
            })
            .map(|clause| &clause.body.result)
            .collect();
        assert_eq!(expressions.len(), 3);
        for ty in [prelude.str_, prelude.nat, prelude.int] {
            assert!(
                expressions
                    .iter()
                    .any(|expr| expr.ty == InferredType::Named(ty, Vec::new())
                        && matches!(expr.kind, crate::typed::ExprKind::Literal(_)))
            );
        }
    }

    #[test]
    fn elaboration_preserves_unwrapped_expression_sites() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "Label : [Label].(to_str : Label -> Str\nto_str(_) -> \"label\")\n\
             text : Label -> Str\ntext(value) -> \"${value}\"\n\
             rest : List(Nat) -> List(Nat)\nrest(values) -> [*values]\n",
        );
        let resolved = n::normalize(resolved);
        let expected: Vec<_> = resolved
            .program
            .functions
            .iter()
            .filter_map(|function| {
                let expression = &function.clauses.first()?.body.result;
                let inner = match &expression.kind {
                    h::ExprKind::String(parts) => match parts.as_slice() {
                        [h::StringPart::Splice(splice)] => splice,
                        _ => return None,
                    },
                    h::ExprKind::List(elements, Some(rest)) if elements.is_empty() => rest,
                    _ => return None,
                };
                Some((function.name, inner.site, inner.span))
            })
            .collect();
        assert_eq!(expected.len(), 2);
        let checked = type_check(resolved, prelude).unwrap();
        for (name, site, span) in expected {
            let function = checked
                .resolved
                .program
                .functions
                .iter()
                .find(|function| function.name == name)
                .unwrap();
            let crate::typed::Definition::Body(clauses) = &function.definition else {
                panic!("a written body")
            };
            let expression = &clauses[0].body.result;
            assert_eq!(expression.site, site);
            assert_eq!(expression.span, span);
        }
    }

    #[test]
    fn typed_hir_carries_projections_widenings_and_generic_operations() {
        use crate::typed::{ExprKind, Target};
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "field : {value: Nat} -> Nat\nfield(record) -> record.value\n\
             wide : [A] -> [A, B]\nwide(x) -> x\n\
             Flip : [Off, On].(not : Flip -> Flip\nnot(Off) -> On\nnot(On) -> Off)\n\
             flip(x) -> x.not()\n",
        );
        let checked = type_check(n::normalize(resolved), prelude).unwrap();
        let expressions = expressions(&checked);
        assert!(
            expressions
                .iter()
                .any(|expr| matches!(expr.kind, ExprKind::Project(..)))
        );
        assert!(
            expressions
                .iter()
                .any(|expr| matches!(expr.kind, ExprKind::Widen(_)))
        );
        assert!(
            expressions
                .iter()
                .any(|expr| matches!(expr.kind, ExprKind::Method(Target::Bound { .. }, _)))
        );
    }

    #[test]
    fn never_is_an_ordinary_constructor_name() {
        let fixture = Fixture::new();
        let (prelude, resolved) =
            fixture.load("Outcome : [Never]\nvalue : Outcome\nvalue = Never\n");
        type_check(n::normalize(resolved), prelude).unwrap();
    }

    #[test]
    fn polymorphic_functions_are_instantiated_at_each_call() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "id : a -> a\nid(x) -> x\nnatural : Nat\nnatural = id(1)\ninteger : Int\ninteger = id(-1)\n",
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
        let checked = type_check(n::normalize(resolved), prelude).unwrap();
        let scheme = &checked
            .resolved
            .program
            .functions
            .iter()
            .find(|function| function.name == id)
            .unwrap()
            .scheme;
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
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert!(failure.message.contains("numeral") || failure.message.contains("mismatch"));
    }

    #[test]
    fn unsigned_definitions_are_generalized_between_components() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture
            .load("id(x) -> x\nnatural : Nat\nnatural = id(1)\ninteger : Int\ninteger = id(-1)\n");
        type_check(n::normalize(resolved), prelude).unwrap();
    }

    /// A function is passed into a call; bound to a name, it would be a
    /// value a program holds.
    #[test]
    fn a_function_is_not_bound() {
        let fixture = Fixture::new();
        let (prelude, resolved) =
            fixture.load("id : a -> a\nid(x) -> x\nlocal : Int\nlocal = (\n  f = id\n  f(-1)\n)\n");
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert!(
            failure.message.contains("passed straight into a call"),
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
        let checked = type_check(n::normalize(resolved), prelude.clone()).unwrap();
        let targets = methods(&checked);
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
            "Flip : [Off, On].(not : Flip -> Flip\nnot(Off) -> On\nnot(On) -> Off)\nflip(x) -> x.not()\n",
        );
        let checked = type_check(n::normalize(resolved), prelude).unwrap();
        let resolved = &checked.resolved;
        let scheme = &resolved
            .program
            .functions
            .iter()
            .find(|function| resolved.symbols.text(function.name).ends_with("$$flip"))
            .unwrap()
            .scheme;
        assert_eq!(scheme.bounds.len(), 1);
        assert_eq!(resolved.symbols.text(scheme.bounds[0].member), "not");
    }

    #[test]
    fn methods_of_unexposed_types_are_not_candidates() {
        let fixture = Fixture::new();
        fixture.write(
            "hidden.fn",
            "export {helper}\nSecret : [Hidden].(not : Secret -> Secret\nnot(Hidden) -> Hidden)\nhelper : Nat\nhelper = 0\n",
        );
        let (prelude, resolved) = fixture.load("import hidden {helper}\nchoose(x) -> x.not()\n");
        let checked = type_check(n::normalize(resolved), prelude.clone()).unwrap();
        assert!(methods(&checked).contains(&prelude.bool_not));
    }

    #[test]
    fn repository_bootstrap_checks_polymorphic_utilities() {
        let root = crate::standard_path();
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/utilities.fn");
        let loaded = modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = resolve::resolve_names(loaded).unwrap();
        let checked = type_check(n::normalize(resolved), prelude).unwrap();
        assert!(!methods(&checked).is_empty());
    }

    #[test]
    fn repository_bootstrap_exposes_arithmetic_for_nat_int_and_u8() {
        let fixture = Fixture::new();
        let entry = fixture.write(
            "arithmetic.fn",
            "nat_ops : (Nat, Nat) -> Nat\n\
             nat_ops(a, b) -> ((((a + b) - b) * b) / b) % b\n\
             int_ops : (Int, Int) -> Int\n\
             int_ops(a, b) -> ((((a + b) - b) * b) / b) % b\n\
             u8_ops : (U8, U8) -> U8\n\
             u8_ops(a, b) -> ((((a + b) - b) * b) / b) % b\n",
        );
        let root = crate::standard_path();
        let loaded = modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = resolve::resolve_names(loaded).unwrap();
        let checked = type_check(n::normalize(resolved), prelude).unwrap();
        let methods: HashSet<_> = methods(&checked)
            .into_iter()
            .map(|target| checked.resolved.symbols.text(target))
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
        let (prelude, resolved) = fixture.load("stop! : Nat -> Nat\nbad : Nat\nbad = stop!(0)\n");
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert!(
            failure
                .message
                .contains("pure definitions cannot call effect")
        );

        let (prelude, resolved) = fixture.load(
            "stop! : Nat -> Nat\nid : Nat -> Nat\nid(n) -> n\nbad! : Nat -> Nat\nbad!(n) -> id(stop!(n))\n",
        );
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert!(failure.message.contains("must stand on its own"));
    }

    /// A constructor handed where its position wants another type says what
    /// it builds and what is wanted, rather than that there is no method.
    #[test]
    fn a_constructor_where_another_type_is_wanted_says_both() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad = Zero.add(True)\n");
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert_eq!(failure.message, "mismatched types");
        assert_eq!(failure.labels[0].text, "expected `Nat`, found `Bool`");
    }

    #[test]
    fn a_negative_nat_is_rejected() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad = -1\n");
        let failure = type_check(n::normalize(resolved), prelude).unwrap_err();
        assert!(failure.message.contains("negative numeral"));
    }
}
