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
//! settled first, so a row a call or a field hands back meets it as its own.
//! Clauses or an `is`'s arms taking a row apart without a catch-all close it. A word a declaration claims waits, as a method does,
//! for its position's type to choose between the tag and the constructor.
//!
//! `where` bounds are structural. A signed body meets its written bounds at
//! its rigid variables; a use of a bounded definition owes its bounds, met
//! where the use's types are known or owed in turn: a bound owed again
//! while it is being met is met there, and one owed again at a larger type
//! is refused, as it would owe another each time. An unsigned component's
//! methods still open on a variable it generalizes become its bounds, as do
//! its field reads off one, met by a record or a declared type having the
//! field, and its numerals of a generic type, through `of_nat`.
//! Specialization calls each concrete type's own member, or reads its field.
//!
//! [`type_check`] runs the parts in order, each in a module of its own:
//!
//! - `declared`: what the declarations alone refuse, before inference.
//! - `effects`: where an effect may be called.
//! - `environment`: each type, signature and method as inference reads it.
//! - `components`: the order unsigned definitions are inferred in.
//! - this module: inference over clauses, patterns and expressions.
//! - `unify`: types as inference holds them, and unification.
//! - `pending`: what waits for a type to decide it, and settling it.
//! - `joins`: where ways meet, and a way of type `[]` takes the others' type.
//! - `elaborate`: the inferred facts written onto typed HIR.

#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::blessed::{self, LiteralExpr, PreludeIds};
use super::context::Context;
use super::diagnostic::{Advised, Diagnostic, Refusal, counted, given};
use super::hir as h;
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

/// Noted where a value of type `{}` stands where another is wanted.
const ANSWERS_NOTHING: &str =
    "a block whose last line is a binding, a loop or a leaving line answers `{}`";

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

mod components;
mod declared;
mod effects;
mod elaborate;
mod environment;
mod joins;
mod pending;
mod unify;

use components::{binary_member, components, unary_member};
use joins::{Join, Meeting, PendingWay, Ways};
use unify::{
    Infer, Mismatch, Scheme, Ty, free_scheme, free_variables, public_type, show, substitute,
};

/// Infer every definition, check declared signatures, resolve methods, and
/// elaborate literals: `program` as typed HIR.
///
/// Type variables in signatures are universally quantified at each use.
/// Unsigned recursive groups are inferred monomorphically and generalized only
/// after the group closes. Each elaboration decision is written on its
/// expression. `where` calls remain explicit until specialization selects
/// their concrete implementations.
///
/// # Errors
///
/// Reports declarations that cannot stand, misplaced effects, and type,
/// arity, ambiguous-method, unsupported-constraint and literal protocol
/// failures.
pub fn type_check(
    program: n::Program,
    cx: &mut Context,
) -> Result<crate::typed::Program, Diagnostic> {
    let facts = infer(&program, cx).map_err(|refusal| cx.told(refusal))?;
    Ok(elaborate::finish(
        program,
        facts,
        &cx.prelude,
        &mut cx.sites,
    ))
}

/// What inference finds of `program`, once its declarations and effects are
/// known to stand.
fn infer(program: &n::Program, cx: &Context) -> Result<Facts, Refusal> {
    declared::check(program, cx.host_module, &cx.symbols)?;
    effects::check(program, &cx.symbols)?;
    Checker::new(program, &cx.symbols, &cx.prelude)?.check(program)
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
    /// Whether a numeral of the type asks it, its `of_nat`, `of_decimal`
    /// or `neg`: where a use leaves the type undecided, the numeral takes
    /// its default there.
    numeral: bool,
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
            numeral: self.numeral,
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
    /// The pending method whose implementation owes this, where one does.
    owing: Option<usize>,
    /// Whether a numeral of the receiver asks it; see [`Bound::numeral`].
    numeral: bool,
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
    handings: usize,
    ways: usize,
}

/// An expression handed a name or a lambda, which may be a function: a
/// record, tuple or list written with it, or a call handed it, which may
/// answer what it builds from it.
#[derive(Clone, Debug)]
struct Handing {
    module: ModuleId,
    span: super::ast::Span,
    ty: Ty,
    /// The type of each function value it is handed.
    handed: Vec<Ty>,
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
    /// Whether it was written as a character literal.
    character: bool,
    ty: Ty,
    resolved: bool,
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

/// Whether `kind` is one that may stand for a function: a name, or a
/// lambda.
const fn names_a_function(kind: &h::ExprKind) -> bool {
    matches!(
        kind,
        h::ExprKind::Local(_)
            | h::ExprKind::Global(_)
            | h::ExprKind::Constructor(_)
            | h::ExprKind::Tag(_)
            | h::ExprKind::Associated(..)
            | h::ExprKind::Dual(_)
            | h::ExprKind::Lambda(..)
    )
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
    /// The pending method whose implementation is being applied, which
    /// owes the bounds that implementation has.
    obliging: Option<usize>,
    pending_numerals: Vec<PendingNumeral>,
    pending_tags: Vec<PendingTag>,
    pending_bare: Vec<PendingBare>,
    pending_closings: Vec<PendingClosing>,
    /// Every join checked, and the ways into them whose types wait.
    joins: Vec<Join>,
    pending_ways: Vec<PendingWay>,
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
    /// The join of what the clause or lambda being checked answers,
    /// innermost last, which a `return` or a `?` in it answers early. A
    /// guard answers nothing.
    answers: Vec<Option<usize>>,
    /// Where the signature of the definition being checked writes its
    /// result's type, which a clause's answer is held to.
    written_result: Option<super::ast::Span>,
    /// Where each definition is introduced: its signature, or where it has
    /// none, its first clause.
    defined: HashMap<Symbol, (ModuleId, super::ast::Span)>,
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
    /// Each expression handed a name or a lambda, in the order checked,
    /// for [`Self::stored_function`] to look at once types are known.
    handings: Vec<Handing>,
    clause_types: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty, Vec<Bound>)>,
    widenings: Vec<(ModuleId, super::ast::Span, h::SiteId, Ty)>,
    checked: Facts,
}

impl Checker<'_> {
    fn check(mut self, program: &n::Program) -> Result<Facts, Refusal> {
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
                                "clause takes {} but its signature takes {}",
                                counted(arity, "pattern"),
                                counted(signature.parameters.len(), "parameter")
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
            // A definition's clauses answer one join, its result.
            for name in &component {
                let function = definitions[name];
                let Ty::Function(_, result) = self.infer.resolve(&monotypes[name]) else {
                    unreachable!("a definition's type is a function")
                };
                let ways = Ways::Answers(None);
                let join = self.join(
                    function.module,
                    function.clauses[0].span,
                    ways,
                    (*result).clone(),
                );
                for clause in &function.clauses {
                    self.check_clause(function.module, clause, &monotypes[name], Some(join))?;
                }
                self.close_join(join)?;
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
                    let message = format!("`{}` answers a function", self.symbols.spelling(*name));
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
            // This component's clauses were checked last, so they are
            // found at the end, however many came before.
            for name in &component {
                for clause in &definitions[name].clauses {
                    if let Some(site) = self
                        .clause_types
                        .iter_mut()
                        .rev()
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
                self.written_result = function
                    .signature
                    .as_ref()
                    .and_then(|signature| signature.result_span);
                let checked = self.check_clause(module, clause, &ty, None);
                self.written_result = None;
                checked?;
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

    /// A clause of a definition of type `function`, answering `join`, or
    /// where none is given, a join of its own.
    fn check_clause(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        function: &Ty,
        join: Option<usize>,
    ) -> Result<(), Refusal> {
        let marks = self.marks();
        let outer = self.clause_marks.replace(marks);
        let checked = self.check_clause_within(module, clause, (function, join), marks);
        self.clause_marks = outer;
        checked
    }

    fn check_clause_within(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        (function, join): (&Ty, Option<usize>),
        marks: Marks,
    ) -> Result<(), Refusal> {
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
                    "clause takes {} but its signature takes {}",
                    counted(clause.patterns.len(), "pattern"),
                    counted(parameters.len(), "parameter")
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
        let own = join.is_none();
        let ways = Ways::Answers(self.written_result);
        let join = join.unwrap_or_else(|| self.join(module, clause.span, ways, (*result).clone()));
        self.answers.push(Some(join));
        let checked = self.clause_body(module, clause, &mut locals, (join, marks));
        self.answers.pop();
        checked?;
        if own {
            self.close_join(join)?;
        }
        Ok(())
    }

    /// A body's bindings, each value checked and its pattern bound before
    /// the next, and what each waits on settled at its line.
    fn bindings(
        &mut self,
        module: ModuleId,
        bindings: &[h::Binding],
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<(), Refusal> {
        for binding in bindings {
            let marks = self.marks();
            let value = self.expr(module, &binding.value, locals)?;
            let mut bound = Vec::new();
            collect_pattern_locals(&binding.pattern, &mut bound);
            self.pattern(module, &binding.pattern, &value, locals, binding.value.span)
                .map_err(|mut error| {
                    // Arms on a line of their own, which the parser binds to
                    // `{}`: the arms answer otherwise, not a block.
                    let alone = matches!(&binding.pattern, h::Pattern::Record(fields, false) if fields.is_empty())
                        && matches!(binding.value.kind, h::ExprKind::Match(..));
                    if !alone {
                        return error;
                    }
                    error.advice().notes.retain(|note| note != ANSWERS_NOTHING);
                    error.note("arms on a line of their own go on with nothing: each arm that does not leave answers `{}`")
                })?;
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

    /// A clause's bindings and answer, a way into `join`, which is on top
    /// of [`Self::answers`], and the marks of what the clause left pending.
    fn clause_body(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        locals: &mut Vec<Option<Scheme>>,
        (join, marks): (usize, Marks),
    ) -> Result<(), Refusal> {
        self.bindings(module, &clause.body.bindings, locals)?;
        let actual = self.expr(module, &clause.body.result, locals)?;
        // What the answer's type waits on -- a method's receiver, a
        // constructor's pattern, a field read -- is settled first, so a
        // closed row it holds meets the signature's as that row, and is
        // widened, rather than the signature's row being taken for it.
        self.settle(marks)?;
        let answered = &clause.body.result;
        self.way(
            join,
            module,
            answered,
            &actual,
            Meeting::Subsumed(answered.site),
        )
    }

    /// A loop: each carried name one type going in, within a round and
    /// after; the condition a `Bool`, or the pattern an element of the
    /// list; the body; and what follows it, whose answer the loop's is.
    fn looped(
        &mut self,
        module: ModuleId,
        looped: &h::Loop,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, Refusal> {
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
    ) -> Result<(), Refusal> {
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
    ) -> Result<(), Refusal> {
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
                character,
            } => {
                self.pending_numerals.push(PendingNumeral {
                    site: None,
                    module,
                    span,
                    magnitude: magnitude.clone(),
                    negative: *negative,
                    scale: None,
                    character: *character,
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
                        character: bound.character,
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
    ) -> Result<Ty, Refusal> {
        let children = self.expression_types.len();
        let ty = self.infer_expr(module, expression, locals)?;
        self.note_handing(module, expression, &ty, children);
        self.expression_types
            .push((module, expression.span, expression.site, ty.clone()));
        Ok(ty)
    }

    /// Note `expression` as a [`Handing`] where it is handed a name or a
    /// lambda, whose types are among those its children noted since
    /// `children`.
    fn note_handing(&mut self, module: ModuleId, expression: &h::Expr, ty: &Ty, children: usize) {
        let handed: Vec<&h::Expr> = match &expression.kind {
            h::ExprKind::List(elements, rest) => elements.iter().chain(rest.as_deref()).collect(),
            h::ExprKind::Record(fields) | h::ExprKind::Update(_, fields) => {
                fields.iter().map(|(_, value)| value).collect()
            }
            h::ExprKind::Tuple(members) => members.iter().collect(),
            h::ExprKind::Call(_, arguments) => arguments.iter().collect(),
            h::ExprKind::Method(receiver, _, arguments) => std::iter::once(receiver.as_ref())
                .chain(arguments)
                .collect(),
            _ => return,
        };
        let noted = &self.expression_types[children..];
        let mut handed_types = Vec::new();
        for child in handed {
            if !names_a_function(&child.kind) {
                continue;
            }
            let found = noted
                .iter()
                .rev()
                .find(|(_, _, site, _)| *site == child.site);
            if let Some((_, _, _, ty)) = found {
                handed_types.push(ty.clone());
            }
        }
        if handed_types.is_empty() {
            return;
        }
        self.handings.push(Handing {
            module,
            span: expression.span,
            ty: ty.clone(),
            handed: handed_types,
        });
    }

    fn infer_expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, Refusal> {
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
                self.oblige(module, expression.span, *global, &replacements)?;
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
                let Some(Some(join)) = self.answers.last().copied() else {
                    return Err(failure(
                        module,
                        expression.span,
                        "`return` answers its clause or lambda, and a guard answers nothing",
                    ));
                };
                self.way(join, module, value, &answered, Meeting::Unified)?;
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
            // body answers the one type the `is` does, unless it never answers.
            h::ExprKind::Match(value, arms) => {
                let tested = self.expr(module, value, locals)?;
                let answer = self.infer.fresh();
                let join = self.join(
                    module,
                    expression.span,
                    Ways::Arms(value.span),
                    answer.clone(),
                );
                for arm in arms {
                    self.tested_pattern(module, &arm.pattern, &tested, locals, value.span)?;
                    if let Some(guard) = &arm.guard {
                        let asked = self.expr(module, guard, locals)?;
                        let bool_ = self.bool_type();
                        self.unify_at(module, guard.span, &asked, &bool_)?;
                    }
                    let answered = self.expr(module, &arm.body, locals)?;
                    self.way(join, module, &arm.body, &answered, Meeting::Unified)?;
                }
                self.close_join(join)?;
                // Arms close the row they take apart as clauses do; a test
                // alone does not, since what it does not match goes on.
                let rows = arms
                    .iter()
                    .map(|arm| (arm.pattern.clone(), arm.guard.is_some()))
                    .collect();
                self.pending_closings.push(PendingClosing {
                    module,
                    span: value.span,
                    ty: tested,
                    rows,
                });
                Ok(answer)
            }
            // Its branches answer one type, the one the `if` answers, unless
            // one never answers.
            h::ExprKind::If(condition, yes, no) => {
                let asked = self.expr(module, condition, locals)?;
                let bool_ = self.bool_type();
                self.unify_at(module, condition.span, &asked, &bool_)?;
                let answer = self.infer.fresh();
                let join = self.join(module, expression.span, Ways::Branches, answer.clone());
                for branch in [yes, no] {
                    let answered = self.expr(module, branch, locals)?;
                    self.way(join, module, branch, &answered, Meeting::Unified)?;
                }
                self.close_join(join)?;
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
            h::ExprKind::Number(_) | h::ExprKind::Character(_) => {
                let (magnitude, character) = match &expression.kind {
                    h::ExprKind::Number(magnitude) => (magnitude.clone(), false),
                    h::ExprKind::Character(scalar) => (u32::from(*scalar).into(), true),
                    _ => unreachable!("guarded"),
                };
                let ty = self.infer.fresh();
                self.pending_numerals.push(PendingNumeral {
                    site: Some(expression.site),
                    module,
                    span: expression.span,
                    magnitude,
                    negative: false,
                    scale: None,
                    character,
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
                    character: false,
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
                let join = self.join(module, body.span, Ways::Answers(None), answer.clone());
                self.answers.push(Some(join));
                let result = self.expr(module, body, locals);
                self.answers.pop();
                let result = result?;
                self.way(join, module, body, &result, Meeting::Unified)?;
                self.close_join(join)?;
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
                Ok(Ty::Function(parameters.into(), Rc::new(answer)))
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
                if let Ty::Function(parameters, result) = self.infer.resolve(&head_type) {
                    if parameters.len() != arguments.len() {
                        return Err(self.miscounted_call(
                            module,
                            expression.span,
                            head,
                            parameters.len(),
                            arguments.len(),
                        ));
                    }
                    let given = arguments.iter().zip(&argument_types);
                    for ((argument, ty), parameter) in given.zip(parameters.iter()) {
                        self.unify_at(module, argument.span, ty, parameter)
                            .map_err(|refused| self.misfit_argument(refused, module, head))?;
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
                    h::ExprKind::Number(_) | h::ExprKind::Character(_) | h::ExprKind::Decimal(..)
                ) =>
            {
                let (magnitude, scale, character) = match &value.kind {
                    h::ExprKind::Number(magnitude) => (magnitude.clone(), None, false),
                    h::ExprKind::Character(scalar) => (u32::from(*scalar).into(), None, true),
                    h::ExprKind::Decimal(digits, scale) => (digits.clone(), Some(*scale), false),
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
                    character,
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
    ) -> Result<Ty, Refusal> {
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
                    "`{}` takes {}, but {} given",
                    spelled(self),
                    counted(parameters.len(), "argument"),
                    given(arguments.len())
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

    /// A call handing a known function more or fewer arguments than it
    /// takes. One handed fewer is not a function of the rest, as there is no
    /// partial application, so the help writes the lambda that would be.
    /// An argument that does not fit `head`'s parameter, pointing as Rust
    /// does at the function called and where it is defined.
    fn misfit_argument(&self, refused: Refusal, module: ModuleId, head: &h::Expr) -> Refusal {
        let refused = refused.also(
            module,
            head.span,
            "arguments to this function are incorrect",
        );
        let defined = match head.kind {
            h::ExprKind::Global(global) => self.defined.get(&global),
            _ => None,
        };
        match defined {
            Some(&(at, span)) => refused.also(at, span, "function defined here"),
            None => refused,
        }
    }

    fn miscounted_call(
        &self,
        module: ModuleId,
        span: super::ast::Span,
        head: &h::Expr,
        taken: usize,
        handed: usize,
    ) -> Refusal {
        let name = match head.kind {
            h::ExprKind::Global(global) => Some(self.symbols.spelling(global)),
            _ => None,
        };
        let called = name.map_or_else(
            || "the function called".to_owned(),
            |name| format!("`{name}`"),
        );
        let message = format!(
            "{called} takes {}, but {} given",
            counted(taken, "argument"),
            given(handed)
        );
        let refusal = failure(module, span, message);
        if handed == 0 || handed > taken {
            return refusal;
        }
        // The arguments left out, `x` alone or `x1, x2, …`.
        let missing = taken - handed;
        let rest: Vec<String> = if missing == 1 {
            vec!["x".to_owned()]
        } else {
            (1..=missing).map(|at| format!("x{at}")).collect()
        };
        let rest = rest.join(", ");
        let lambda = format!("|{rest}| {}(…, {rest})", name.unwrap_or("f"));
        refusal.help(format!(
            "there is no partial application: to take the rest later, write a lambda, as `{lambda}`"
        ))
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
    ) -> Result<Ty, Refusal> {
        let marks = self.clause_marks.unwrap_or_else(|| self.marks());
        let taken = self.expr(module, value, locals)?;
        let (ok, error) = (self.infer.fresh(), self.infer.fresh());
        let result = Ty::Named(self.prelude.result, Rc::from([ok.clone(), error.clone()]));
        self.unify_at(module, value.span, &taken, &result)?;
        // As for a clause's answer: the producer's own row, once what it
        // waits on is settled, is what joins the answer's.
        self.settle(marks)?;
        let Some(Some(join)) = self.answers.last().copied() else {
            return Err(failure(
                module,
                span,
                "`?` answers early from its clause or lambda, and a guard answers nothing",
            ));
        };
        // An `Err` answered early is a way of its own into the answer.
        self.join_met(join);
        let answer = self.join_answer(join);
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

    fn method_symbol(
        &self,
        module: ModuleId,
        span: super::ast::Span,
        name: &str,
    ) -> Result<Symbol, Refusal> {
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
    ) -> Result<(), Refusal> {
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
    ) -> Result<(), Refusal> {
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
    ) -> Refusal {
        // Which tag or field does not fit is the whole of it.
        if let Mismatch::NotAmong { .. } = reason {
            return failure(module, span, reason.describe(self.symbols));
        }
        let actual = self.infer.resolve(actual);
        let nothing = matches!(&actual, Ty::Record(fields, None) if fields.is_empty());
        let expected = show(&self.infer.resolve(expected), self.symbols);
        let actual = show(&actual, self.symbols);
        let error = failure(module, span, "mismatched types");
        let error = error.label(format!("expected `{expected}`, found `{actual}`"));
        let error = if nothing {
            error.note(ANSWERS_NOTHING)
        } else {
            error
        };
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
            "`{}` takes {}, but {} given",
            symbols.text(pending.name),
            counted(parameters.len() - receiver, "argument"),
            given(pending.arguments.len())
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
                "{which} of `{}` should be `{}`, but is `{}`",
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
                "`{}` answers `{}`, where `{}` is wanted",
                symbols.text(pending.name),
                show(&infer.resolve(&result), symbols),
                show(&wanted, symbols)
            ),
        })?;
    Ok(replacements)
}

fn collect_pattern_locals(pattern: &h::Pattern, output: &mut Vec<h::LocalId>) {
    match pattern {
        h::Pattern::Bind(local) => output.push(*local),
        h::Pattern::As(local, inner) => {
            output.push(*local);
            collect_pattern_locals(inner, output);
        }
        // Every alternative binds the same locals.
        h::Pattern::Or(alternatives) => collect_pattern_locals(&alternatives[0], output),
        _ => {
            for part in pattern.parts() {
                collect_pattern_locals(part, output);
            }
        }
    }
}

/// The test a pattern makes that only a clause can, `range`, `string` or
/// `list's end`, wherever in it one is.
fn test_in(pattern: &h::Pattern) -> Option<&'static str> {
    match pattern {
        h::Pattern::Range(..) => Some("range"),
        h::Pattern::String(_) => Some("string"),
        h::Pattern::Ending(..) => Some("list's end"),
        _ => pattern.parts().find_map(test_in),
    }
}

fn component_name_set(monotypes: &HashMap<Symbol, Ty>) -> HashSet<Symbol> {
    monotypes.keys().copied().collect()
}

pub(crate) fn failure(
    module: ModuleId,
    span: super::ast::Span,
    message: impl Into<String>,
) -> Refusal {
    Refusal::at(module, span, message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules;
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

        fn load(&self, entry_source: &str) -> (h::Program, Context) {
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
            let host = self.write(
                "host.fn",
                "export {Host}\nHost : {argc: Nat}.(\n  exit! : (Host, Nat) -> []\n)\n",
            );
            let loaded = modules::load_program(&entry, &standard, &host).unwrap();
            crate::resolve(loaded).unwrap()
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn expressions(checked: &crate::typed::Program) -> Vec<&crate::typed::Expr> {
        let mut expressions = Vec::new();
        for function in &checked.functions {
            if let crate::typed::Definition::Body(clauses) = &function.definition {
                for expression in clauses.iter().flat_map(crate::typed::Clause::exprs) {
                    expression.for_each_within(&mut |inner| expressions.push(inner));
                }
            }
        }
        expressions
    }

    fn methods(checked: &crate::typed::Program) -> Vec<Symbol> {
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
        let (program, cx) = fixture.load(
            "pick : Nat -> Nat\npick(0) -> 1\npick(_) -> 2\n\
             external : Nat -> Nat\n\
             Switch : [Off, On].(flip(Off) -> On\nflip(On) -> Off)\n",
        );
        let declared = n::normalize(program);
        let named = |suffix| {
            declared
                .functions
                .iter()
                .find(|function| cx.symbols.text(function.name).ends_with(suffix))
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
        assert!(declared.data.contains_key(&method.owner.unwrap()));
    }

    #[test]
    fn context_selects_nat_int_and_str_elaboration() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load(
            "natural : Nat\nnatural = 42\ninteger : Int\ninteger = -42\ntext : Str\ntext = \"é\"\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
        let entry = *cx.package.last().unwrap();
        let expressions: Vec<_> = checked
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
        for ty in [cx.prelude.str_, cx.prelude.nat, cx.prelude.int] {
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
        let (program, mut cx) = fixture.load(
            "Label : [Label].(to_str : Label -> Str\nto_str(_) -> \"label\")\n\
             text : Label -> Str\ntext(value) -> \"${value}\"\n\
             rest : List(Nat) -> List(Nat)\nrest(values) -> [*values]\n",
        );
        let declared = n::normalize(program);
        let expected: Vec<_> = declared
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
        let checked = type_check(declared, &mut cx).unwrap();
        for (name, site, span) in expected {
            let function = checked
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
        let (program, mut cx) = fixture.load(
            "field : {value: Nat} -> Nat\nfield(record) -> record.value\n\
             wide : [A] -> [A, B]\nwide(x) -> x\n\
             Flip : [Off, On].(not : Flip -> Flip\nnot(Off) -> On\nnot(On) -> Off)\n\
             flip(x) -> x.not()\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
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
        let (program, mut cx) = fixture.load("Outcome : [Never]\nvalue : Outcome\nvalue = Never\n");
        crate::checked(program, &mut cx).unwrap();
    }

    #[test]
    fn polymorphic_functions_are_instantiated_at_each_call() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load(
            "id : a -> a\nid(x) -> x\nnatural : Nat\nnatural = id(1)\ninteger : Int\ninteger = id(-1)\n",
        );
        let id = program
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
        let checked = crate::checked(program, &mut cx).unwrap();
        let scheme = &checked
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
        let (program, mut cx) = fixture.load("constant : a -> a\nconstant(_) -> 1\n");
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert!(failure.message.contains("numeral") || failure.message.contains("mismatch"));
    }

    #[test]
    fn unsigned_definitions_are_generalized_between_components() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture
            .load("id(x) -> x\nnatural : Nat\nnatural = id(1)\ninteger : Int\ninteger = id(-1)\n");
        crate::checked(program, &mut cx).unwrap();
    }

    /// A function is passed into a call; bound to a name, it would be a
    /// value a program holds.
    #[test]
    fn a_function_is_not_bound() {
        let fixture = Fixture::new();
        let (program, mut cx) =
            fixture.load("id : a -> a\nid(x) -> x\nlocal : Int\nlocal = (\n  f = id\n  f(-1)\n)\n");
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert!(
            failure.message.contains("passed straight into a call"),
            "{}",
            failure.message
        );
    }

    /// Data a generic definition builds from a function it is handed holds
    /// that function, though nothing it writes says so: refused at the
    /// call, whether a record, a tuple, a list or a tag holds it.
    #[test]
    fn a_function_is_not_stored_in_data_a_generic_definition_builds() {
        let builders = [
            "keep(f) -> {call: f}",
            "keep(f) -> (f, True)",
            "keep(f) -> [f]",
            "keep(f) -> Some(f)",
        ];
        for builder in builders {
            let fixture = Fixture::new();
            let source = format!(
                "increment : Nat -> Nat\nincrement(n) -> n + 1\n{builder}\nkept : Bool\nkept = (\n  held = keep(increment)\n  True\n)\n"
            );
            let (program, mut cx) = fixture.load(&source);
            let failure = crate::checked(program, &mut cx).unwrap_err();
            assert!(
                failure.message.contains("holds a function"),
                "{builder}: {}",
                failure.message
            );
        }
    }

    #[test]
    fn receiver_type_selects_a_method() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load(
            "increment : Nat -> Nat\nincrement(n) -> n.add(1)\ntruth : Bool -> Bool\ntruth(b) -> b.not()\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
        let targets = methods(&checked);
        assert!(targets.contains(&cx.prelude.bool_not));
        assert!(
            targets
                .iter()
                .any(|target| cx.symbols.text(*target).ends_with("Nat.add"))
        );
    }

    /// A method several types have, called on a value nothing else says the
    /// type of, is a bound the definition carries: `flip` is generic over
    /// every type with a `not`.
    #[test]
    fn a_method_several_types_have_is_a_bound() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load(
            "Flip : [Off, On].(not : Flip -> Flip\nnot(Off) -> On\nnot(On) -> Off)\nflip(x) -> x.not()\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
        let scheme = &checked
            .functions
            .iter()
            .find(|function| cx.symbols.text(function.name).ends_with("$$flip"))
            .unwrap()
            .scheme;
        assert_eq!(scheme.bounds.len(), 1);
        assert_eq!(cx.symbols.text(scheme.bounds[0].member), "not");
    }

    /// So is a method only one type in scope has: a type out of scope may
    /// have it too, as `Stdout` has `write_all!` where only `Host` is
    /// imported, and `say!` is generic over both.
    #[test]
    fn a_method_one_type_in_scope_has_is_a_bound() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load(
            "Fake : [Fake].(write_all! : (Fake, Nat) -> Nat\nwrite_all!(_, n) -> n)\nsay!(out, n) -> out.write_all!(n)\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
        let scheme = &checked
            .functions
            .iter()
            .find(|function| cx.symbols.text(function.name).ends_with("$$say!"))
            .unwrap()
            .scheme;
        assert_eq!(scheme.bounds.len(), 1);
        assert_eq!(cx.symbols.text(scheme.bounds[0].member), "write_all!");
    }

    #[test]
    fn methods_of_unexposed_types_are_not_candidates() {
        let fixture = Fixture::new();
        fixture.write(
            "hidden.fn",
            "export {helper}\nSecret : [Hidden].(not : Secret -> Secret\nnot(Hidden) -> Hidden)\nhelper : Nat\nhelper = 0\n",
        );
        // The receiver is nothing generic: what `anything` answers, which
        // nothing else says of, is the one type in scope having a `not`.
        let (program, mut cx) = fixture.load(
            "import hidden {helper}\nanything(n) -> anything(n)\nchoose(n) -> anything(n).not()\n",
        );
        let checked = crate::checked(program, &mut cx).unwrap();
        assert!(methods(&checked).contains(&cx.prelude.bool_not));
    }

    #[test]
    fn repository_bootstrap_checks_polymorphic_utilities() {
        let root = crate::standard_path();
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/utilities.fn");
        let loaded = modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let (program, mut cx) = crate::resolve(loaded).unwrap();
        let checked = crate::checked(program, &mut cx).unwrap();
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
        let (program, mut cx) = crate::resolve(loaded).unwrap();
        let checked = crate::checked(program, &mut cx).unwrap();
        let methods: HashSet<_> = methods(&checked)
            .into_iter()
            .map(|target| cx.symbols.text(target))
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
        let (program, mut cx) =
            fixture.load("stop! : Nat -> Nat\nstop!(n) -> n\nbad : Nat\nbad = stop!(0)\n");
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert!(
            failure
                .message
                .contains("pure definitions cannot call effect")
        );

        let (program, mut cx) = fixture.load(
            "stop! : Nat -> Nat\nstop!(n) -> n\nid : Nat -> Nat\nid(n) -> n\nbad! : Nat -> Nat\nbad!(n) -> id(stop!(n))\n",
        );
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert!(failure.message.contains("must stand on its own"));
    }

    /// A constructor handed where its position wants another type says what
    /// it builds and what is wanted, rather than that there is no method.
    #[test]
    fn a_constructor_where_another_type_is_wanted_says_both() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load("bad : Nat\nbad = Zero.add(True)\n");
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert_eq!(failure.message, "mismatched types");
        assert_eq!(failure.labels[0].text, "expected `Nat`, found `Bool`");
    }

    #[test]
    fn a_negative_nat_is_rejected() {
        let fixture = Fixture::new();
        let (program, mut cx) = fixture.load("bad : Nat\nbad = -1\n");
        let failure = crate::checked(program, &mut cx).unwrap_err();
        assert!(failure.message.contains("negative numeral"));
    }
}
