//! Specialize checked polymorphic HIR into concrete, still-functional terms.
//!
//! Barb has no type variables. This pass follows direct calls from one concrete
//! entry signature and clones each reachable global at every concrete function
//! type used by the program. Function values remain explicit until
//! [`crate::callbacks`] makes each into the definition it is handed to.

#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use num_bigint::BigUint;

use crate::blessed::NumeralType;
use crate::blessed::{LiteralExpr, PreludeIds};
use crate::check::{
    CheckedProgram, ClauseSite, DeferredNumeral, InferredBound, InferredScheme, InferredType,
    Reading, TypeVariable, Types,
};
use crate::hir as h;
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Type {
    Named(Symbol, Vec<Self>),
    Function(Vec<Self>, Box<Self>),
    /// A closed tag row, its tags in one order so that two spellings of one
    /// row are one type. The empty row is the type with no values.
    Variants(Vec<(Symbol, Vec<Self>)>),
    /// A closed record, its fields in one order.
    Record(Vec<(Symbol, Self)>),
    /// A positional product of two or more.
    Tuple(Vec<Self>),
}

impl Type {
    /// The empty row, which nothing inhabits.
    pub(crate) const fn empty() -> Self {
        Self::Variants(Vec::new())
    }

    /// The row holding `tags`, in the order every row keeps them.
    fn row(mut tags: Vec<(Symbol, Vec<Self>)>) -> Self {
        tags.sort_by_key(|(label, _)| *label);
        Self::Variants(tags)
    }

    pub(crate) fn function(&self) -> Option<(&[Self], &Self)> {
        let Self::Function(parameters, result) = self else {
            return None;
        };
        Some((parameters, result))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FunctionKey {
    pub(crate) name: Symbol,
    pub(crate) ty: Type,
    /// Which of the definitions made from `name` at `ty` this is.
    pub(crate) instance: Instance,
}

/// A definition as written, or one made from it for the callbacks it is
/// handed; see [`crate::callbacks`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Instance {
    Written,
    /// The definition for one set of callbacks, numbered.
    Called(u32),
    /// A lambda written in the definition, for one set of the callbacks it
    /// reads, numbered.
    Lambda(u32),
}

#[derive(Clone, Debug)]
pub(crate) struct Program {
    /// Where the program starts, when it is an application.
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, h::DataDecl>,
}

#[derive(Clone, Debug)]
pub(crate) struct Constructor {
    pub(crate) owner: Symbol,
    pub(crate) fields: Vec<h::Type>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) clauses: Vec<Clause>,
    pub(crate) provider: Option<Symbol>,
}

#[derive(Clone, Debug)]
pub(crate) struct Clause {
    pub(crate) patterns: Vec<Pattern>,
    pub(crate) guard: Option<Expr>,
    pub(crate) body: Body,
}

#[derive(Clone, Debug)]
pub(crate) enum Pattern {
    Wild,
    Bind(h::LocalId),
    Constructor(Symbol, Vec<Self>),
    Number {
        magnitude: BigUint,
        negative: bool,
    },
    /// A range, which only a clause's guard can test for; see
    /// [`Specializer::tested`].
    Range,
    List(Vec<Self>, Option<Box<Self>>),
    Record(Vec<(Symbol, Self)>),
    Product(Vec<Self>),
    /// A string, which only a clause's guard can test for; see
    /// [`Specializer::tested`].
    String,
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) bindings: Vec<Binding>,
    pub(crate) result: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub(crate) pattern: Pattern,
    pub(crate) value: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Expr {
    pub(crate) module: ModuleId,
    pub(crate) span: crate::ast::Span,
    pub(crate) ty: Type,
    pub(crate) kind: ExprKind,
}

#[derive(Clone, Debug)]
pub(crate) enum ExprKind {
    Local(h::LocalId),
    Function(FunctionKey),
    ConstructorFunction(Symbol),
    Construct(Symbol, Vec<Expr>),
    Natural(BigUint),
    /// A `List(U8)` known whole.
    Bytes(Vec<u8>),
    Record(Vec<(Symbol, Expr)>),
    /// A record with the fields named replaced.
    Update(Box<Expr>, Vec<(Symbol, Expr)>),
    Tuple(Vec<Expr>),
    Project(Box<Expr>, Symbol),
    DirectCall(FunctionKey, Vec<Expr>),
    Invoke(Box<Expr>, Vec<Expr>),
    /// The source occurrence is stable across specialization and identifies
    /// this lambda independently of any other lambda at its diagnostic span.
    Lambda(h::SiteId, Vec<Pattern>, Box<Expr>),
    /// The value as this expression's wider type: the same value, its tag
    /// rows holding the tags a caller added.
    Widen(Box<Expr>),
    /// `value?`: an `Ok`'s value, or its `Err` answered at once by the
    /// function or lambda this is in.
    Try(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecializeError {
    pub message: String,
    /// Where in the source it is about, when that is known.
    pub at: Option<(ModuleId, crate::ast::Span)>,
}

impl fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for SpecializeError {}

/// Specialize what one parameterless `entry` reaches, and nothing else.
#[cfg(test)]
pub(crate) fn monomorphize_from_entry(
    checked: &CheckedProgram,
    entry: Symbol,
) -> Result<Program, SpecializeError> {
    let specializer = Specializer::new(checked)?;
    let entry = specializer.entry_key(entry, None)?;
    specializer.run(Some(entry), Vec::new())
}

/// Specialize a package: what its `main!` reaches, when it has one, then
/// every definition of the package that can stand on its own, so that all
/// the code it writes is checked whether or not anything calls it.
///
/// A definition stands on its own when its parameters hold no function,
/// which only a caller could supply. A generic one is also specialized at
/// the empty type `[]` for each of its variables: without constraints, what
/// it does cannot depend on the type, so that one instance is checked for
/// all of them. Constraints would end that, as a bound's implementation can
/// decide whether a definition stops.
pub(crate) fn monomorphize_package(
    checked: &CheckedProgram,
    host: &crate::host::HostIds,
    main: Option<&crate::host::Main>,
) -> Result<Program, SpecializeError> {
    let specializer = Specializer::new(checked)?;
    let entry = main
        .map(|main| specializer.entry_key(main.symbol, Some(host.host)))
        .transpose()?;
    specializer.run(entry, package_roots(checked)?)
}

/// The package's definitions that stand on their own, in the order written,
/// each generic one at the empty type.
fn package_roots(checked: &CheckedProgram) -> Result<Vec<FunctionKey>, SpecializeError> {
    let resolved = &checked.resolved;
    let mut roots = Vec::new();
    let mut seen = HashSet::new();
    let written = resolved
        .program
        .modules
        .iter()
        .filter(|module| resolved.package.contains(&module.source))
        .flat_map(|module| &module.items)
        .flat_map(|item| match item {
            h::Item::Clause(clause) => vec![clause],
            h::Item::Data(data) => data
                .methods
                .iter()
                .filter_map(|method| match method {
                    h::MethodItem::Clause(clause) => Some(clause),
                    h::MethodItem::Signature(_) => None,
                })
                .collect(),
            h::Item::Signature(_) => Vec::new(),
        });
    for clause in written {
        if !seen.insert(clause.name) {
            continue;
        }
        let Some(scheme) = checked.types.values.get(&clause.name) else {
            continue;
        };
        // A bounded definition is judged where something meets its bounds.
        if !scheme.bounds.is_empty() && !scheme.variables.is_empty() {
            continue;
        }
        // A generic definition can do nothing with a value of a type variable
        // but hand it on, having no constraint that would say more, so how it
        // behaves is the same at every type: judge it once, at the empty type.
        // A row's rest is left out: it closes to its own empty row.
        let mut ordinary = Vec::new();
        ordinary_variables(&scheme.ty, &mut ordinary);
        let placeholder = scheme
            .variables
            .iter()
            .filter(|variable| ordinary.contains(variable))
            .map(|variable| (*variable, Type::empty()))
            .collect();
        let ty = substitute_type(&scheme.ty, &placeholder)?;
        let Some((parameters, _)) = ty.function() else {
            continue;
        };
        if parameters.iter().any(holds_function) {
            continue;
        }
        roots.push(FunctionKey {
            name: clause.name,
            ty,
            instance: Instance::Written,
        });
    }
    Ok(roots)
}

/// Whether a value of `ty` may hold a function, as far as its type says.
fn holds_function(ty: &Type) -> bool {
    match ty {
        Type::Function(_, _) => true,
        Type::Named(_, arguments) => arguments.iter().any(holds_function),
        Type::Record(fields) => fields.iter().any(|(_, field)| holds_function(field)),
        Type::Tuple(members) => members.iter().any(holds_function),
        Type::Variants(tags) => tags
            .iter()
            .flat_map(|(_, fields)| fields)
            .any(holds_function),
    }
}

struct Specializer<'a> {
    checked: &'a Types,
    /// The spellings a refusal names.
    symbols: &'a crate::Symbols,
    prelude: &'a PreludeIds,
    expression_types: HashMap<h::SiteId, &'a InferredType>,
    clause_types: HashMap<h::SiteId, &'a ClauseSite>,
    /// Calls through `where` bounds: the owner whose member each is.
    bound_sites: HashMap<h::SiteId, (&'a InferredType, Symbol)>,
    /// Numerals of a generic type, elaborated at each specialization.
    deferred_numerals: HashMap<h::SiteId, &'a DeferredNumeral>,
    /// Each declared type's methods, by owner and spelling: what a bound's
    /// member is at a concrete type.
    members: HashMap<(Symbol, Symbol), Symbol>,
    literal_sites: HashMap<h::SiteId, &'a LiteralExpr>,
    method_sites: HashMap<h::SiteId, Symbol>,
    projection_sites: HashMap<h::SiteId, Symbol>,
    widening_sites: HashMap<h::SiteId, &'a InferredType>,
    definitions: HashMap<Symbol, Vec<(ModuleId, &'a h::Clause)>>,
    signatures: HashMap<Symbol, Symbol>,
    data: HashMap<Symbol, h::DataDecl>,
    constructors: HashMap<Symbol, Constructor>,
    requested: HashMap<FunctionKey, usize>,
    /// The `equals` and `cmp` of closed records and tuples, which nothing
    /// declares, each with the first place that asked for it.
    structural: HashMap<FunctionKey, (ModuleId, crate::ast::Span)>,
    queue: VecDeque<FunctionKey>,
    functions: Vec<Option<Function>>,
}

impl<'a> Specializer<'a> {
    fn new(checked: &'a CheckedProgram) -> Result<Self, SpecializeError> {
        let (resolved, prelude) = (&checked.resolved, &checked.prelude);
        let checked = &checked.types;
        let mut definitions: HashMap<_, Vec<_>> = HashMap::new();
        let mut signatures = HashMap::new();
        let mut data = HashMap::new();
        let mut constructors = HashMap::new();
        for module in &resolved.program.modules {
            for item in &module.items {
                match item {
                    h::Item::Data(declaration) => {
                        data.insert(declaration.name, declaration.clone());
                        for constructor in &declaration.constructors {
                            constructors.insert(
                                constructor.name,
                                Constructor {
                                    owner: declaration.name,
                                    fields: constructor.fields.clone(),
                                },
                            );
                        }
                        if let Some(wrapper) = &declaration.wrapper {
                            constructors.insert(
                                wrapper.constructor,
                                Constructor {
                                    owner: declaration.name,
                                    fields: vec![wrapper.field.clone()],
                                },
                            );
                        }
                        for method in &declaration.methods {
                            match method {
                                h::MethodItem::Signature(signature) => {
                                    signatures.insert(signature.name, signature.spelling);
                                }
                                h::MethodItem::Clause(clause) => definitions
                                    .entry(clause.name)
                                    .or_default()
                                    .push((module.source, clause)),
                            }
                        }
                    }
                    h::Item::Clause(clause) => definitions
                        .entry(clause.name)
                        .or_default()
                        .push((module.source, clause)),
                    h::Item::Signature(signature) => {
                        signatures.insert(signature.name, signature.spelling);
                    }
                }
            }
        }
        if checked.expressions.is_empty() && !definitions.is_empty() {
            return Err(error("checked HIR has no expression type annotations"));
        }
        let expression_types = checked
            .expressions
            .iter()
            .map(|site| (site.site, &site.ty))
            .collect();
        let clause_types = checked
            .clauses
            .iter()
            .map(|site| (site.site, site))
            .collect();
        let bound_sites = checked
            .bound_sites
            .iter()
            .map(|site| (site.site, (&site.owner, site.member)))
            .collect();
        let deferred_numerals = checked
            .deferred_numerals
            .iter()
            .map(|numeral| (numeral.site, numeral))
            .collect();
        let members = data
            .values()
            .flat_map(|declaration: &h::DataDecl| {
                declaration
                    .methods
                    .iter()
                    .filter_map(move |method| match method {
                        h::MethodItem::Signature(signature) => {
                            Some(((declaration.name, signature.spelling), signature.name))
                        }
                        h::MethodItem::Clause(_) => None,
                    })
            })
            .collect();
        let literal_sites = checked
            .literals
            .iter()
            .map(|site| (site.site, &site.value))
            .collect();
        let method_sites = checked
            .methods
            .iter()
            .map(|site| (site.site, site.target))
            .collect();
        let projection_sites = checked
            .projections
            .iter()
            .map(|site| (site.site, site.field))
            .collect();
        let widening_sites = checked
            .widenings
            .iter()
            .map(|site| (site.site, &site.ty))
            .collect();
        Ok(Self {
            checked,
            symbols: &resolved.symbols,
            prelude,
            expression_types,
            clause_types,
            bound_sites,
            deferred_numerals,
            members,
            literal_sites,
            method_sites,
            projection_sites,
            widening_sites,
            definitions,
            signatures,
            data,
            constructors,
            requested: HashMap::new(),
            structural: HashMap::new(),
            queue: VecDeque::new(),
            functions: Vec::new(),
        })
    }

    /// The key `entry` is specialized at, checking it takes what an entry
    /// may: nothing, or for an application exactly one `Host`.
    fn entry_key(
        &self,
        entry: Symbol,
        application_host: Option<Symbol>,
    ) -> Result<FunctionKey, SpecializeError> {
        let scheme = self
            .checked
            .values
            .get(&entry)
            .ok_or_else(|| error("entry has no inferred type"))?;
        let entry_ty = concrete_scheme(scheme)?;
        let (parameters, _) = entry_ty
            .function()
            .ok_or_else(|| error("entry is not a function"))?;
        let valid_parameters = match (application_host, parameters) {
            (None, []) => true,
            (Some(host), [Type::Named(found, arguments)]) => *found == host && arguments.is_empty(),
            _ => false,
        };
        if !valid_parameters {
            return Err(error(match application_host {
                Some(_) => "application entry must take exactly one Host",
                None => "Barb entry functions cannot take parameters",
            }));
        }
        Ok(FunctionKey {
            name: entry,
            ty: entry_ty,
            instance: Instance::Written,
        })
    }

    /// Specialize everything `entry` reaches, then everything each root
    /// reaches that it did not, so what the entry reaches keeps its order.
    fn run(
        mut self,
        entry: Option<FunctionKey>,
        roots: Vec<FunctionKey>,
    ) -> Result<Program, SpecializeError> {
        for key in entry.iter().cloned().chain(roots) {
            self.request(key);
            while let Some(key) = self.queue.pop_front() {
                let index = self.requested[&key];
                let function = self.specialize_function(&key)?;
                self.functions[index] = Some(function);
            }
        }
        let program = Program {
            entry,
            functions: self
                .functions
                .into_iter()
                .map(|function| function.expect("every requested function was specialized"))
                .collect(),
            data: self.data,
        };
        Ok(program)
    }

    fn request(&mut self, key: FunctionKey) {
        if self.requested.contains_key(&key) {
            return;
        }
        let index = self.functions.len();
        self.requested.insert(key.clone(), index);
        self.functions.push(None);
        self.queue.push_back(key);
    }

    /// Ask for `key`, which the expression at `at` calls.
    fn request_at(&mut self, key: FunctionKey, at: (ModuleId, crate::ast::Span)) {
        if self.is_structural(key.name, key.ty.function().map(|(p, _)| p)) {
            self.structural.entry(key.clone()).or_insert(at);
        }
        self.request(key);
    }

    /// Whether `name` on these parameters is a closed record's or a
    /// tuple's own `equals`, `cmp`, `to_str` or `hash_into`, or a tag row's
    /// own `equals` or `to_str`.
    fn is_structural(&self, name: Symbol, parameters: Option<&[Type]>) -> bool {
        let receiver = parameters.and_then(<[Type]>::first);
        let name = Some(name);
        (name == self.prelude.equals
            && matches!(
                receiver,
                Some(Type::Record(_) | Type::Tuple(_) | Type::Variants(_))
            ))
            || ((name == self.prelude.cmp || name == self.prelude.hash_into)
                && matches!(receiver, Some(Type::Record(_) | Type::Tuple(_))))
            || (name == self.prelude.to_str
                && matches!(
                    receiver,
                    Some(Type::Record(_) | Type::Tuple(_) | Type::Variants(_))
                ))
    }

    fn specialize_function(&mut self, key: &FunctionKey) -> Result<Function, SpecializeError> {
        if let Some(&at) = self.structural.get(key) {
            return self.structural_function(key, at);
        }
        let clauses = self.definitions.get(&key.name).cloned().unwrap_or_default();
        let provider =
            if clauses.is_empty() {
                Some(*self.signatures.get(&key.name).ok_or_else(|| {
                    error("reachable function has neither a body nor a signature")
                })?)
            } else {
                None
            };
        let mut specialized = Vec::with_capacity(clauses.len());
        for (module, clause) in clauses {
            let site = *self
                .clause_types
                .get(&clause.site)
                .ok_or_else(|| error("checked clause type is missing"))?;
            let mut substitution = HashMap::new();
            match_type(&site.ty, &key.ty, &mut substitution)?;
            self.discharge(&site.bounds, &mut substitution)
                .map_err(|message| located(module, clause.span, &message))?;
            let (parameters, _) = key
                .ty
                .function()
                .ok_or_else(|| error("a specialized definition is not a function"))?;
            let parameters = parameters.to_vec();
            specialized.extend(self.clause(module, clause, &substitution, &parameters)?);
        }
        Ok(Function {
            key: key.clone(),
            clauses: specialized,
            provider,
        })
    }

    /// A record's, a tuple's or a tag row's `equals`, every component equal,
    /// a tuple's `cmp`, the first position not `Eq`, or a record's or a
    /// tuple's `hash_into`, each component fed in order, each component
    /// taken by its own type's member. Values of a row are equal where
    /// they are one tag with equal fields.
    fn structural_function(
        &mut self,
        key: &FunctionKey,
        at: (ModuleId, crate::ast::Span),
    ) -> Result<Function, SpecializeError> {
        let (parameters, answer) = key
            .ty
            .function()
            .ok_or_else(|| error("a structural member is not a function"))?;
        let (receiver, answer) = (parameters[0].clone(), answer.clone());
        if Some(key.name) == self.prelude.to_str {
            return match &receiver {
                Type::Variants(tags) => self.row_to_str(key, at, tags),
                Type::Tuple(members) => {
                    let parts: Vec<_> = members.iter().map(|ty| (None, ty.clone())).collect();
                    self.product_to_str(key, at, &parts, ("(", ")"), Pattern::Product)
                }
                Type::Record(fields) => {
                    // In the order of their names, as Ori renders a record,
                    // whatever order the record was written or held in.
                    let mut order: Vec<_> = (0..fields.len()).collect();
                    order.sort_by(|&a, &b| {
                        self.symbols
                            .text(fields[a].0)
                            .cmp(self.symbols.text(fields[b].0))
                    });
                    let parts: Vec<_> = order
                        .iter()
                        .map(|&at| (Some(fields[at].0), fields[at].1.clone()))
                        .collect();
                    let shape = |binds: Vec<Pattern>| {
                        Pattern::Record(order.iter().map(|&at| fields[at].0).zip(binds).collect())
                    };
                    self.product_to_str(key, at, &parts, ("{", "}"), shape)
                }
                _ => unreachable!("only records, tuples and rows have a structural `to_str`"),
            };
        }
        let hashing = Some(key.name) == self.prelude.hash_into;
        let clauses = match &receiver {
            Type::Tuple(members) if hashing => {
                vec![self.fed(key, at, &answer, members, Pattern::Product)?]
            }
            Type::Tuple(members) => {
                vec![self.componentwise(key, at, &answer, members, Pattern::Product)?]
            }
            Type::Record(fields) if hashing => {
                let components: Vec<Type> = fields.iter().map(|(_, ty)| ty.clone()).collect();
                let shape = |binds: Vec<Pattern>| {
                    Pattern::Record(fields.iter().map(|(name, _)| *name).zip(binds).collect())
                };
                vec![self.fed(key, at, &answer, &components, shape)?]
            }
            Type::Record(fields) => {
                let components: Vec<Type> = fields.iter().map(|(_, ty)| ty.clone()).collect();
                let shape = |binds: Vec<Pattern>| {
                    Pattern::Record(fields.iter().map(|(name, _)| *name).zip(binds).collect())
                };
                vec![self.componentwise(key, at, &answer, &components, shape)?]
            }
            Type::Variants(tags) => {
                let mut clauses = Vec::with_capacity(tags.len() + 1);
                for (label, fields) in tags {
                    let shape = |binds| Pattern::Constructor(*label, binds);
                    clauses.push(self.componentwise(key, at, &answer, fields, shape)?);
                }
                // Two different tags, where there are two to differ.
                if tags.len() != 1 {
                    clauses.push(Clause {
                        patterns: vec![Pattern::Wild, Pattern::Wild],
                        guard: None,
                        body: Body {
                            bindings: Vec::new(),
                            result: Expr {
                                module: at.0,
                                span: at.1,
                                ty: answer.clone(),
                                kind: ExprKind::Construct(self.prelude.bool_false, Vec::new()),
                            },
                        },
                    });
                }
                clauses
            }
            _ => unreachable!("only records, tuples and rows have structural members"),
        };
        Ok(Function {
            key: key.clone(),
            clauses,
            provider: None,
        })
    }

    /// A tag row's `to_str`, as Ori writes a tag: its name, and the `to_str`
    /// of each of its fields after it in parentheses, `Invalid(3)`.
    fn row_to_str(
        &mut self,
        key: &FunctionKey,
        (module, span): (ModuleId, crate::ast::Span),
        tags: &[(Symbol, Vec<Type>)],
    ) -> Result<Function, SpecializeError> {
        let str_ = Type::Named(self.prelude.str_, Vec::new());
        let concat = self.method_key(
            self.prelude.str_concat,
            &str_,
            std::slice::from_ref(&str_),
            &str_,
        )?;
        let mut clauses = Vec::with_capacity(tags.len());
        for (label, fields) in tags {
            let count =
                u32::try_from(fields.len()).map_err(|_| error("a tag has too many fields"))?;
            let name = self.symbols.text(*label).to_owned();
            // The name, then each field and what follows it.
            let opening = if fields.is_empty() {
                name
            } else {
                format!("{name}(")
            };
            let mut pieces = vec![self.text(module, span, &opening)?];
            for (index, field) in (0..count).zip(fields) {
                let target = self.implementation(field, key.name)?;
                let call = self.method_key(target, field, &[], &str_)?;
                self.request_at(call.clone(), (module, span));
                pieces.push(Expr {
                    module,
                    span,
                    ty: str_.clone(),
                    kind: ExprKind::DirectCall(
                        call,
                        vec![Expr {
                            module,
                            span,
                            ty: field.clone(),
                            kind: ExprKind::Local(h::LocalId(index)),
                        }],
                    ),
                });
                let after = if index + 1 == count { ")" } else { ", " };
                pieces.push(self.text(module, span, after)?);
            }
            let mut pieces = pieces.into_iter();
            let mut result = pieces.next().ok_or_else(|| error("a tag has a name"))?;
            for next in pieces {
                self.request(concat.clone());
                result = Expr {
                    module,
                    span,
                    ty: str_.clone(),
                    kind: ExprKind::DirectCall(concat.clone(), vec![result, next]),
                };
            }
            clauses.push(Clause {
                patterns: vec![Pattern::Constructor(
                    *label,
                    (0..count)
                        .map(|index| Pattern::Bind(h::LocalId(index)))
                        .collect(),
                )],
                guard: None,
                body: Body {
                    bindings: Vec::new(),
                    result,
                },
            });
        }
        Ok(Function {
            key: key.clone(),
            clauses,
            provider: None,
        })
    }

    /// A record's or a tuple's `to_str`: `open`, each part's own `to_str`
    /// after its name where it has one, separated by `, `, then `close`, so
    /// `{x: 1, y: 2}` and `(1, "a")`.
    fn product_to_str(
        &mut self,
        key: &FunctionKey,
        (module, span): (ModuleId, crate::ast::Span),
        parts: &[(Option<Symbol>, Type)],
        (open, close): (&str, &str),
        shape: impl Fn(Vec<Pattern>) -> Pattern,
    ) -> Result<Function, SpecializeError> {
        let str_ = Type::Named(self.prelude.str_, Vec::new());
        let concat = self.method_key(
            self.prelude.str_concat,
            &str_,
            std::slice::from_ref(&str_),
            &str_,
        )?;
        let count =
            u32::try_from(parts.len()).map_err(|_| error("a product has too many parts"))?;
        let mut pieces = Vec::new();
        let mut before = open.to_owned();
        for (index, (name, ty)) in (0..count).zip(parts) {
            if let Some(name) = name {
                before.push_str(self.symbols.text(*name));
                before.push_str(": ");
            }
            pieces.push(self.text(module, span, &before)?);
            let target = self.implementation(ty, key.name)?;
            let call = self.method_key(target, ty, &[], &str_)?;
            self.request_at(call.clone(), (module, span));
            pieces.push(Expr {
                module,
                span,
                ty: str_.clone(),
                kind: ExprKind::DirectCall(
                    call,
                    vec![Expr {
                        module,
                        span,
                        ty: ty.clone(),
                        kind: ExprKind::Local(h::LocalId(index)),
                    }],
                ),
            });
            ", ".clone_into(&mut before);
        }
        let closing = if parts.is_empty() {
            format!("{open}{close}")
        } else {
            close.to_owned()
        };
        pieces.push(self.text(module, span, &closing)?);
        let mut pieces = pieces.into_iter();
        let mut result = pieces
            .next()
            .ok_or_else(|| error("a product renders something"))?;
        for next in pieces {
            self.request(concat.clone());
            result = Expr {
                module,
                span,
                ty: str_.clone(),
                kind: ExprKind::DirectCall(concat.clone(), vec![result, next]),
            };
        }
        Ok(Function {
            key: key.clone(),
            clauses: vec![Clause {
                patterns: vec![shape(
                    (0..count)
                        .map(|index| Pattern::Bind(h::LocalId(index)))
                        .collect(),
                )],
                guard: None,
                body: Body {
                    bindings: Vec::new(),
                    result,
                },
            }],
            provider: None,
        })
    }

    /// A string literal of `text`.
    fn text(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        text: &str,
    ) -> Result<Expr, SpecializeError> {
        let literal = crate::blessed::string(text.as_bytes(), self.prelude);
        let str_ = Type::Named(self.prelude.str_, Vec::new());
        self.literal(module, span, &literal, &str_)
    }

    /// The clause taking two values of one shape apart, `shape` holding the
    /// binds of their `components`, that answers each pair of components
    /// compared by the component type's own member, the answers joined.
    fn componentwise(
        &mut self,
        key: &FunctionKey,
        (module, span): (ModuleId, crate::ast::Span),
        answer: &Type,
        components: &[Type],
        shape: impl Fn(Vec<Pattern>) -> Pattern,
    ) -> Result<Clause, SpecializeError> {
        let count = u32::try_from(components.len())
            .map_err(|_| error("a product has too many components"))?;
        let side = |offset: u32| {
            shape(
                (0..count)
                    .map(|index| Pattern::Bind(h::LocalId(offset + index)))
                    .collect(),
            )
        };
        let patterns = vec![side(0), side(count)];
        let local = |index: u32, ty: &Type| Expr {
            module,
            span,
            ty: ty.clone(),
            kind: ExprKind::Local(h::LocalId(index)),
        };
        let mut compared = Vec::with_capacity(components.len());
        for (index, component) in (0..count).zip(components) {
            let target = self.implementation(component, key.name)?;
            let call =
                self.method_key(target, component, std::slice::from_ref(component), answer)?;
            self.request_at(call.clone(), (module, span));
            compared.push(Expr {
                module,
                span,
                ty: answer.clone(),
                kind: ExprKind::DirectCall(
                    call,
                    vec![local(index, component), local(count + index, component)],
                ),
            });
        }
        let (join, unit) = if Some(key.name) == self.prelude.cmp {
            (self.prelude.order_then, self.prelude.order_eq)
        } else {
            (self.prelude.bool_and, self.prelude.bool_true)
        };
        let join = self.method_key(join, answer, std::slice::from_ref(answer), answer)?;
        let mut result = Expr {
            module,
            span,
            ty: answer.clone(),
            kind: ExprKind::Construct(unit, Vec::new()),
        };
        if let Some(last) = compared.pop() {
            result = last;
            self.request(join.clone());
        }
        // From the last position back, so the first decides first.
        while let Some(earlier) = compared.pop() {
            result = Expr {
                module,
                span,
                ty: answer.clone(),
                kind: ExprKind::DirectCall(join.clone(), vec![earlier, result]),
            };
        }
        Ok(Clause {
            patterns,
            guard: None,
            body: Body {
                bindings: Vec::new(),
                result,
            },
        })
    }

    /// The clause taking a value of one shape apart, `shape` holding the
    /// binds of its `components`, and a hasher beside it, that feeds each
    /// component to the hasher by the component type's own `hash_into`,
    /// first to last, and answers the hasher fed.
    fn fed(
        &mut self,
        key: &FunctionKey,
        (module, span): (ModuleId, crate::ast::Span),
        hasher: &Type,
        components: &[Type],
        shape: impl Fn(Vec<Pattern>) -> Pattern,
    ) -> Result<Clause, SpecializeError> {
        let count = u32::try_from(components.len())
            .map_err(|_| error("a product has too many components"))?;
        let patterns = vec![
            shape(
                (0..count)
                    .map(|index| Pattern::Bind(h::LocalId(index)))
                    .collect(),
            ),
            Pattern::Bind(h::LocalId(count)),
        ];
        let local = |index: u32, ty: &Type| Expr {
            module,
            span,
            ty: ty.clone(),
            kind: ExprKind::Local(h::LocalId(index)),
        };
        let mut result = local(count, hasher);
        for (index, component) in (0..count).zip(components) {
            let target = self.implementation(component, key.name)?;
            let call = self.method_key(target, component, std::slice::from_ref(hasher), hasher)?;
            self.request_at(call.clone(), (module, span));
            result = Expr {
                module,
                span,
                ty: hasher.clone(),
                kind: ExprKind::DirectCall(call, vec![local(index, component), result]),
            };
        }
        Ok(Clause {
            patterns,
            guard: None,
            body: Body {
                bindings: Vec::new(),
                result,
            },
        })
    }

    /// A written clause at this specialization: one clause for each row its
    /// `|` patterns stand for, each with the one guard and body.
    fn clause(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        substitution: &HashMap<TypeVariable, Type>,
        parameters: &[Type],
    ) -> Result<Vec<Clause>, SpecializeError> {
        let guard = clause
            .guard
            .as_ref()
            .map(|expression| self.expr(module, expression, substitution))
            .transpose()?;
        let body = Body {
            bindings: clause
                .body
                .bindings
                .iter()
                .map(|binding| {
                    Ok(Binding {
                        pattern: convert_pattern(&binding.pattern, &self.checked.readings),
                        value: self.expr(module, &binding.value, substitution)?,
                    })
                })
                .collect::<Result<_, SpecializeError>>()?,
            result: self.expr(module, &clause.body.result, substitution)?,
        };
        let mut rows = h::Pattern::rows(&clause.patterns);
        let last = rows.pop().expect("a clause is at least one row");
        let mut clauses = Vec::with_capacity(rows.len() + 1);
        for row in rows {
            clauses.push(self.row(
                module,
                clause,
                &row,
                parameters,
                (guard.clone(), body.clone()),
            )?);
        }
        clauses.push(self.row(module, clause, &last, parameters, (guard, body))?);
        Ok(clauses)
    }

    /// One row of a clause's patterns, its literals tested before `guard`.
    fn row(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        row: &[h::Pattern],
        parameters: &[Type],
        (guard, body): (Option<Expr>, Body),
    ) -> Result<Clause, SpecializeError> {
        let mut next = clause.locals;
        let mut tests = Vec::new();
        let patterns = row
            .iter()
            .zip(parameters)
            .map(|(pattern, ty)| {
                self.tested((module, clause.span), pattern, ty, (&mut next, &mut tests))
            })
            .collect::<Result<_, _>>()?;
        let guard = self.joined(module, clause.span, tests, guard)?;
        Ok(Clause {
            patterns,
            guard,
            body,
        })
    }

    /// An expression at this specialization, widened where checking said a
    /// signature answers it as a wider type and the two differ here.
    /// A clause pattern at its type, each literal a test rather than a
    /// shape taken out as a fresh name and tested with its type's `equals`:
    /// a numeral of a word, and a string. The tests are what the clause's
    /// guard asks first.
    fn tested(
        &mut self,
        (module, span): (ModuleId, crate::ast::Span),
        pattern: &h::Pattern,
        ty: &Type,
        (next, tests): (&mut u32, &mut Vec<Expr>),
    ) -> Result<Pattern, SpecializeError> {
        // A range binds nothing it shows: a fresh name, and each end it has
        // asked of that name, through the type's `cmp`.
        if let h::Pattern::Range(start, end) = pattern {
            let local = h::LocalId(*next);
            *next = next.checked_add(1).expect("fewer than 2^32 locals");
            let held = Expr {
                module,
                span,
                ty: ty.clone(),
                kind: ExprKind::Local(local),
            };
            if let Some(start) = start {
                let low = self.natural_numeral(
                    module,
                    span,
                    start.magnitude.clone(),
                    start.negative,
                    ty,
                )?;
                tests.push(self.at_most((module, span), low, held.clone(), ty)?);
            }
            if let Some(end) = end {
                let high =
                    self.natural_numeral(module, span, end.magnitude.clone(), end.negative, ty)?;
                tests.push(self.at_most((module, span), held, high, ty)?);
            }
            return Ok(Pattern::Bind(local));
        }
        let readings = &self.checked.readings;
        let literal = match pattern {
            h::Pattern::String(bytes) => Some((
                crate::blessed::string(bytes, self.prelude),
                self.prelude.str_equals,
            )),
            h::Pattern::Number {
                magnitude,
                negative,
            } => match ty {
                Type::Named(name, _) => self
                    .prelude
                    .words
                    .iter()
                    .find(|word| word.ty == *name)
                    .map(|word| {
                        crate::blessed::numeral(
                            magnitude.clone(),
                            *negative,
                            NumeralType::Word(word),
                            self.prelude,
                        )
                        .map(|literal| (literal, word.equals))
                        .map_err(|failure| located(module, span, &failure.to_string()))
                    })
                    .transpose()?,
                _ => None,
            },
            _ => None,
        };
        if let Some((literal, equals)) = literal {
            let local = h::LocalId(*next);
            *next = next.checked_add(1).expect("fewer than 2^32 locals");
            let value = self.literal(module, span, &literal, ty)?;
            let held = Expr {
                module,
                span,
                ty: ty.clone(),
                kind: ExprKind::Local(local),
            };
            let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
            let key = self.method_key(equals, ty, std::slice::from_ref(ty), &bool_ty)?;
            self.request(key.clone());
            tests.push(Expr {
                module,
                span,
                ty: bool_ty,
                kind: ExprKind::DirectCall(key, vec![held, value]),
            });
            return Ok(Pattern::Bind(local));
        }
        let fields: Option<(Symbol, Vec<(&h::Pattern, Type)>)> = match (pattern, ty) {
            (h::Pattern::Constructor(constructor, fields), Type::Named(..)) => {
                let types = self.constructor_fields(*constructor, ty)?;
                Some((*constructor, fields.iter().zip(types).collect()))
            }
            (h::Pattern::Dual(dual, fields), Type::Named(..)) => {
                let constructor = read(dual, readings);
                let types = self.constructor_fields(constructor, ty)?;
                Some((constructor, fields.iter().zip(types).collect()))
            }
            (
                h::Pattern::Tag(label, fields)
                | h::Pattern::Constructor(label, fields)
                | h::Pattern::Dual(
                    h::Dual {
                        spelling: label, ..
                    },
                    fields,
                ),
                Type::Variants(tags),
            ) => {
                let types = tags
                    .iter()
                    .find(|(found, _)| found == label)
                    .map(|(_, types)| types.clone())
                    .unwrap_or_default();
                Some((*label, fields.iter().zip(types).collect()))
            }
            _ => None,
        };
        if let Some((constructor, fields)) = fields {
            let fields = fields
                .into_iter()
                .map(|(field, ty)| self.tested((module, span), field, &ty, (next, tests)))
                .collect::<Result<_, _>>()?;
            return Ok(Pattern::Constructor(constructor, fields));
        }
        Ok(match (pattern, ty) {
            (h::Pattern::List(elements, rest), Type::Named(_, arguments))
                if arguments.len() == 1 =>
            {
                let element = arguments[0].clone();
                Pattern::List(
                    elements
                        .iter()
                        .map(|item| self.tested((module, span), item, &element, (next, tests)))
                        .collect::<Result<_, _>>()?,
                    rest.as_deref()
                        .map(|rest| self.tested((module, span), rest, ty, (next, tests)))
                        .transpose()?
                        .map(Box::new),
                )
            }
            (h::Pattern::Record(fields, _), Type::Record(types)) => Pattern::Record(
                fields
                    .iter()
                    .map(|(name, field)| {
                        let field_ty = types
                            .iter()
                            .find(|(found, _)| found == name)
                            .map(|(_, ty)| ty.clone())
                            .ok_or_else(|| {
                                error("a record pattern names a field its type lacks")
                            })?;
                        Ok((
                            *name,
                            self.tested((module, span), field, &field_ty, (next, tests))?,
                        ))
                    })
                    .collect::<Result<_, SpecializeError>>()?,
            ),
            (h::Pattern::Tuple(members), Type::Tuple(types)) => Pattern::Product(
                members
                    .iter()
                    .zip(types)
                    .map(|(member, ty)| self.tested((module, span), member, ty, (next, tests)))
                    .collect::<Result<_, _>>()?,
            ),
            _ => convert_pattern(pattern, readings),
        })
    }

    /// A clause's literal tests and its written guard as one guard, the
    /// tests first.
    fn joined(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        tests: Vec<Expr>,
        guard: Option<Expr>,
    ) -> Result<Option<Expr>, SpecializeError> {
        let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
        let and = self.method_key(
            self.prelude.bool_and,
            &bool_ty,
            std::slice::from_ref(&bool_ty),
            &bool_ty,
        )?;
        let mut conditions = tests.into_iter().chain(guard);
        let Some(first) = conditions.next() else {
            return Ok(None);
        };
        let mut joined = first;
        for condition in conditions {
            self.request(and.clone());
            joined = Expr {
                module,
                span,
                ty: bool_ty.clone(),
                kind: ExprKind::DirectCall(and.clone(), vec![joined, condition]),
            };
        }
        Ok(Some(joined))
    }

    fn expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Expr, SpecializeError> {
        let written = self.written_expr(module, expression, substitution)?;
        let Some(target) = self.widening_sites.get(&expression.site) else {
            return Ok(written);
        };
        let target = self.site_type(target, substitution)?;
        if target == written.ty {
            return Ok(written);
        }
        Ok(Expr {
            module,
            span: expression.span,
            ty: target,
            kind: ExprKind::Widen(Box::new(written)),
        })
    }

    fn written_expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Expr, SpecializeError> {
        let template = self
            .expression_types
            .get(&expression.site)
            .ok_or_else(|| error("checked expression type is missing"))?;
        let ty = self.site_type(template, substitution)?;
        let kind = match &expression.kind {
            h::ExprKind::Local(local) => ExprKind::Local(*local),
            h::ExprKind::Global(name) => {
                let key = FunctionKey {
                    name: *name,
                    ty: ty.clone(),
                    instance: Instance::Written,
                };
                self.request(key.clone());
                ExprKind::Function(key)
            }
            // A tag is built as the constructor of its row it names.
            h::ExprKind::Tag(label) if matches!(ty, Type::Function(_, _)) => {
                ExprKind::ConstructorFunction(*label)
            }
            h::ExprKind::Tag(label) => ExprKind::Construct(*label, Vec::new()),
            h::ExprKind::Associated(..) => {
                return Err(error("a member a bound gives is only ever called"));
            }
            h::ExprKind::Dual(dual) => {
                let read = read(dual, &self.checked.readings);
                if matches!(ty, Type::Function(_, _)) {
                    ExprKind::ConstructorFunction(read)
                } else {
                    ExprKind::Construct(read, Vec::new())
                }
            }
            h::ExprKind::Constructor(constructor) => {
                if matches!(ty, Type::Function(_, _)) {
                    ExprKind::ConstructorFunction(*constructor)
                } else {
                    ExprKind::Construct(*constructor, Vec::new())
                }
            }
            h::ExprKind::String(parts)
                if parts
                    .iter()
                    .any(|part| matches!(part, h::StringPart::Splice(_))) =>
            {
                return self.interpolated(module, expression.span, parts, &ty, substitution);
            }
            h::ExprKind::Number(_) | h::ExprKind::Decimal(..) => {
                return self.numeral(module, expression, &ty);
            }
            h::ExprKind::String(_) => {
                let literal = self.literal_site(expression.site)?;
                return self.literal(module, expression.span, &literal, &ty);
            }
            h::ExprKind::List(elements, rest) => {
                let Type::Named(list, arguments) = &ty else {
                    return Err(error("list syntax did not infer as a named type"));
                };
                if *list != self.prelude.list || arguments.len() != 1 {
                    return Err(error("list syntax did not infer as List"));
                }
                let mut tail = if let Some(rest) = rest {
                    self.expr(module, rest, substitution)?
                } else {
                    Expr {
                        module,
                        span: expression.span,
                        ty: ty.clone(),
                        kind: ExprKind::Construct(self.prelude.list_nil, Vec::new()),
                    }
                };
                for element in elements.iter().rev() {
                    let head = self.expr(module, element, substitution)?;
                    tail = Expr {
                        module,
                        span: expression.span,
                        ty: ty.clone(),
                        kind: ExprKind::Construct(self.prelude.list_cons, vec![head, tail]),
                    };
                }
                return Ok(tail);
            }
            h::ExprKind::Record(fields) => ExprKind::Record(
                fields
                    .iter()
                    .map(|(name, value)| Ok((*name, self.expr(module, value, substitution)?)))
                    .collect::<Result<_, SpecializeError>>()?,
            ),
            h::ExprKind::Update(base, fields) => ExprKind::Update(
                Box::new(self.expr(module, base, substitution)?),
                fields
                    .iter()
                    .map(|(name, value)| Ok((*name, self.expr(module, value, substitution)?)))
                    .collect::<Result<_, SpecializeError>>()?,
            ),
            h::ExprKind::Tuple(members) => ExprKind::Tuple(
                members
                    .iter()
                    .map(|member| self.expr(module, member, substitution))
                    .collect::<Result<_, _>>()?,
            ),
            h::ExprKind::Lambda(patterns, body) => ExprKind::Lambda(
                expression.site,
                patterns
                    .iter()
                    .map(|pattern| convert_pattern(pattern, &self.checked.readings))
                    .collect(),
                Box::new(self.expr(module, body, substitution)?),
            ),
            h::ExprKind::Call(head, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.expr(module, argument, substitution))
                    .collect::<Result<Vec<_>, _>>()?;
                match &head.kind {
                    h::ExprKind::Global(name) => {
                        let head_ty = self.expression_type(head.site, substitution)?;
                        let key = FunctionKey {
                            name: *name,
                            ty: head_ty,
                            instance: Instance::Written,
                        };
                        self.request(key.clone());
                        ExprKind::DirectCall(key, arguments)
                    }
                    h::ExprKind::Constructor(constructor) | h::ExprKind::Tag(constructor) => {
                        ExprKind::Construct(*constructor, arguments)
                    }
                    h::ExprKind::Dual(dual) => {
                        ExprKind::Construct(read(dual, &self.checked.readings), arguments)
                    }
                    // `a.zero()`: the member of whatever `a` is here.
                    h::ExprKind::Associated(..) => {
                        let target = self.target(expression.site, substitution)?;
                        let parameters = arguments.iter().map(|argument| argument.ty.clone());
                        let key = FunctionKey {
                            name: target,
                            ty: Type::Function(parameters.collect(), Box::new(ty.clone())),
                            instance: Instance::Written,
                        };
                        self.request(key.clone());
                        ExprKind::DirectCall(key, arguments)
                    }
                    _ => ExprKind::Invoke(
                        Box::new(self.expr(module, head, substitution)?),
                        arguments,
                    ),
                }
            }
            h::ExprKind::Member(receiver, _) => {
                let receiver = self.expr(module, receiver, substitution)?;
                if let Some(field) = self.projection_sites.get(&expression.site) {
                    ExprKind::Project(Box::new(receiver), *field)
                } else {
                    let target = self.target(expression.site, substitution)?;
                    let key = self.method_key(target, &receiver.ty, &[], &ty)?;
                    self.request(key.clone());
                    ExprKind::DirectCall(key, vec![receiver])
                }
            }
            h::ExprKind::Method(receiver, _, arguments) => {
                let target = self.target(expression.site, substitution)?;
                let receiver = self.expr(module, receiver, substitution)?;
                let mut lowered = Vec::with_capacity(arguments.len() + 1);
                lowered.push(receiver);
                for argument in arguments {
                    lowered.push(self.expr(module, argument, substitution)?);
                }
                let argument_types: Vec<_> = lowered[1..]
                    .iter()
                    .map(|argument| argument.ty.clone())
                    .collect();
                let key = self.method_key(target, &lowered[0].ty, &argument_types, &ty)?;
                self.request_at(key.clone(), (module, expression.span));
                ExprKind::DirectCall(key, lowered)
            }
            h::ExprKind::Try(value) => {
                ExprKind::Try(Box::new(self.expr(module, value, substitution)?))
            }
            h::ExprKind::Unary(_, value)
                if matches!(
                    value.kind,
                    h::ExprKind::Number(_) | h::ExprKind::Decimal(..)
                ) =>
            {
                return self.numeral(module, expression, &ty);
            }
            h::ExprKind::Unary(_, value) => {
                let target = self.target(expression.site, substitution)?;
                let value = self.expr(module, value, substitution)?;
                let key = self.method_key(target, &value.ty, &[], &ty)?;
                self.request(key.clone());
                ExprKind::DirectCall(key, vec![value])
            }
            h::ExprKind::Binary(operator, left, right) => {
                let target = self.target(expression.site, substitution)?;
                let left = self.expr(module, left, substitution)?;
                let right = self.expr(module, right, substitution)?;
                let ordering = matches!(
                    operator,
                    crate::ast::BinaryOp::Less
                        | crate::ast::BinaryOp::LessEqual
                        | crate::ast::BinaryOp::Greater
                        | crate::ast::BinaryOp::GreaterEqual
                );
                let answered = if ordering {
                    Type::Named(self.prelude.order, Vec::new())
                } else {
                    ty.clone()
                };
                let key =
                    self.method_key(target, &left.ty, std::slice::from_ref(&right.ty), &answered)?;
                self.request_at(key.clone(), (module, expression.span));
                let call = ExprKind::DirectCall(key, vec![left, right]);
                let view = match operator {
                    crate::ast::BinaryOp::Less => Some(self.prelude.order_lt),
                    crate::ast::BinaryOp::LessEqual => Some(self.prelude.order_le),
                    crate::ast::BinaryOp::Greater => Some(self.prelude.order_gt),
                    crate::ast::BinaryOp::GreaterEqual => Some(self.prelude.order_ge),
                    _ => None,
                };
                if let Some(view) = view {
                    // The operator reads its view of what `cmp` answered.
                    let order = Type::Named(self.prelude.order, Vec::new());
                    let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
                    let view = self.method_key(view, &order, &[], &bool_ty)?;
                    self.request(view.clone());
                    let compared = Expr {
                        module,
                        span: expression.span,
                        ty: order,
                        kind: call,
                    };
                    ExprKind::DirectCall(view, vec![compared])
                } else if matches!(operator, crate::ast::BinaryOp::NotEqual) {
                    let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
                    let not = self.method_key(self.prelude.bool_not, &bool_ty, &[], &bool_ty)?;
                    self.request(not.clone());
                    let argument = Expr {
                        module,
                        span: expression.span,
                        ty: bool_ty,
                        kind: call,
                    };
                    ExprKind::DirectCall(not, vec![argument])
                } else {
                    call
                }
            }
        };
        Ok(Expr {
            module,
            span: expression.span,
            ty,
            kind,
        })
    }

    /// `"a${x}b"` as `"a".concat(x.to_str()).concat("b")`, in the order
    /// written, leaving out empty text.
    fn interpolated(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        parts: &[h::StringPart],
        str_: &Type,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Expr, SpecializeError> {
        let mut pieces = Vec::with_capacity(parts.len());
        for part in parts {
            pieces.push(match part {
                h::StringPart::Text(bytes) if bytes.is_empty() => continue,
                h::StringPart::Text(bytes) => {
                    let literal = crate::blessed::string(bytes, self.prelude);
                    self.literal(module, span, &literal, str_)?
                }
                h::StringPart::Splice(splice) => self.expr(module, splice, substitution)?,
            });
        }
        let concat = self.method_key(
            self.prelude.str_concat,
            str_,
            std::slice::from_ref(str_),
            str_,
        )?;
        self.request(concat.clone());
        let mut pieces = pieces.into_iter();
        let first = pieces.next().expect("a string with a splice has a piece");
        Ok(pieces.fold(first, |joined, piece| Expr {
            module,
            span,
            ty: str_.clone(),
            kind: ExprKind::DirectCall(concat.clone(), vec![joined, piece]),
        }))
    }

    fn expression_type(
        &self,
        site: h::SiteId,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Type, SpecializeError> {
        let ty = self
            .expression_types
            .get(&site)
            .ok_or_else(|| error("checked expression type is missing"))?;
        self.site_type(ty, substitution)
    }

    /// A site's type at this specialization. A type variable nothing pinned
    /// -- the element of `[]` in `[].len()` -- is `Nat`, as in Ori: no value
    /// of it is ever built, so which type it is cannot be seen. A row's
    /// rest nothing pinned holds no tags instead.
    fn site_type(
        &self,
        template: &InferredType,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Type, SpecializeError> {
        let mut free = Vec::new();
        ordinary_variables(template, &mut free);
        free.retain(|variable| !substitution.contains_key(variable));
        if free.is_empty() {
            return substitute_type(template, substitution);
        }
        let mut defaulted = substitution.clone();
        for variable in free {
            defaulted.insert(variable, Type::Named(self.prelude.nat, Vec::new()));
        }
        substitute_type(template, &defaulted)
    }

    /// The method a call names: where it goes through a `where` bound, the
    /// member of the concrete type the bound's owner is here.
    fn target(
        &self,
        site: h::SiteId,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Symbol, SpecializeError> {
        let Some((owner, member)) = self.bound_sites.get(&site).copied() else {
            return self.method_site(site);
        };
        let owner = self.site_type(owner, substitution)?;
        self.implementation(&owner, member)
    }

    /// Which method of `owner` is its `member`.
    fn implementation(&self, owner: &Type, member: Symbol) -> Result<Symbol, SpecializeError> {
        if self.is_structural(member, Some(std::slice::from_ref(owner))) {
            return Ok(member);
        }
        let Type::Named(name, _) = owner else {
            return Err(error(
                "a `where` bound is met only by a declared type's methods",
            ));
        };
        self.members
            .get(&(*name, member))
            .copied()
            .ok_or_else(|| error("a type does not have a member a `where` bound asks of it"))
    }

    /// Fix what a definition's bounds determine: once an owner is known, its
    /// member's implementation says the types of the member's other
    /// positions, which may be all that says what a variable is. The bound's
    /// shape and the implementation's signature are met from both sides, so
    /// a position either one knows fixes the other's. Runs until nothing
    /// more is determined; a bound still open then names a variable nothing
    /// determines, which is refused rather than guessed.
    fn discharge(
        &self,
        bounds: &[InferredBound],
        substitution: &mut HashMap<TypeVariable, Type>,
    ) -> Result<(), String> {
        let mut open: Vec<&InferredBound> = bounds.iter().collect();
        loop {
            let before = substitution.len();
            let mut waiting = Vec::new();
            for bound in open {
                let Ok(owner) = substitute_type(&bound.owner, substitution) else {
                    waiting.push(bound);
                    continue;
                };
                let target = self
                    .implementation(&owner, bound.member)
                    .map_err(|failure| failure.message)?;
                // A record's or a tuple's own member takes two of it: the
                // owner says all there is.
                if self.is_structural(target, Some(std::slice::from_ref(&owner))) {
                    continue;
                }
                let scheme = self
                    .checked
                    .values
                    .get(&target)
                    .ok_or("a bound's implementation has no scheme")?;
                let InferredType::Function(parameters, result) = &scheme.ty else {
                    continue;
                };
                // The implementation at this owner: fixed by its receiver,
                // or for a member of the type, by what it answers.
                let mut fixed = HashMap::new();
                let pinned = if bound.associated {
                    match_type(result, &owner, &mut fixed)
                } else {
                    parameters
                        .first()
                        .map_or(Ok(()), |receiver| match_type(receiver, &owner, &mut fixed))
                };
                if pinned.is_err() {
                    continue;
                }
                while meet(&bound.ty, &scheme.ty, (substitution, &mut fixed)) {}
                if substitute_type(&bound.ty, substitution).is_err() {
                    waiting.push(bound);
                }
            }
            if waiting.is_empty() {
                return Ok(());
            }
            if substitution.len() == before {
                return Err(format!(
                    "nothing determines the types a `where` bound's member `{}` takes here",
                    self.symbols.text(waiting[0].member)
                ));
            }
            open = waiting;
        }
    }

    /// A numeral at its type here: elaborated by checking where that type
    /// was known there, and here where it was generic.
    fn numeral(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        ty: &Type,
    ) -> Result<Expr, SpecializeError> {
        let span = expression.span;
        if let Some(literal) = self.literal_sites.get(&expression.site) {
            let literal = (*literal).clone();
            return self.literal(module, span, &literal, ty);
        }
        let numeral = self
            .deferred_numerals
            .get(&expression.site)
            .copied()
            .ok_or_else(|| error("elaborated literal is missing"))?;
        if let Some(scale) = numeral.scale {
            let float = match ty {
                Type::Named(name, arguments) if arguments.is_empty() => {
                    self.prelude.floats.iter().find(|float| float.ty == *name)
                }
                _ => None,
            }
            .ok_or_else(|| located(module, span, "a decimal numeral is an `F32` or an `F64`"))?;
            let literal =
                crate::blessed::decimal(numeral.magnitude.clone(), scale, numeral.negative, float);
            return self.literal(module, span, &literal, ty);
        }
        self.natural_numeral(
            module,
            span,
            numeral.magnitude.clone(),
            numeral.negative,
            ty,
        )
    }

    /// A numeral with no point, `magnitude` negated or not, at `ty`, which
    /// must be one a numeral can be.
    fn natural_numeral(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        magnitude: BigUint,
        negative: bool,
        ty: &Type,
    ) -> Result<Expr, SpecializeError> {
        let kind = match ty {
            Type::Named(name, arguments) if arguments.is_empty() && *name == self.prelude.nat => {
                Some(NumeralType::Nat)
            }
            Type::Named(name, arguments) if arguments.is_empty() && *name == self.prelude.int => {
                Some(NumeralType::Int)
            }
            Type::Named(name, arguments) if arguments.is_empty() => self
                .prelude
                .words
                .iter()
                .find(|word| word.ty == *name)
                .map(NumeralType::Word),
            _ => None,
        }
        .ok_or_else(|| {
            located(
                module,
                span,
                "a numeral is a `Nat`, `Int`, `U8`, `U16`, `U32`, or `U64`",
            )
        })?;
        let literal = crate::blessed::numeral(magnitude, negative, kind, self.prelude)
            .map_err(|failure| located(module, span, &failure.to_string()))?;
        self.literal(module, span, &literal, ty)
    }

    /// `low <= high` at `ty`: the `le` view of what `ty`'s `cmp` answers.
    fn at_most(
        &mut self,
        (module, span): (ModuleId, crate::ast::Span),
        low: Expr,
        high: Expr,
        ty: &Type,
    ) -> Result<Expr, SpecializeError> {
        let cmp = self
            .prelude
            .cmp
            .ok_or_else(|| error("a range is tested with `cmp`, which nothing declares"))?;
        let order = Type::Named(self.prelude.order, Vec::new());
        let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
        let target = self
            .implementation(ty, cmp)
            .map_err(|_| located(module, span, "a range is tested with its type's `cmp`"))?;
        let compare = self.method_key(target, ty, std::slice::from_ref(ty), &order)?;
        self.request_at(compare.clone(), (module, span));
        let view = self.method_key(self.prelude.order_le, &order, &[], &bool_ty)?;
        self.request(view.clone());
        let compared = Expr {
            module,
            span,
            ty: order,
            kind: ExprKind::DirectCall(compare, vec![low, high]),
        };
        Ok(Expr {
            module,
            span,
            ty: bool_ty,
            kind: ExprKind::DirectCall(view, vec![compared]),
        })
    }

    fn method_site(&self, site: h::SiteId) -> Result<Symbol, SpecializeError> {
        self.method_sites
            .get(&site)
            .copied()
            .ok_or_else(|| error("resolved method target is missing"))
    }

    fn method_key(
        &self,
        name: Symbol,
        receiver: &Type,
        arguments: &[Type],
        result: &Type,
    ) -> Result<FunctionKey, SpecializeError> {
        let mut parameters = Vec::with_capacity(arguments.len() + 1);
        parameters.push(receiver.clone());
        parameters.extend_from_slice(arguments);
        let ty = Type::Function(parameters, Box::new(result.clone()));
        if self.is_structural(name, ty.function().map(|(p, _)| p)) {
            return Ok(FunctionKey {
                name,
                ty,
                instance: Instance::Written,
            });
        }
        let scheme = self
            .checked
            .values
            .get(&name)
            .ok_or_else(|| error("method target has no inferred scheme"))?;
        let mut substitution = HashMap::new();
        match_type(&scheme.ty, &ty, &mut substitution)?;
        Ok(FunctionKey {
            name,
            ty,
            instance: Instance::Written,
        })
    }

    fn literal_site(&self, site: h::SiteId) -> Result<LiteralExpr, SpecializeError> {
        self.literal_sites
            .get(&site)
            .map(|literal| (*literal).clone())
            .ok_or_else(|| error("elaborated literal is missing"))
    }

    fn literal(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        literal: &LiteralExpr,
        expected: &Type,
    ) -> Result<Expr, SpecializeError> {
        let kind = match literal {
            LiteralExpr::Natural(magnitude) => ExprKind::Natural(magnitude.clone()),
            LiteralExpr::Bytes(bytes) => ExprKind::Bytes(bytes.clone()),
            LiteralExpr::Construct(constructor, fields) => {
                let field_types = self.constructor_fields(*constructor, expected)?;
                if fields.len() != field_types.len() {
                    return Err(error(
                        "literal constructor arity does not match its declaration",
                    ));
                }
                ExprKind::Construct(
                    *constructor,
                    fields
                        .iter()
                        .zip(field_types)
                        .map(|(field, ty)| self.literal(module, span, field, &ty))
                        .collect::<Result<_, _>>()?,
                )
            }
            LiteralExpr::Call(function, arguments) => {
                let scheme = self
                    .checked
                    .values
                    .get(function)
                    .ok_or_else(|| error("literal helper has no inferred scheme"))?;
                let Type::Function(parameters, result) = scheme_result(scheme, expected)? else {
                    unreachable!("a literal helper scheme is a function")
                };
                if arguments.len() != parameters.len() {
                    return Err(error("literal helper arity does not match its declaration"));
                }
                let key = FunctionKey {
                    name: *function,
                    ty: Type::Function(parameters.clone(), result),
                    instance: Instance::Written,
                };
                self.request(key.clone());
                ExprKind::DirectCall(
                    key,
                    arguments
                        .iter()
                        .zip(parameters)
                        .map(|(argument, ty)| self.literal(module, span, argument, &ty))
                        .collect::<Result<_, _>>()?,
                )
            }
        };
        Ok(Expr {
            module,
            span,
            ty: expected.clone(),
            kind,
        })
    }

    fn constructor_fields(
        &self,
        constructor: Symbol,
        result: &Type,
    ) -> Result<Vec<Type>, SpecializeError> {
        let declaration = self
            .constructors
            .get(&constructor)
            .ok_or_else(|| error("constructor declaration is missing"))?;
        let Type::Named(owner, arguments) = result else {
            return Err(error("constructor result is not a named type"));
        };
        if *owner != declaration.owner {
            return Err(error("constructor result has the wrong owner"));
        }
        let data = &self.data[owner];
        if data.parameters.len() != arguments.len() {
            return Err(error("type specialization has the wrong arity"));
        }
        let variables: HashMap<_, _> = data
            .parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect();
        declaration
            .fields
            .iter()
            .map(|field| surface_type(field, &variables))
            .collect()
    }
}

/// A checked pattern as specialization reads it, each claimed word as the
/// reading checking gave it.
fn convert_pattern(pattern: &h::Pattern, readings: &HashMap<h::SiteId, Reading>) -> Pattern {
    let convert = |pattern| convert_pattern(pattern, readings);
    match pattern {
        h::Pattern::Dual(dual, fields) => {
            Pattern::Constructor(read(dual, readings), fields.iter().map(convert).collect())
        }
        h::Pattern::Wild => Pattern::Wild,
        h::Pattern::Or(_) => unreachable!("a clause is specialized a row at a time"),
        h::Pattern::String(_) => Pattern::String,
        h::Pattern::Bind(local) => Pattern::Bind(*local),
        h::Pattern::Constructor(constructor, fields) | h::Pattern::Tag(constructor, fields) => {
            Pattern::Constructor(*constructor, fields.iter().map(convert).collect())
        }
        h::Pattern::Number {
            magnitude,
            negative,
        } => Pattern::Number {
            magnitude: magnitude.clone(),
            negative: *negative,
        },
        h::Pattern::Range(..) => Pattern::Range,
        h::Pattern::List(elements, rest) => Pattern::List(
            elements.iter().map(convert).collect(),
            rest.as_deref().map(convert).map(Box::new),
        ),
        // A field an open pattern leaves out is taken whatever it is.
        h::Pattern::Record(fields, _) => Pattern::Record(
            fields
                .iter()
                .map(|(name, pattern)| (*name, convert(pattern)))
                .collect(),
        ),
        h::Pattern::Tuple(members) => Pattern::Product(members.iter().map(convert).collect()),
    }
}

/// What a claimed word was read as: the constructor or the tag checking
/// chose for it. Checking reads every word before it answers.
fn read(dual: &h::Dual, readings: &HashMap<h::SiteId, Reading>) -> Symbol {
    match readings.get(&dual.site) {
        Some(Reading::Constructor(symbol) | Reading::Tag(symbol)) => *symbol,
        None => unreachable!("checking reads every claimed word"),
    }
}

/// The type variables of `ty` that stand for types, not for a row's rest.
fn ordinary_variables(ty: &InferredType, output: &mut Vec<TypeVariable>) {
    match ty {
        InferredType::Variable(variable) => output.push(*variable),
        InferredType::Named(_, arguments) => {
            for argument in arguments {
                ordinary_variables(argument, output);
            }
        }
        InferredType::Function(parameters, result) => {
            for parameter in parameters {
                ordinary_variables(parameter, output);
            }
            ordinary_variables(result, output);
        }
        InferredType::Variants(tags, tail) => {
            for field in tags.iter().flat_map(|(_, fields)| fields) {
                ordinary_variables(field, output);
            }
            if let Some(tail) = tail.as_deref()
                && !matches!(tail, InferredType::Variable(_))
            {
                ordinary_variables(tail, output);
            }
        }
        InferredType::Record(fields, tail) => {
            for (_, field) in fields {
                ordinary_variables(field, output);
            }
            if let Some(tail) = tail.as_deref()
                && !matches!(tail, InferredType::Variable(_))
            {
                ordinary_variables(tail, output);
            }
        }
        InferredType::Tuple(members) => {
            for member in members {
                ordinary_variables(member, output);
            }
        }
    }
}

fn concrete_scheme(scheme: &InferredScheme) -> Result<Type, SpecializeError> {
    if !scheme.variables.is_empty() {
        return Err(error("entry has an ambiguous polymorphic type"));
    }
    substitute_type(&scheme.ty, &HashMap::new())
}

/// Meet a bound's shape with its implementation's signature, each side's
/// variables its own: where one side is known in full, the other is matched
/// against it; where both are built alike, their parts meet. Answers
/// whether either side learnt anything. A part neither knows yet, or rows
/// neither side knows in full, wait for a later round.
fn meet(
    bound: &InferredType,
    implementation: &InferredType,
    (known, fixed): (
        &mut HashMap<TypeVariable, Type>,
        &mut HashMap<TypeVariable, Type>,
    ),
) -> bool {
    /// Match `template` against `concrete` where it fits, learning nothing
    /// where it does not; answers whether it learnt anything.
    fn learn(
        template: &InferredType,
        concrete: &Type,
        substitution: &mut HashMap<TypeVariable, Type>,
    ) -> bool {
        let mut trial = substitution.clone();
        if match_type(template, concrete, &mut trial).is_ok() && trial.len() > substitution.len() {
            *substitution = trial;
            return true;
        }
        false
    }
    if let Ok(concrete) = substitute_type(implementation, fixed) {
        return learn(bound, &concrete, known);
    }
    if let Ok(concrete) = substitute_type(bound, known) {
        return learn(implementation, &concrete, fixed);
    }
    let mut learnt = false;
    let mut each = |bounds: &[InferredType], implementations: &[InferredType]| {
        for (bound, implementation) in bounds.iter().zip(implementations) {
            learnt |= meet(bound, implementation, (&mut *known, &mut *fixed));
        }
    };
    match (bound, implementation) {
        (InferredType::Named(a, bounds), InferredType::Named(b, implementations))
            if a == b && bounds.len() == implementations.len() =>
        {
            each(bounds, implementations);
        }
        (InferredType::Tuple(bounds), InferredType::Tuple(implementations))
            if bounds.len() == implementations.len() =>
        {
            each(bounds, implementations);
        }
        (
            InferredType::Function(bounds, bound_result),
            InferredType::Function(implementations, implementation_result),
        ) if bounds.len() == implementations.len() => {
            each(bounds, implementations);
            learnt |= meet(bound_result, implementation_result, (known, fixed));
        }
        _ => {}
    }
    learnt
}

fn substitute_type(
    ty: &InferredType,
    substitution: &HashMap<TypeVariable, Type>,
) -> Result<Type, SpecializeError> {
    match ty {
        InferredType::Variable(variable) => substitution
            .get(variable)
            .cloned()
            .ok_or_else(|| error("specialization left an unresolved type variable")),
        InferredType::Named(name, arguments) => Ok(Type::Named(
            *name,
            arguments
                .iter()
                .map(|argument| substitute_type(argument, substitution))
                .collect::<Result<_, _>>()?,
        )),
        InferredType::Function(parameters, result) => Ok(Type::Function(
            parameters
                .iter()
                .map(|parameter| substitute_type(parameter, substitution))
                .collect::<Result<_, _>>()?,
            Box::new(substitute_type(result, substitution)?),
        )),
        // A rest nothing pinned holds no tags: no value the program builds
        // carries one it did not write.
        InferredType::Variants(tags, tail) => {
            let mut row = tags
                .iter()
                .map(|(label, fields)| {
                    let fields = fields
                        .iter()
                        .map(|field| substitute_type(field, substitution))
                        .collect::<Result<_, _>>()?;
                    Ok((*label, fields))
                })
                .collect::<Result<Vec<_>, SpecializeError>>()?;
            let rest = match tail.as_deref() {
                None => Type::empty(),
                Some(InferredType::Variable(variable)) => substitution
                    .get(variable)
                    .cloned()
                    .unwrap_or_else(Type::empty),
                Some(other) => substitute_type(other, substitution)?,
            };
            let Type::Variants(more) = rest else {
                return Err(error("the rest of a tag row is not a row"));
            };
            row.extend(more);
            Ok(Type::row(row))
        }
        // A record's rest nothing pinned holds no fields.
        InferredType::Record(fields, tail) => {
            let mut record = fields
                .iter()
                .map(|(name, ty)| Ok((*name, substitute_type(ty, substitution)?)))
                .collect::<Result<Vec<_>, SpecializeError>>()?;
            let rest = match tail.as_deref() {
                None => Type::Record(Vec::new()),
                Some(InferredType::Variable(variable)) => substitution
                    .get(variable)
                    .cloned()
                    .unwrap_or(Type::Record(Vec::new())),
                Some(other) => substitute_type(other, substitution)?,
            };
            let Type::Record(more) = rest else {
                return Err(error("the rest of a record is not a record"));
            };
            record.extend(more);
            record.sort_by_key(|(name, _)| *name);
            Ok(Type::Record(record))
        }
        InferredType::Tuple(members) => Ok(Type::Tuple(
            members
                .iter()
                .map(|member| substitute_type(member, substitution))
                .collect::<Result<_, _>>()?,
        )),
    }
}

fn match_type(
    template: &InferredType,
    concrete: &Type,
    substitution: &mut HashMap<TypeVariable, Type>,
) -> Result<(), SpecializeError> {
    match (template, concrete) {
        (InferredType::Variable(variable), concrete) => {
            if let Some(previous) = substitution.get(variable) {
                if previous != concrete {
                    return Err(error(
                        "one type variable received incompatible specializations",
                    ));
                }
            } else {
                substitution.insert(*variable, concrete.clone());
            }
            Ok(())
        }
        (InferredType::Named(a, aa), Type::Named(b, ba)) if a == b && aa.len() == ba.len() => {
            for (a, b) in aa.iter().zip(ba) {
                match_type(a, b, substitution)?;
            }
            Ok(())
        }
        (InferredType::Function(ap, ar), Type::Function(bp, br)) if ap.len() == bp.len() => {
            for (a, b) in ap.iter().zip(bp) {
                match_type(a, b, substitution)?;
            }
            match_type(ar, br, substitution)
        }
        (InferredType::Variants(tags, tail), Type::Variants(concrete)) => {
            for (label, fields) in tags {
                let Some((_, held)) = concrete.iter().find(|(found, _)| found == label) else {
                    return Err(error("a concrete tag row lacks a tag its use holds"));
                };
                if fields.len() != held.len() {
                    return Err(error("a tag's fields differ between a use and its row"));
                }
                for (field, held) in fields.iter().zip(held) {
                    match_type(field, held, substitution)?;
                }
            }
            let rest: Vec<_> = concrete
                .iter()
                .filter(|(label, _)| !tags.iter().any(|(found, _)| found == label))
                .cloned()
                .collect();
            match tail.as_deref() {
                Some(tail) => match_type(tail, &Type::Variants(rest), substitution),
                None if rest.is_empty() => Ok(()),
                None => Err(error("a closed tag row received more tags")),
            }
        }
        (InferredType::Record(fields, tail), Type::Record(concrete)) => {
            for (name, field) in fields {
                let Some((_, held)) = concrete.iter().find(|(found, _)| found == name) else {
                    return Err(error("a concrete record lacks a field its use has"));
                };
                match_type(field, held, substitution)?;
            }
            let rest: Vec<_> = concrete
                .iter()
                .filter(|(name, _)| !fields.iter().any(|(found, _)| found == name))
                .cloned()
                .collect();
            match tail.as_deref() {
                Some(tail) => match_type(tail, &Type::Record(rest), substitution),
                None if rest.is_empty() => Ok(()),
                None => Err(error("a closed record received more fields")),
            }
        }
        (InferredType::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
            for (a, b) in a.iter().zip(b) {
                match_type(a, b, substitution)?;
            }
            Ok(())
        }
        _ => Err(error("a concrete use does not match its inferred scheme")),
    }
}

fn scheme_result(scheme: &InferredScheme, result: &Type) -> Result<Type, SpecializeError> {
    let InferredType::Function(_, template_result) = &scheme.ty else {
        return Err(error("literal helper is not a function"));
    };
    let mut substitution = HashMap::new();
    match_type(template_result, result, &mut substitution)?;
    substitute_type(&scheme.ty, &substitution)
}

pub(crate) fn surface_type(
    ty: &h::Type,
    variables: &HashMap<Symbol, Type>,
) -> Result<Type, SpecializeError> {
    match ty {
        h::Type::Named(name, arguments) => Ok(Type::Named(
            *name,
            arguments
                .iter()
                .map(|argument| surface_type(argument, variables))
                .collect::<Result<_, _>>()?,
        )),
        h::Type::Variable(variable) => variables
            .get(variable)
            .cloned()
            .ok_or_else(|| error("data field contains an unbound type variable")),
        h::Type::Function(parameters, result) => Ok(Type::Function(
            parameters
                .iter()
                .map(|parameter| surface_type(parameter, variables))
                .collect::<Result<_, _>>()?,
            Box::new(surface_type(result, variables)?),
        )),
        h::Type::Variants(constructors) => Ok(Type::row(
            constructors
                .iter()
                .map(|constructor| {
                    let fields = constructor
                        .fields
                        .iter()
                        .map(|field| surface_type(field, variables))
                        .collect::<Result<_, _>>()?;
                    Ok((constructor.name, fields))
                })
                .collect::<Result<_, SpecializeError>>()?,
        )),
        h::Type::Record(fields, _) => Ok(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((*name, surface_type(ty, variables)?)))
                .collect::<Result<_, SpecializeError>>()?,
        )),
        h::Type::Tuple(members) => Ok(Type::Tuple(
            members
                .iter()
                .map(|member| surface_type(member, variables))
                .collect::<Result<_, _>>()?,
        )),
    }
}

fn located(module: ModuleId, span: crate::ast::Span, message: &str) -> SpecializeError {
    SpecializeError {
        message: message.to_owned(),
        at: Some((module, span)),
    }
}

fn error(message: impl Into<String>) -> SpecializeError {
    SpecializeError {
        message: message.into(),
        at: None,
    }
}
