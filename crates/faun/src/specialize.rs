//! Specialize checked polymorphic HIR into concrete, still-functional terms.
//!
//! Barb has no type variables. This pass follows direct calls from one concrete
//! entry signature and clones each reachable global at every concrete function
//! type used by the program. Function values remain explicit until
//! [`crate::callbacks`] makes each into the definition it is handed to.
//! Every function key carries a signature, not an arbitrary type; an external
//! names its provider instead of carrying an empty body.

#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, VecDeque};

use num_bigint::BigUint;

use crate::blessed::NumeralType;
use crate::blessed::{LiteralExpr, PreludeIds};
use crate::check::{CheckedProgram, InferredBound, InferredScheme, InferredType, TypeVariable};
use crate::diagnostic::LowerError;
use crate::hir as h;
use crate::typed as t;
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Type {
    Named(Symbol, Vec<Self>),
    Function(Signature),
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

    /// Take the signature at a checked function boundary.
    fn into_signature(self) -> Result<Signature, LowerError> {
        match self {
            Self::Function(signature) => Ok(signature),
            _ => Err(error("a checked function has a non-function type")),
        }
    }

    /// Instantiate each constructor's fields, or return a tag row's tags.
    pub(crate) fn constructors(
        &self,
        data: &HashMap<Symbol, crate::declarations::Data>,
    ) -> Result<Vec<(Symbol, Vec<Self>)>, LowerError> {
        if let Self::Variants(tags) = self {
            return Ok(tags.clone());
        }
        let Self::Named(name, arguments) = self else {
            return Err(error("pattern matching requires a named data type"));
        };
        let data = data
            .get(name)
            .ok_or_else(|| error("named type has no data declaration"))?;
        if data.parameters.len() != arguments.len() {
            return Err(error("type specialization has the wrong argument count"));
        }
        let variables: HashMap<_, _> = data
            .parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect();
        let mut constructors = Vec::new();
        for constructor in &data.constructors {
            constructors.push((
                constructor.name,
                constructor
                    .fields
                    .iter()
                    .map(|field| surface_type(field, &variables))
                    .collect::<Result<_, LowerError>>()?,
            ));
        }
        if let Some(wrapper) = &data.wrapper {
            constructors.push((
                wrapper.constructor,
                vec![surface_type(&wrapper.field, &variables)?],
            ));
        }
        Ok(constructors)
    }

    /// The types of a record's fields, in their order, or a tuple's members:
    /// the columns a product is taken apart into.
    pub(crate) fn members(&self) -> Option<Vec<Self>> {
        match self {
            Self::Record(fields) => Some(fields.iter().map(|(_, ty)| ty.clone()).collect()),
            Self::Tuple(members) => Some(members.clone()),
            _ => None,
        }
    }
}

/// A concrete function's parameters and result, including callback signatures.
/// The result is boxed to break the recursion through `Type::Function`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Signature {
    pub(crate) parameters: Vec<Type>,
    pub(crate) result: Box<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FunctionKey {
    pub(crate) name: Symbol,
    pub(crate) signature: Signature,
    /// Which definition made from `name` at this signature this is.
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
    pub(crate) data: HashMap<Symbol, crate::declarations::Data>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) definition: Definition,
}

/// Keep a provider declaration separate from a body, even one with no clauses.
#[derive(Clone, Debug)]
pub(crate) enum Definition {
    External(Symbol),
    Body(Vec<Clause>),
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
    /// A list's end, which only a clause takes apart, as a [`Split`]; see
    /// [`Specializer::tested`].
    Ending,
    Split(Box<Split>),
}

/// A list's end, `[*front, a, b]`, as a clause takes it apart: the list
/// split before its last `last.len()` elements, through its type's `len`,
/// `take` and `drop` at this element type, each side matched as written.
#[derive(Clone, Debug)]
pub(crate) struct Split {
    pub(crate) front: Pattern,
    pub(crate) last: Vec<Pattern>,
    pub(crate) len: FunctionKey,
    pub(crate) take: FunctionKey,
    pub(crate) drop: FunctionKey,
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
    /// `if condition then yes else no`; see [`crate::hir::ExprKind::If`].
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`; see [`crate::hir::ExprKind::Is`]: a row for
    /// each choice of the pattern's alternatives, with the tests its
    /// literals ask.
    Is(Box<Expr>, Vec<(Pattern, Option<Expr>)>),
    /// Bindings, then the answer; see [`crate::hir::ExprKind::Block`].
    Block(Box<Body>),
}

/// Specialize what one parameterless `entry` reaches, and nothing else.
#[cfg(test)]
pub(crate) fn monomorphize_from_entry(
    checked: &CheckedProgram,
    entry: Symbol,
) -> Result<Program, LowerError> {
    let specializer = Specializer::new(checked);
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
) -> Result<Program, LowerError> {
    let specializer = Specializer::new(checked);
    let entry = main
        .map(|main| specializer.entry_key(main.symbol, Some(host.host)))
        .transpose()?;
    specializer.run(entry, package_roots(checked)?)
}

/// The package's definitions that stand on their own, in the order written,
/// each generic one at the empty type.
fn package_roots(checked: &CheckedProgram) -> Result<Vec<FunctionKey>, LowerError> {
    let resolved = &checked.resolved;
    let mut roots = Vec::new();
    for function in &resolved.program.functions {
        if !resolved.package.contains(&function.module)
            || matches!(function.definition, t::Definition::External(_))
        {
            continue;
        }
        let scheme = &function.scheme;
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
        let signature = substitute_type(&scheme.ty, &placeholder)?.into_signature()?;
        if signature.parameters.iter().any(holds_function) {
            continue;
        }
        roots.push(FunctionKey {
            name: function.name,
            signature,
            instance: Instance::Written,
        });
    }
    Ok(roots)
}

/// Whether a value of `ty` may hold a function, as far as its type says.
fn holds_function(ty: &Type) -> bool {
    match ty {
        Type::Function(_) => true,
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
    /// The spellings a refusal names.
    symbols: &'a crate::Symbols,
    prelude: &'a PreludeIds,
    members: &'a HashMap<(Symbol, Symbol), Symbol>,
    definitions: HashMap<Symbol, &'a t::Function>,
    data: HashMap<Symbol, crate::declarations::Data>,
    constructors: HashMap<Symbol, (Symbol, &'a [h::Type])>,
    requested: HashMap<FunctionKey, usize>,
    /// The `equals` and `cmp` of closed records and tuples, which nothing
    /// declares, each with the first place that asked for it.
    structural: HashMap<FunctionKey, (ModuleId, crate::ast::Span)>,
    queue: VecDeque<FunctionKey>,
    functions: Vec<Option<Function>>,
    /// The next local a test's literal is held in, numbered apart from
    /// every clause's own.
    test_locals: u32,
}

impl<'a> Specializer<'a> {
    fn new(checked: &'a CheckedProgram) -> Self {
        let program = &checked.resolved.program;
        let constructors = program
            .data
            .values()
            .flat_map(|data| {
                data.constructors
                    .iter()
                    .map(|constructor| {
                        (constructor.name, (data.name, constructor.fields.as_slice()))
                    })
                    .chain(data.wrapper.iter().map(|wrapper| {
                        (
                            wrapper.constructor,
                            (data.name, std::slice::from_ref(&wrapper.field)),
                        )
                    }))
            })
            .collect();
        Self {
            symbols: &checked.resolved.symbols,
            prelude: &checked.prelude,
            members: &program.members,
            definitions: program
                .functions
                .iter()
                .map(|function| (function.name, function))
                .collect(),
            data: program.data.clone(),
            constructors,
            requested: HashMap::new(),
            structural: HashMap::new(),
            queue: VecDeque::new(),
            functions: Vec::new(),
            test_locals: 1 << 30,
        }
    }

    /// The key `entry` is specialized at, checking it takes what an entry
    /// may: nothing, or for an application exactly one `Host`.
    fn entry_key(
        &self,
        entry: Symbol,
        application_host: Option<Symbol>,
    ) -> Result<FunctionKey, LowerError> {
        let scheme = self
            .definitions
            .get(&entry)
            .map(|function| &function.scheme)
            .ok_or_else(|| error("entry has no inferred type"))?;
        let signature = concrete_scheme(scheme)?.into_signature()?;
        let valid_parameters = match (application_host, signature.parameters.as_slice()) {
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
            signature,
            instance: Instance::Written,
        })
    }

    /// Specialize everything `entry` reaches, then everything each root
    /// reaches that it did not, so what the entry reaches keeps its order.
    fn run(
        mut self,
        entry: Option<FunctionKey>,
        roots: Vec<FunctionKey>,
    ) -> Result<Program, LowerError> {
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
        if self.is_structural(key.name, &key.signature.parameters) {
            self.structural.entry(key.clone()).or_insert(at);
        }
        self.request(key);
    }

    /// Whether `name` on these parameters is a closed record's or a
    /// tuple's own `equals`, `cmp`, `to_str` or `hash_into`, or a tag row's
    /// own `equals` or `to_str`.
    fn is_structural(&self, name: Symbol, parameters: &[Type]) -> bool {
        let receiver = parameters.first();
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

    fn specialize_function(&mut self, key: &FunctionKey) -> Result<Function, LowerError> {
        if let Some(&at) = self.structural.get(key) {
            return self.structural_function(key, at);
        }
        let function = *self
            .definitions
            .get(&key.name)
            .ok_or_else(|| error("a called definition is missing"))?;
        let clauses = match &function.definition {
            t::Definition::External(provider) => {
                return Ok(Function {
                    key: key.clone(),
                    definition: Definition::External(*provider),
                });
            }
            t::Definition::Body(clauses) => clauses,
        };
        let module = function.module;
        let mut specialized = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let mut substitution = HashMap::new();
            match_parameters(
                &clause.signature.parameters,
                &clause.signature.result,
                &key.signature,
                &mut substitution,
            )?;
            self.discharge(&clause.bounds, &mut substitution)
                .map_err(|message| located(module, clause.span, &message))?;
            specialized.extend(self.clause(
                module,
                clause,
                &substitution,
                &key.signature.parameters,
            )?);
        }
        Ok(Function {
            key: key.clone(),
            definition: Definition::Body(specialized),
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
    ) -> Result<Function, LowerError> {
        let receiver = key.signature.parameters[0].clone();
        let answer = key.signature.result.as_ref().clone();
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
            definition: Definition::Body(clauses),
        })
    }

    /// A tag row's `to_str`, as Ori writes a tag: its name, and the `to_str`
    /// of each of its fields after it in parentheses, `Invalid(3)`.
    fn row_to_str(
        &mut self,
        key: &FunctionKey,
        (module, span): (ModuleId, crate::ast::Span),
        tags: &[(Symbol, Vec<Type>)],
    ) -> Result<Function, LowerError> {
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
            definition: Definition::Body(clauses),
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
    ) -> Result<Function, LowerError> {
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
            definition: Definition::Body(vec![Clause {
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
            }]),
        })
    }

    /// A string literal of `text`.
    fn text(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        text: &str,
    ) -> Result<Expr, LowerError> {
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
    ) -> Result<Clause, LowerError> {
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
            (self.prelude.order_or, self.prelude.order_eq)
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
    ) -> Result<Clause, LowerError> {
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
        clause: &t::Clause,
        substitution: &HashMap<TypeVariable, Type>,
        parameters: &[Type],
    ) -> Result<Vec<Clause>, LowerError> {
        let guard = clause
            .guard
            .as_ref()
            .map(|expression| self.expr(module, expression, substitution))
            .transpose()?;
        let body = self.body(module, &clause.body, substitution)?;
        let mut rows = t::Pattern::rows(&clause.patterns);
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
        clause: &t::Clause,
        row: &[t::Pattern],
        parameters: &[Type],
        (guard, body): (Option<Expr>, Body),
    ) -> Result<Clause, LowerError> {
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
        pattern: &t::Pattern,
        ty: &Type,
        (next, tests): (&mut u32, &mut Vec<Expr>),
    ) -> Result<Pattern, LowerError> {
        // A range binds nothing it shows: a fresh name, and each end it has
        // asked of that name, through the type's `cmp`.
        if let t::Pattern::Range(start, end) = pattern {
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
        let literal = match pattern {
            t::Pattern::String(bytes) => Some((
                crate::blessed::string(bytes, self.prelude),
                self.prelude.str_equals,
            )),
            t::Pattern::Number {
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
        let fields: Option<(Symbol, Vec<(&t::Pattern, Type)>)> = match (pattern, ty) {
            (t::Pattern::Constructor(constructor, fields), Type::Named(..)) => {
                let types = self.constructor_fields(*constructor, ty)?;
                Some((*constructor, fields.iter().zip(types).collect()))
            }
            (
                t::Pattern::Tag(label, fields) | t::Pattern::Constructor(label, fields),
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
            (t::Pattern::List(elements, rest), Type::Named(_, arguments))
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
            (t::Pattern::Ending(front, last), Type::Named(_, arguments))
                if arguments.len() == 1 =>
            {
                let element = arguments[0].clone();
                let nat = Type::Named(self.prelude.nat, Vec::new());
                let len = self.method_key(self.prelude.list_len, ty, &[], &nat)?;
                let take =
                    self.method_key(self.prelude.list_take, ty, std::slice::from_ref(&nat), ty)?;
                let drop = self.method_key(self.prelude.list_drop, ty, &[nat], ty)?;
                for key in [&len, &take, &drop] {
                    self.request(key.clone());
                }
                Pattern::Split(Box::new(Split {
                    front: self.tested((module, span), front, ty, (next, tests))?,
                    last: last
                        .iter()
                        .map(|item| self.tested((module, span), item, &element, (next, tests)))
                        .collect::<Result<_, _>>()?,
                    len,
                    take,
                    drop,
                }))
            }
            (t::Pattern::Record(fields, _), Type::Record(types)) => Pattern::Record(
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
                    .collect::<Result<_, LowerError>>()?,
            ),
            (t::Pattern::Tuple(members), Type::Tuple(types)) => Pattern::Product(
                members
                    .iter()
                    .zip(types)
                    .map(|(member, ty)| self.tested((module, span), member, ty, (next, tests)))
                    .collect::<Result<_, _>>()?,
            ),
            _ => convert_pattern(pattern),
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
    ) -> Result<Option<Expr>, LowerError> {
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

    fn body(
        &mut self,
        module: ModuleId,
        body: &t::Body,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Body, LowerError> {
        Ok(Body {
            bindings: body
                .bindings
                .iter()
                .map(|binding| {
                    Ok(Binding {
                        pattern: convert_pattern(&binding.pattern),
                        value: self.expr(module, &binding.value, substitution)?,
                    })
                })
                .collect::<Result<_, LowerError>>()?,
            result: self.expr(module, &body.result, substitution)?,
        })
    }

    fn expr(
        &mut self,
        module: ModuleId,
        expression: &t::Expr,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Expr, LowerError> {
        let ty = self.site_type(&expression.ty, substitution)?;
        let span = expression.span;
        let kind = match &expression.kind {
            t::ExprKind::Block(body) => {
                ExprKind::Block(Box::new(self.body(module, body, substitution)?))
            }
            t::ExprKind::Local(local) => ExprKind::Local(*local),
            t::ExprKind::Function(name) => {
                let key = FunctionKey {
                    name: *name,
                    signature: ty.clone().into_signature()?,
                    instance: Instance::Written,
                };
                self.request(key.clone());
                ExprKind::Function(key)
            }
            t::ExprKind::Constructor(name) => {
                if matches!(ty, Type::Function(_)) {
                    ExprKind::ConstructorFunction(*name)
                } else {
                    ExprKind::Construct(*name, Vec::new())
                }
            }
            t::ExprKind::Construct(name, fields) => ExprKind::Construct(
                *name,
                fields
                    .iter()
                    .map(|e| self.expr(module, e, substitution))
                    .collect::<Result<_, _>>()?,
            ),
            t::ExprKind::Literal(literal) => return self.literal(module, span, literal, &ty),
            t::ExprKind::Numeral(numeral) => return self.numeral(module, span, numeral, &ty),
            t::ExprKind::Record(fields) => ExprKind::Record(
                fields
                    .iter()
                    .map(|(name, value)| Ok((*name, self.expr(module, value, substitution)?)))
                    .collect::<Result<_, LowerError>>()?,
            ),
            t::ExprKind::Update(base, fields) => ExprKind::Update(
                Box::new(self.expr(module, base, substitution)?),
                fields
                    .iter()
                    .map(|(name, value)| Ok((*name, self.expr(module, value, substitution)?)))
                    .collect::<Result<_, LowerError>>()?,
            ),
            t::ExprKind::Tuple(members) => ExprKind::Tuple(
                members
                    .iter()
                    .map(|e| self.expr(module, e, substitution))
                    .collect::<Result<_, _>>()?,
            ),
            t::ExprKind::Lambda(patterns, body) => ExprKind::Lambda(
                expression.site,
                patterns.iter().map(convert_pattern).collect(),
                Box::new(self.expr(module, body, substitution)?),
            ),
            t::ExprKind::Call(head, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|e| self.expr(module, e, substitution))
                    .collect::<Result<_, _>>()?;
                let head = self.expr(module, head, substitution)?;
                match head.kind {
                    ExprKind::Function(key) => ExprKind::DirectCall(key, arguments),
                    ExprKind::ConstructorFunction(name) => ExprKind::Construct(name, arguments),
                    // Nullary constructors may be written with `()`.
                    ExprKind::Construct(name, fields) if fields.is_empty() => {
                        ExprKind::Construct(name, arguments)
                    }
                    _ => ExprKind::Invoke(Box::new(head), arguments),
                }
            }
            // A bare read through a bound is the owner's field where it has one.
            t::ExprKind::Method(
                t::Target::Bound {
                    owner,
                    member,
                    bare: true,
                },
                arguments,
            ) if self
                .field_type(&self.site_type(owner, substitution)?, *member)?
                .is_some() =>
            {
                let [receiver] = arguments.as_slice() else {
                    return Err(error("a field is read off one value"));
                };
                let receiver = self.expr(module, receiver, substitution)?;
                ExprKind::Project(Box::new(receiver), *member)
            }
            t::ExprKind::Method(target, arguments) => {
                let name = match target {
                    t::Target::Direct(name) => *name,
                    t::Target::Bound { owner, member, .. } => {
                        let owner = self.site_type(owner, substitution)?;
                        self.implementation(&owner, *member)?
                    }
                };
                let arguments = arguments
                    .iter()
                    .map(|e| self.expr(module, e, substitution))
                    .collect::<Result<Vec<_>, _>>()?;
                let key = if let Some((receiver, rest)) = arguments.split_first() {
                    let types: Vec<_> = rest.iter().map(|arg| arg.ty.clone()).collect();
                    self.method_key(name, &receiver.ty, &types, &ty)?
                } else {
                    FunctionKey {
                        name,
                        signature: Signature {
                            parameters: Vec::new(),
                            result: Box::new(ty.clone()),
                        },
                        instance: Instance::Written,
                    }
                };
                self.request_at(key.clone(), (module, span));
                ExprKind::DirectCall(key, arguments)
            }
            t::ExprKind::Project(receiver, field) => {
                ExprKind::Project(Box::new(self.expr(module, receiver, substitution)?), *field)
            }
            t::ExprKind::Widen(value) => {
                let value = self.expr(module, value, substitution)?;
                if value.ty == ty {
                    return Ok(value);
                }
                ExprKind::Widen(Box::new(value))
            }
            // A row for each choice of alternatives, its literals tested
            // as a clause's are, before nothing.
            t::ExprKind::Is(value, pattern) => {
                let value = self.expr(module, value, substitution)?;
                let mut next = self.test_locals;
                let mut rows = Vec::new();
                for row in t::Pattern::rows(std::slice::from_ref(pattern)) {
                    let mut tests = Vec::new();
                    let pattern =
                        self.tested((module, span), &row[0], &value.ty, (&mut next, &mut tests))?;
                    rows.push((pattern, self.joined(module, span, tests, None)?));
                }
                self.test_locals = next;
                ExprKind::Is(Box::new(value), rows)
            }
            t::ExprKind::If(condition, yes, no) => ExprKind::If(
                Box::new(self.expr(module, condition, substitution)?),
                Box::new(self.expr(module, yes, substitution)?),
                Box::new(self.expr(module, no, substitution)?),
            ),
            t::ExprKind::Try(value) => {
                ExprKind::Try(Box::new(self.expr(module, value, substitution)?))
            }
        };
        Ok(Expr {
            module,
            span,
            ty,
            kind,
        })
    }

    /// A site's type at this specialization. A type variable nothing pinned
    /// -- the element of `[]` in `[].len()` -- is `Nat`, as in Ori: no value
    /// of it is ever built, so which type it is cannot be seen. A row's
    /// rest nothing pinned holds no tags instead.
    fn site_type(
        &self,
        template: &InferredType,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Type, LowerError> {
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

    /// The type of `owner`'s field `name`, where it is a record having it
    /// or a declared type whose record does.
    fn field_type(&self, owner: &Type, name: Symbol) -> Result<Option<Type>, LowerError> {
        let fields = match owner {
            Type::Record(fields) => fields.clone(),
            Type::Named(owner, arguments) => {
                let Some(wrapper) = self.data.get(owner).and_then(|data| data.wrapper.as_ref())
                else {
                    return Ok(None);
                };
                let data = &self.data[owner];
                let variables: HashMap<_, _> = data
                    .parameters
                    .iter()
                    .copied()
                    .zip(arguments.iter().cloned())
                    .collect();
                let Type::Record(fields) = surface_type(&wrapper.field, &variables)? else {
                    return Ok(None);
                };
                fields
            }
            _ => return Ok(None),
        };
        let field = fields
            .into_iter()
            .find(|(field, _)| *field == name)
            .map(|(_, ty)| ty);
        Ok(field)
    }

    /// Which method of `owner` is its `member`.
    fn implementation(&self, owner: &Type, member: Symbol) -> Result<Symbol, LowerError> {
        if self.is_structural(member, std::slice::from_ref(owner)) {
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
                // A field read: what the owner's field is, the bound answers.
                let field = if bound.bare {
                    self.field_type(&owner, bound.member)
                        .map_err(|failure| failure.message)?
                } else {
                    None
                };
                if let Some(field) = field {
                    let InferredType::Function(_, result) = &bound.ty else {
                        return Err("a field bound reads a value".to_owned());
                    };
                    match_type(result, &field, substitution).map_err(|failure| failure.message)?;
                    continue;
                }
                let target = self
                    .implementation(&owner, bound.member)
                    .map_err(|failure| failure.message)?;
                // A record's or a tuple's own member takes two of it: the
                // owner says all there is.
                if self.is_structural(target, std::slice::from_ref(&owner)) {
                    continue;
                }
                let scheme = self
                    .definitions
                    .get(&target)
                    .map(|function| &function.scheme)
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
        span: crate::ast::Span,
        numeral: &t::Numeral,
        ty: &Type,
    ) -> Result<Expr, LowerError> {
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
    ) -> Result<Expr, LowerError> {
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
    ) -> Result<Expr, LowerError> {
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

    fn method_key(
        &self,
        name: Symbol,
        receiver: &Type,
        arguments: &[Type],
        result: &Type,
    ) -> Result<FunctionKey, LowerError> {
        let mut parameters = Vec::with_capacity(arguments.len() + 1);
        parameters.push(receiver.clone());
        parameters.extend_from_slice(arguments);
        let signature = Signature {
            parameters,
            result: Box::new(result.clone()),
        };
        if self.is_structural(name, &signature.parameters) {
            return Ok(FunctionKey {
                name,
                signature,
                instance: Instance::Written,
            });
        }
        let scheme = self
            .definitions
            .get(&name)
            .map(|function| &function.scheme)
            .ok_or_else(|| error("method target has no inferred scheme"))?;
        let mut substitution = HashMap::new();
        match_signature(&scheme.ty, &signature, &mut substitution)?;
        Ok(FunctionKey {
            name,
            signature,
            instance: Instance::Written,
        })
    }

    fn literal(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        literal: &LiteralExpr,
        expected: &Type,
    ) -> Result<Expr, LowerError> {
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
                    .definitions
                    .get(function)
                    .map(|function| &function.scheme)
                    .ok_or_else(|| error("literal helper has no inferred scheme"))?;
                let signature = scheme_result(scheme, expected)?;
                if arguments.len() != signature.parameters.len() {
                    return Err(error("literal helper arity does not match its declaration"));
                }
                let key = FunctionKey {
                    name: *function,
                    signature,
                    instance: Instance::Written,
                };
                self.request(key.clone());
                let arguments = arguments
                    .iter()
                    .zip(&key.signature.parameters)
                    .map(|(argument, ty)| self.literal(module, span, argument, ty))
                    .collect::<Result<_, _>>()?;
                ExprKind::DirectCall(key, arguments)
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
    ) -> Result<Vec<Type>, LowerError> {
        let (declared_owner, fields) = self
            .constructors
            .get(&constructor)
            .ok_or_else(|| error("constructor declaration is missing"))?;
        let Type::Named(owner, arguments) = result else {
            return Err(error("constructor result is not a named type"));
        };
        if owner != declared_owner {
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
        fields
            .iter()
            .map(|field| surface_type(field, &variables))
            .collect()
    }
}

/// A checked pattern as specialization reads it, each claimed word as the
/// reading checking gave it.
fn convert_pattern(pattern: &t::Pattern) -> Pattern {
    let convert = convert_pattern;
    match pattern {
        t::Pattern::Dual(..) => unreachable!("typed patterns cannot be ambiguous"),
        t::Pattern::Wild => Pattern::Wild,
        t::Pattern::Or(_) => unreachable!("a clause is specialized a row at a time"),
        t::Pattern::String(_) => Pattern::String,
        t::Pattern::Bind(local) => Pattern::Bind(*local),
        t::Pattern::Constructor(constructor, fields) | t::Pattern::Tag(constructor, fields) => {
            Pattern::Constructor(*constructor, fields.iter().map(convert).collect())
        }
        t::Pattern::Number {
            magnitude,
            negative,
        } => Pattern::Number {
            magnitude: magnitude.clone(),
            negative: *negative,
        },
        t::Pattern::Range(..) => Pattern::Range,
        t::Pattern::Ending(..) => Pattern::Ending,
        t::Pattern::List(elements, rest) => Pattern::List(
            elements.iter().map(convert).collect(),
            rest.as_deref().map(convert).map(Box::new),
        ),
        // A field an open pattern leaves out is taken whatever it is.
        t::Pattern::Record(fields, _) => Pattern::Record(
            fields
                .iter()
                .map(|(name, pattern)| (*name, convert(pattern)))
                .collect(),
        ),
        t::Pattern::Tuple(members) => Pattern::Product(members.iter().map(convert).collect()),
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

fn concrete_scheme(scheme: &InferredScheme) -> Result<Type, LowerError> {
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
) -> Result<Type, LowerError> {
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
        InferredType::Function(parameters, result) => Ok(Type::Function(Signature {
            parameters: parameters
                .iter()
                .map(|parameter| substitute_type(parameter, substitution))
                .collect::<Result<_, _>>()?,
            result: Box::new(substitute_type(result, substitution)?),
        })),
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
                .collect::<Result<Vec<_>, LowerError>>()?;
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
                .collect::<Result<Vec<_>, LowerError>>()?;
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

/// Match a checked signature without wrapping and cloning its concrete type.
fn match_signature(
    template: &InferredType,
    concrete: &Signature,
    substitution: &mut HashMap<TypeVariable, Type>,
) -> Result<(), LowerError> {
    let InferredType::Function(parameters, result) = template else {
        return Err(error("a checked function has a non-function type"));
    };
    match_parameters(parameters, result, concrete, substitution)
}

fn match_parameters(
    parameters: &[InferredType],
    result: &InferredType,
    concrete: &Signature,
    substitution: &mut HashMap<TypeVariable, Type>,
) -> Result<(), LowerError> {
    if parameters.len() != concrete.parameters.len() {
        return Err(error("a concrete use does not match its inferred scheme"));
    }
    for (parameter, concrete) in parameters.iter().zip(&concrete.parameters) {
        match_type(parameter, concrete, substitution)?;
    }
    match_type(result, &concrete.result, substitution)
}

fn match_type(
    template: &InferredType,
    concrete: &Type,
    substitution: &mut HashMap<TypeVariable, Type>,
) -> Result<(), LowerError> {
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
        (InferredType::Function(..), Type::Function(signature)) => {
            match_signature(template, signature, substitution)
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

fn scheme_result(scheme: &InferredScheme, result: &Type) -> Result<Signature, LowerError> {
    let InferredType::Function(_, template_result) = &scheme.ty else {
        return Err(error("literal helper is not a function"));
    };
    let mut substitution = HashMap::new();
    match_type(template_result, result, &mut substitution)?;
    substitute_type(&scheme.ty, &substitution)?.into_signature()
}

pub(crate) fn surface_type(
    ty: &h::Type,
    variables: &HashMap<Symbol, Type>,
) -> Result<Type, LowerError> {
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
        h::Type::Hole => Err(error(
            "`_` stands for a type only in a function's signature",
        )),
        h::Type::Function(parameters, result) => Ok(Type::Function(Signature {
            parameters: parameters
                .iter()
                .map(|parameter| surface_type(parameter, variables))
                .collect::<Result<_, _>>()?,
            result: Box::new(surface_type(result, variables)?),
        })),
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
                .collect::<Result<_, LowerError>>()?,
        )),
        h::Type::Record(fields, _) => Ok(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((*name, surface_type(ty, variables)?)))
                .collect::<Result<_, LowerError>>()?,
        )),
        h::Type::Tuple(members) => Ok(Type::Tuple(
            members
                .iter()
                .map(|member| surface_type(member, variables))
                .collect::<Result<_, _>>()?,
        )),
    }
}

fn located(module: ModuleId, span: crate::ast::Span, message: &str) -> LowerError {
    LowerError::new(message, Some((module, span)))
}

fn error(message: impl Into<String>) -> LowerError {
    LowerError::new(message.into(), None)
}
