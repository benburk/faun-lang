//! Specialize checked polymorphic HIR into concrete, still-functional terms.
//!
//! Barb has no type variables. This pass follows direct calls from one concrete
//! entry signature and clones each reachable global at every concrete function
//! type used by the program. Function values remain explicit for the separate
//! defunctionalizing lowering pass.

#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use num_bigint::BigUint;

use crate::blessed::{LiteralExpr, PreludeIds};
use crate::check::{CheckedProgram, InferredScheme, InferredType, TypeVariable, Types};
use crate::hir as h;
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Type {
    Named(Symbol, Vec<Self>),
    Function(Vec<Self>, Box<Self>),
    Empty,
    Record(Vec<(Symbol, Self)>),
}

impl Type {
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
    Number { magnitude: BigUint, negative: bool },
    Range(BigUint, BigUint),
    List(Vec<Self>, Option<Box<Self>>),
    Record(Vec<(Symbol, Self)>),
    Product(Vec<Self>),
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
    Record(Vec<(Symbol, Expr)>),
    Project(Box<Expr>, Symbol),
    DirectCall(FunctionKey, Vec<Expr>),
    Invoke(Box<Expr>, Vec<Expr>),
    Lambda(Vec<Pattern>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecializeError {
    pub message: String,
}

impl fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for SpecializeError {}

/// Specialize what one parameterless `entry` reaches, and nothing else.
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
        // A generic definition can do nothing with a value of a type variable
        // but hand it on, having no constraint that would say more, so how it
        // behaves is the same at every type: judge it once, at the empty type.
        let placeholder = scheme
            .variables
            .iter()
            .map(|variable| (*variable, Type::Empty))
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
        Type::Empty => false,
    }
}

struct Specializer<'a> {
    checked: &'a Types,
    prelude: &'a PreludeIds,
    expression_types: HashMap<(ModuleId, crate::ast::Span), &'a InferredType>,
    clause_types: HashMap<(ModuleId, crate::ast::Span), &'a InferredType>,
    literal_sites: HashMap<(ModuleId, crate::ast::Span), &'a LiteralExpr>,
    method_sites: HashMap<(ModuleId, crate::ast::Span), Symbol>,
    projection_sites: HashMap<(ModuleId, crate::ast::Span), Symbol>,
    definitions: HashMap<Symbol, Vec<(ModuleId, &'a h::Clause)>>,
    signatures: HashMap<Symbol, Symbol>,
    data: HashMap<Symbol, h::DataDecl>,
    constructors: HashMap<Symbol, Constructor>,
    requested: HashMap<FunctionKey, usize>,
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
            .map(|site| ((site.module, site.span), &site.ty))
            .collect();
        let clause_types = checked
            .clauses
            .iter()
            .map(|site| ((site.module, site.span), &site.ty))
            .collect();
        let literal_sites = checked
            .literals
            .iter()
            .map(|site| ((site.module, site.span), &site.value))
            .collect();
        let method_sites = checked
            .methods
            .iter()
            .map(|site| ((site.module, site.span), site.target))
            .collect();
        let projection_sites = checked
            .projections
            .iter()
            .map(|site| ((site.module, site.span), site.field))
            .collect();
        Ok(Self {
            checked,
            prelude,
            expression_types,
            clause_types,
            literal_sites,
            method_sites,
            projection_sites,
            definitions,
            signatures,
            data,
            constructors,
            requested: HashMap::new(),
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
        Ok(Program {
            entry,
            functions: self
                .functions
                .into_iter()
                .map(|function| function.expect("every requested function was specialized"))
                .collect(),
            data: self.data,
        })
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

    fn specialize_function(&mut self, key: &FunctionKey) -> Result<Function, SpecializeError> {
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
            let template = self
                .clause_types
                .get(&(module, clause.span))
                .ok_or_else(|| error("checked clause type is missing"))?;
            let mut substitution = HashMap::new();
            match_type(template, &key.ty, &mut substitution)?;
            specialized.push(self.clause(module, clause, &substitution)?);
        }
        Ok(Function {
            key: key.clone(),
            clauses: specialized,
            provider,
        })
    }

    fn clause(
        &mut self,
        module: ModuleId,
        clause: &h::Clause,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Clause, SpecializeError> {
        Ok(Clause {
            patterns: clause.patterns.iter().map(convert_pattern).collect(),
            guard: clause
                .guard
                .as_ref()
                .map(|expression| self.expr(module, expression, substitution))
                .transpose()?,
            body: Body {
                bindings: clause
                    .body
                    .bindings
                    .iter()
                    .map(|binding| {
                        Ok(Binding {
                            pattern: convert_pattern(&binding.pattern),
                            value: self.expr(module, &binding.value, substitution)?,
                        })
                    })
                    .collect::<Result<_, SpecializeError>>()?,
                result: self.expr(module, &clause.body.result, substitution)?,
            },
        })
    }

    fn expr(
        &mut self,
        module: ModuleId,
        expression: &h::Expr,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Expr, SpecializeError> {
        let template = self
            .expression_types
            .get(&(module, expression.span))
            .ok_or_else(|| error("checked expression type is missing"))?;
        let ty = substitute_type(template, substitution)?;
        let kind = match &expression.kind {
            h::ExprKind::Local(local) => ExprKind::Local(*local),
            h::ExprKind::Global(name) => {
                let key = FunctionKey {
                    name: *name,
                    ty: ty.clone(),
                };
                self.request(key.clone());
                ExprKind::Function(key)
            }
            h::ExprKind::Constructor(constructor) => {
                if matches!(ty, Type::Function(_, _)) {
                    ExprKind::ConstructorFunction(*constructor)
                } else {
                    ExprKind::Construct(*constructor, Vec::new())
                }
            }
            h::ExprKind::Number(_) | h::ExprKind::String(_) => {
                let literal = self.literal_site(module, expression.span)?;
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
            h::ExprKind::Lambda(patterns, body) => ExprKind::Lambda(
                patterns.iter().map(convert_pattern).collect(),
                Box::new(self.expr(module, body, substitution)?),
            ),
            h::ExprKind::Call(head, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.expr(module, argument, substitution))
                    .collect::<Result<Vec<_>, _>>()?;
                match &head.kind {
                    h::ExprKind::Global(name) => {
                        let head_ty = self.expression_type(module, head.span, substitution)?;
                        let key = FunctionKey {
                            name: *name,
                            ty: head_ty,
                        };
                        self.request(key.clone());
                        ExprKind::DirectCall(key, arguments)
                    }
                    h::ExprKind::Constructor(constructor) => {
                        ExprKind::Construct(*constructor, arguments)
                    }
                    _ => ExprKind::Invoke(
                        Box::new(self.expr(module, head, substitution)?),
                        arguments,
                    ),
                }
            }
            h::ExprKind::Member(receiver, _) => {
                let receiver = self.expr(module, receiver, substitution)?;
                if let Some(field) = self.projection_sites.get(&(module, expression.span)) {
                    ExprKind::Project(Box::new(receiver), *field)
                } else {
                    let target = self.method_site(module, expression.span)?;
                    let key = self.method_key(target, &receiver.ty, &[], &ty)?;
                    self.request(key.clone());
                    ExprKind::DirectCall(key, vec![receiver])
                }
            }
            h::ExprKind::Method(receiver, _, arguments) => {
                let target = self.method_site(module, expression.span)?;
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
                self.request(key.clone());
                ExprKind::DirectCall(key, lowered)
            }
            h::ExprKind::Unary(_, value) if matches!(value.kind, h::ExprKind::Number(_)) => {
                let literal = self.literal_site(module, expression.span)?;
                return self.literal(module, expression.span, &literal, &ty);
            }
            h::ExprKind::Unary(_, value) => {
                let target = self.method_site(module, expression.span)?;
                let value = self.expr(module, value, substitution)?;
                let key = self.method_key(target, &value.ty, &[], &ty)?;
                self.request(key.clone());
                ExprKind::DirectCall(key, vec![value])
            }
            h::ExprKind::Binary(operator, left, right) => {
                let target = self.method_site(module, expression.span)?;
                let left = self.expr(module, left, substitution)?;
                let right = self.expr(module, right, substitution)?;
                let key =
                    self.method_key(target, &left.ty, std::slice::from_ref(&right.ty), &ty)?;
                self.request(key.clone());
                let call = ExprKind::DirectCall(key, vec![left, right]);
                if matches!(operator, crate::ast::BinaryOp::NotEqual) {
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

    fn expression_type(
        &self,
        module: ModuleId,
        span: crate::ast::Span,
        substitution: &HashMap<TypeVariable, Type>,
    ) -> Result<Type, SpecializeError> {
        let ty = self
            .expression_types
            .get(&(module, span))
            .ok_or_else(|| error("checked expression type is missing"))?;
        substitute_type(ty, substitution)
    }

    fn method_site(
        &self,
        module: ModuleId,
        span: crate::ast::Span,
    ) -> Result<Symbol, SpecializeError> {
        self.method_sites
            .get(&(module, span))
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
        let scheme = self
            .checked
            .values
            .get(&name)
            .ok_or_else(|| error("method target has no inferred scheme"))?;
        let mut substitution = HashMap::new();
        match_type(&scheme.ty, &ty, &mut substitution)?;
        Ok(FunctionKey { name, ty })
    }

    fn literal_site(
        &self,
        module: ModuleId,
        span: crate::ast::Span,
    ) -> Result<LiteralExpr, SpecializeError> {
        self.literal_sites
            .get(&(module, span))
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

fn convert_pattern(pattern: &h::Pattern) -> Pattern {
    match pattern {
        h::Pattern::Wild => Pattern::Wild,
        h::Pattern::Bind(local) => Pattern::Bind(*local),
        h::Pattern::Constructor(constructor, fields) => {
            Pattern::Constructor(*constructor, fields.iter().map(convert_pattern).collect())
        }
        h::Pattern::Number {
            magnitude,
            negative,
        } => Pattern::Number {
            magnitude: magnitude.clone(),
            negative: *negative,
        },
        h::Pattern::Range(start, end) => Pattern::Range(start.clone(), end.clone()),
        h::Pattern::List(elements, rest) => Pattern::List(
            elements.iter().map(convert_pattern).collect(),
            rest.as_deref().map(convert_pattern).map(Box::new),
        ),
        h::Pattern::Record(fields) => Pattern::Record(
            fields
                .iter()
                .map(|(name, pattern)| (*name, convert_pattern(pattern)))
                .collect(),
        ),
    }
}

fn concrete_scheme(scheme: &InferredScheme) -> Result<Type, SpecializeError> {
    if !scheme.variables.is_empty() {
        return Err(error("entry has an ambiguous polymorphic type"));
    }
    substitute_type(&scheme.ty, &HashMap::new())
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
        InferredType::Variants(constructors) if constructors.is_empty() => Ok(Type::Empty),
        InferredType::Variants(_) => Err(error(
            "nonempty structural variant types are not supported by Barb lowering yet",
        )),
        InferredType::Record(fields) => Ok(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((*name, substitute_type(ty, substitution)?)))
                .collect::<Result<_, SpecializeError>>()?,
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
        (InferredType::Variants(constructors), Type::Empty) if constructors.is_empty() => Ok(()),
        (InferredType::Record(a), Type::Record(b)) if a.len() == b.len() => {
            for ((an, at), (bn, bt)) in a.iter().zip(b) {
                if an != bn {
                    return Err(error("record specialization has different fields"));
                }
                match_type(at, bt, substitution)?;
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
        h::Type::Variants(constructors) if constructors.is_empty() => Ok(Type::Empty),
        h::Type::Variants(_) => Err(error(
            "nonempty structural variant fields are not supported by Barb lowering yet",
        )),
        h::Type::Record(fields) => Ok(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((*name, surface_type(ty, variables)?)))
                .collect::<Result<_, SpecializeError>>()?,
        )),
    }
}

fn error(message: impl Into<String>) -> SpecializeError {
    SpecializeError {
        message: message.into(),
    }
}
