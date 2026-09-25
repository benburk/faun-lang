//! Polymorphic type inference and receiver-directed method resolution.
//!
//! Explicit signatures are universally quantified. Unsigned definitions use
//! Algorithm W over call-graph components, keeping recursive groups
//! monomorphic until the whole group has been checked. Method calls are held
//! until ordinary unification (and numeral defaulting) identifies a receiver.
//! Constraints and bodyless-method derivation are deliberately outside this
//! pass; the bootstrap library supplies concrete implementations instead.

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
    Variants(Vec<(Symbol, Vec<Self>)>),
    Record(Vec<(Symbol, Self)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredScheme {
    pub variables: Vec<TypeVariable>,
    pub ty: InferredType,
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
}

/// A resolved program with what checking learned about it.
#[derive(Clone, Debug)]
pub struct CheckedProgram {
    pub resolved: ResolvedProgram,
    /// The standard identities its literals and patterns were checked against.
    pub prelude: PreludeIds,
    pub types: Types,
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
/// protocol failures.
pub fn type_check(
    resolved: ResolvedProgram,
    prelude: PreludeIds,
) -> Result<CheckedProgram, Diagnostic> {
    let types = validate_effects(&resolved.program, &resolved.symbols).and_then(|()| {
        Checker::new(&resolved.program, &resolved.symbols, &prelude)?.check(&resolved.program)
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
    if !carries.is_some_and(|wrapper| matches!(wrapper.field, h::Type::Record(_))) {
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
                Box::new(InferredType::Variants(Vec::new())),
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
                Box::new(InferredType::Variants(Vec::new())),
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
    Variants(Vec<(Symbol, Vec<Self>)>),
    Record(Vec<(Symbol, Self)>),
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
    member: bool,
    resolved: bool,
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
            Ty::Variants(constructors) => Ty::Variants(
                constructors
                    .iter()
                    .map(|(name, fields)| {
                        (*name, fields.iter().map(|ty| self.resolve(ty)).collect())
                    })
                    .collect(),
            ),
            Ty::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve(ty)))
                    .collect(),
            ),
        }
    }

    fn unify(&mut self, left: &Ty, right: &Ty) -> Result<(), String> {
        let left = self.resolve(left);
        let right = self.resolve(right);
        match (&left, &right) {
            (Ty::Var(a), Ty::Var(b)) if a == b => Ok(()),
            (Ty::Rigid(a), Ty::Rigid(b)) if a == b => Ok(()),
            (Ty::Var(id), other) | (other, Ty::Var(id)) => {
                if contains(other, *id) {
                    Err("a type would contain itself".to_string())
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
            (Ty::Variants(a), Ty::Variants(b)) if a.len() == b.len() => {
                for ((an, af), (bn, bf)) in a.iter().zip(b) {
                    if an != bn || af.len() != bf.len() {
                        return Err("different structural variant types".to_string());
                    }
                    for (a, b) in af.iter().zip(bf) {
                        self.unify(a, b)?;
                    }
                }
                Ok(())
            }
            (Ty::Record(a), Ty::Record(b)) if a.len() == b.len() => {
                for ((an, at), (bn, bt)) in a.iter().zip(b) {
                    if an != bn {
                        return Err("different record fields".to_string());
                    }
                    self.unify(at, bt)?;
                }
                Ok(())
            }
            _ => Err("incompatible types".to_string()),
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        let replacements: HashMap<_, _> = scheme
            .variables
            .iter()
            .map(|variable| (*variable, self.fresh()))
            .collect();
        substitute(&scheme.ty, &replacements)
    }

    fn skolemize(&mut self, scheme: &Scheme) -> Ty {
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
        substitute(&scheme.ty, &replacements)
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
        Ty::Variants(constructors) => constructors
            .iter()
            .flat_map(|(_, fields)| fields)
            .any(|ty| contains(ty, variable)),
        Ty::Record(fields) => fields.iter().any(|(_, ty)| contains(ty, variable)),
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
        Ty::Variants(constructors) => Ty::Variants(
            constructors
                .iter()
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
        ),
        Ty::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, substitute(ty, replacements)))
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
    expression_types: Vec<(ModuleId, super::ast::Span, Ty)>,
    clause_types: Vec<(ModuleId, super::ast::Span, Ty)>,
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
            expression_types: Vec::new(),
            clause_types: Vec::new(),
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
            if let Ty::Record(fields) = &field {
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
        if !signature.constraints.is_empty() {
            return Err(failure(
                module,
                signature.span,
                "`where` constraints are not supported by type inference yet",
            ));
        }
        let mut variables = HashMap::new();
        let parameters = signature
            .parameters
            .iter()
            .map(|ty| self.surface_type(ty, &mut variables))
            .collect();
        let result = self.surface_type(&signature.result, &mut variables);
        let ty = Ty::Function(parameters, Box::new(result));
        let scheme = Scheme {
            variables: free_variables(&ty),
            ty,
        };
        self.values.insert(signature.name, scheme.clone());
        if let Some(owner) = owner {
            self.methods
                .entry(signature.spelling)
                .or_default()
                .push(MethodImpl {
                    owner,
                    target: signature.name,
                    scheme,
                });
        }
        Ok(())
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
            ),
            h::Type::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.surface_type(ty, variables)))
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
            let method_start = self.pending_methods.len();
            let numeral_start = self.pending_numerals.len();
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
            self.finish_pending(method_start, numeral_start)?;
            for name in component {
                let ty = self.infer.resolve(&monotypes[&name]);
                let scheme = self.generalize(&ty, Some(&component_name_set(&monotypes)));
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
                let method_start = self.pending_methods.len();
                let numeral_start = self.pending_numerals.len();
                let ty = self.infer.skolemize(&scheme);
                self.check_clause(module, clause, &ty)?;
                self.finish_pending(method_start, numeral_start)?;
            }
        }
        self.checked.values = self
            .values
            .iter()
            .map(|(&name, scheme)| (name, self.public_scheme(scheme)))
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
        self.checked.clauses = self
            .clause_types
            .iter()
            .map(|(module, span, ty)| ClauseSite {
                module: *module,
                span: *span,
                ty: public_type(&self.infer.resolve(ty)),
            })
            .collect();
        Ok(self.checked)
    }

    fn public_scheme(&self, scheme: &Scheme) -> InferredScheme {
        InferredScheme {
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
            .push((module, clause.span, function.clone()));
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
            let actual = self.expr(module, guard, &mut locals)?;
            self.unify_at(module, guard.span, &actual, &self.bool_type())?;
        }
        for binding in &clause.body.bindings {
            let method_start = self.pending_methods.len();
            let numeral_start = self.pending_numerals.len();
            let value = self.expr(module, &binding.value, &mut locals)?;
            let mut bound = Vec::new();
            collect_pattern_locals(&binding.pattern, &mut bound);
            self.pattern(
                module,
                &binding.pattern,
                &value,
                &mut locals,
                binding.value.span,
            )?;
            self.finish_pending(method_start, numeral_start)?;
            for local in bound {
                let ty = locals[local.index()]
                    .as_ref()
                    .expect("pattern binding installs its local")
                    .ty
                    .clone();
                locals[local.index()] = Some(self.generalize_local(&ty, &locals, local));
            }
        }
        let actual = self.expr(module, &clause.body.result, &mut locals)?;
        self.unify_at(module, clause.body.result.span, &actual, &result)
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
            h::Pattern::Record(fields) => {
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|(name, _)| (*name, self.infer.fresh()))
                    .collect();
                self.unify_at(module, span, expected, &Ty::Record(field_types.clone()))?;
                for ((_, pattern), (_, ty)) in fields.iter().zip(field_types) {
                    self.pattern(module, pattern, &ty, locals, span)?;
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
                Ok(self.infer.instantiate(&scheme))
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
            h::ExprKind::String(parts) => {
                for part in parts {
                    if let h::StringPart::Splice(splice) = part {
                        self.expr(module, splice, locals)?;
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
                Ok(Ty::Record(inferred))
            }
            h::ExprKind::Lambda(patterns, body) => {
                let parameters: Vec<_> = patterns.iter().map(|_| self.infer.fresh()).collect();
                let mut bound = Vec::new();
                for (pattern, parameter) in patterns.iter().zip(&parameters) {
                    collect_pattern_locals(pattern, &mut bound);
                    self.pattern(module, pattern, parameter, locals, expression.span)?;
                }
                let result = self.expr(module, body, locals)?;
                for local in bound {
                    locals[local.index()] = None;
                }
                Ok(Ty::Function(parameters, Box::new(result)))
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
                    Ok(self.bool_type())
                } else {
                    Ok(result)
                }
            }
        }
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
            member,
            resolved: false,
        });
        result
    }

    fn finish_pending(
        &mut self,
        method_start: usize,
        numeral_start: usize,
    ) -> Result<(), CheckError> {
        self.settle_methods(method_start, false)?;
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved {
                continue;
            }
            if matches!(self.infer.resolve(&numeral.ty), Ty::Var(_)) {
                let default = if numeral.negative {
                    Ty::Named(self.prelude.int, Vec::new())
                } else {
                    Ty::Named(self.prelude.nat, Vec::new())
                };
                self.unify_at(numeral.module, numeral.span, &numeral.ty, &default)?;
            }
        }
        self.settle_methods(method_start, true)?;
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved {
                continue;
            }
            let ty = self.infer.resolve(&numeral.ty);
            let (kind, symbol) = match ty {
                Ty::Named(name, ref arguments)
                    if name == self.prelude.nat && arguments.is_empty() =>
                {
                    (NumeralType::Nat, self.prelude.nat)
                }
                Ty::Named(name, ref arguments)
                    if name == self.prelude.int && arguments.is_empty() =>
                {
                    (NumeralType::Int, self.prelude.int)
                }
                _ => {
                    return Err(failure(
                        numeral.module,
                        numeral.span,
                        "a numeral must infer as Nat or Int",
                    ));
                }
            };
            let value =
                blessed::numeral(numeral.magnitude, numeral.negative, kind, self.prelude)
                    .map_err(|error| failure(numeral.module, numeral.span, error.to_string()))?;
            self.checked.literals.push(LiteralSite {
                module: numeral.module,
                span: numeral.span,
                ty: symbol,
                value,
            });
            self.pending_numerals[index].resolved = true;
        }
        Ok(())
    }

    fn settle_methods(&mut self, start: usize, final_pass: bool) -> Result<(), CheckError> {
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
                if final_pass {
                    let pending = &self.pending_methods[next[0]];
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
        if !pending.member || !pending.arguments.is_empty() {
            return Vec::new();
        }
        let receiver = self.infer.resolve(&pending.receiver);
        if let Ty::Record(fields) = &receiver {
            return fields
                .iter()
                .find(|(name, _)| *name == pending.name)
                .map(|(_, field)| Scheme {
                    variables: Vec::new(),
                    ty: Ty::Function(vec![receiver.clone()], Box::new(field.clone())),
                })
                .into_iter()
                .collect();
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

    /// The visible methods named at `pending` that its receiver could have.
    fn owned_methods(&self, pending: &PendingMethod) -> Vec<MethodImpl> {
        let Some(implementations) = self.methods.get(&pending.name) else {
            return Vec::new();
        };
        let receiver = self.infer.resolve(&pending.receiver);
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
        apply_signature(
            &mut self.infer,
            pending,
            &implementation.scheme,
            self.symbols,
        )
        .map_err(|message| failure(pending.module, pending.span, message))?;
        self.checked.methods.push(MethodSite {
            module: pending.module,
            span: pending.span,
            target: implementation.target,
        });
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
            failure(
                module,
                span,
                format!(
                    "type mismatch: {} and {} ({reason})",
                    show(&self.infer.resolve(actual), self.symbols),
                    show(&self.infer.resolve(expected), self.symbols)
                ),
            )
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
) -> Result<(), String> {
    let instantiated = infer.instantiate(scheme);
    let Ty::Function(parameters, result) = instantiated else {
        return Err("a method declaration is not a function".to_string());
    };
    if parameters.len() != pending.arguments.len() + 1 {
        return Err(format!(
            "`{}` takes {} arguments, but {} were given",
            symbols.text(pending.name),
            parameters.len() - 1,
            pending.arguments.len()
        ));
    }
    let given = std::iter::once(&pending.receiver).chain(&pending.arguments);
    for (at, (argument, parameter)) in given.zip(&parameters).enumerate() {
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
    infer.unify(&pending.result, &result)
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
        Ty::Variants(constructors) => InferredType::Variants(
            constructors
                .iter()
                .map(|(name, fields)| (*name, fields.iter().map(public_type).collect()))
                .collect(),
        ),
        Ty::Record(fields) => InferredType::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, public_type(ty)))
                .collect(),
        ),
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
            Ty::Variants(constructors) => {
                for (_, fields) in constructors {
                    for ty in fields {
                        collect(ty, output);
                    }
                }
            }
            Ty::Record(fields) => {
                for (_, ty) in fields {
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
        h::ExprKind::Lambda(_, body) | h::ExprKind::Unary(_, body) => expr_globals(body, output),
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
        h::ExprKind::Local(_) | h::ExprKind::Constructor(_) | h::ExprKind::Number(_) => {}
    }
}

fn collect_pattern_locals(pattern: &h::Pattern, output: &mut Vec<h::LocalId>) {
    match pattern {
        h::Pattern::Bind(local) => output.push(*local),
        h::Pattern::Constructor(_, fields) | h::Pattern::List(fields, None) => {
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
        h::Pattern::Record(fields) => {
            for (_, pattern) in fields {
                collect_pattern_locals(pattern, output);
            }
        }
        h::Pattern::Wild | h::Pattern::Number { .. } | h::Pattern::Range(..) => {}
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
        Ty::Variants(variants) => format!(
            "[{}]",
            variants
                .iter()
                .map(|(name, fields)| if fields.is_empty() {
                    spelled(*name, symbols).to_owned()
                } else {
                    let fields: Vec<_> = fields.iter().map(|ty| show(ty, symbols)).collect();
                    format!("{}({})", spelled(*name, symbols), fields.join(" "))
                })
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Ty::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", symbols.text(*name), show(ty, symbols)))
                .collect::<Vec<_>>()
                .join(" ")
        ),
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
            self.write("bool.fn", "exports {Bool.*}\nBool : [False True].(not : Bool -> Bool not(False) -> True not(True) -> False)\n");
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
            self.write("str.fn", "exports {Str}\nStr : List(U8)\n");
            let standard = self.write(
                "standard.fn",
                "package {}\nimport bool {Bool.*}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport str {Str}\nexports {Bool.* Nat.* Int.* U8 List.* Str}\n",
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

    #[test]
    fn local_function_bindings_are_generalized() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "id : a -> a\nid(x) -> x\nlocal : Int\nlocal() ->\n  f = id\n  natural = f(1)\n  f(-1)\n",
        );
        type_check(resolved, prelude).unwrap();
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

    #[test]
    fn an_ambiguous_unconstrained_method_is_rejected() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "Flip : [Off On].(not : Flip -> Flip not(Off) -> On not(On) -> Off)\nbad(x) -> x.not()\n",
        );
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(failure.message.contains("ambiguous") || failure.message.contains("compatible"));
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

    /// A method that exists, called with an argument it does not take, says
    /// which argument and both types, rather than that there is no method.
    #[test]
    fn a_method_given_the_wrong_argument_names_it() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad() -> Zero.add(True)\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert_eq!(
            failure.message,
            "argument 1 of `add` should be Nat, but is Bool"
        );
    }

    #[test]
    fn a_negative_nat_is_rejected() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad() -> -1\n");
        let failure = type_check(resolved, prelude).unwrap_err();
        assert!(failure.message.contains("negative numeral"));
    }
}
