//! Defunctionalize concrete frontend terms and emit Barb declarations and bodies.

#![allow(clippy::too_many_lines)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use faun::barb::{self, Atom, Builder, CtorId, FnId, TypeId};
use num_traits::ToPrimitive;

use crate::blessed::PreludeIds;
use crate::hir::LocalId;
use crate::resolve::ResolvedProgram;
use crate::specialize::{self, Expr, ExprKind, FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowerError {
    pub message: String,
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LowerError {}

impl From<specialize::SpecializeError> for LowerError {
    fn from(error: specialize::SpecializeError) -> Self {
        Self {
            message: error.message,
        }
    }
}

/// Specialize the reachable program, defunctionalize function values, and emit Barb.
///
/// `entry` must name a monomorphic, parameterless function. The returned
/// program contains only concrete types and saturated first-order calls.
///
/// # Errors
///
/// Reports ambiguous specialization, unsupported structural types or ranges,
/// missing declarations, non-exhaustive clauses, and invalid literal shapes.
pub fn program(
    resolved: &ResolvedProgram,
    checked: &crate::check::CheckedProgram,
    prelude: &PreludeIds,
    entry: Symbol,
) -> Result<barb::Program, LowerError> {
    let specialized = specialize::program(resolved, checked, prelude, entry)?;
    Lowerer::new(resolved, prelude, specialized)?.lower()
}

/// Select a uniquely named checked value and lower it as the entry.
///
/// # Errors
///
/// Reports a missing or ambiguous source-level name in addition to the errors
/// from [`program`].
pub fn named_program(
    resolved: &ResolvedProgram,
    checked: &crate::check::CheckedProgram,
    prelude: &PreludeIds,
    entry: &str,
) -> Result<barb::Program, LowerError> {
    let suffix = format!("$${entry}");
    let mut candidates = checked
        .values
        .keys()
        .copied()
        .filter(|symbol| resolved.symbols.text(*symbol).ends_with(&suffix));
    let selected = candidates
        .next()
        .ok_or_else(|| error(format!("no checked value is named `{entry}`")))?;
    if candidates.next().is_some() {
        return Err(error(format!(
            "more than one checked value is named `{entry}`"
        )));
    }
    program(resolved, checked, prelude, selected)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ClosureKey {
    Global(FunctionKey),
    Constructor(Symbol, Type),
    Lambda(ModuleId, crate::ast::Span, Type),
}

#[derive(Clone, Debug)]
struct ClosureVariant {
    key: ClosureKey,
    captures: Vec<(LocalId, Type)>,
    lambda: Option<(Vec<Pattern>, Expr)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Value(u32);

#[derive(Clone, Debug)]
struct Subject {
    value: Value,
    ty: Type,
}

#[derive(Clone, Debug)]
struct Row {
    patterns: Vec<Pattern>,
    guard: Option<Expr>,
    body: specialize::Body,
    locals: HashMap<LocalId, Value>,
}

#[derive(Clone, Debug)]
enum Decision {
    Body {
        body: specialize::Body,
        locals: HashMap<LocalId, Value>,
    },
    Match {
        subject: Value,
        owner: Type,
        arms: Vec<DecisionArm>,
    },
    Guard {
        condition: Expr,
        locals: HashMap<LocalId, Value>,
        false_constructor: Symbol,
        true_constructor: Symbol,
        otherwise: Box<Self>,
        answer: Box<Self>,
    },
}

#[derive(Clone, Debug)]
struct DecisionArm {
    constructor: Symbol,
    fields: Vec<Value>,
    decision: Box<Decision>,
}

struct Lowerer<'a> {
    resolved: &'a ResolvedProgram,
    prelude: &'a PreludeIds,
    specialized: specialize::Program,
    closures: BTreeMap<Type, Vec<ClosureVariant>>,
    invoked: BTreeSet<Type>,
    types: BTreeSet<Type>,
    type_ids: HashMap<Type, TypeId>,
    constructor_ids: HashMap<(Symbol, Type), CtorId>,
    closure_constructor_ids: HashMap<ClosureKey, CtorId>,
    function_ids: HashMap<FunctionKey, FnId>,
    apply_ids: HashMap<Type, FnId>,
    output: barb::Program,
}

impl<'a> Lowerer<'a> {
    fn new(
        resolved: &'a ResolvedProgram,
        prelude: &'a PreludeIds,
        specialized: specialize::Program,
    ) -> Result<Self, LowerError> {
        let mut lowerer = Self {
            resolved,
            prelude,
            specialized,
            closures: BTreeMap::new(),
            invoked: BTreeSet::new(),
            types: BTreeSet::new(),
            type_ids: HashMap::new(),
            constructor_ids: HashMap::new(),
            closure_constructor_ids: HashMap::new(),
            function_ids: HashMap::new(),
            apply_ids: HashMap::new(),
            output: barb::Program::default(),
        };
        lowerer.discover()?;
        Ok(lowerer)
    }

    fn lower(mut self) -> Result<barb::Program, LowerError> {
        self.declare_types();
        self.define_types()?;
        self.declare_functions()?;
        self.define_functions()?;
        self.define_apply_functions()?;
        let entry = self.function_ids[&self.specialized.entry];
        self.output.set_entry(entry);
        barb::validate(&self.output).map_err(error)?;
        Ok(self.output)
    }

    fn discover(&mut self) -> Result<(), LowerError> {
        let functions = self.specialized.functions.clone();
        for function in &functions {
            let (parameters, result) = function
                .key
                .ty
                .function()
                .expect("specialized globals have function types");
            for parameter in parameters {
                self.collect_type(parameter)?;
            }
            self.collect_type(result)?;
            for clause in &function.clauses {
                if let Some(guard) = &clause.guard {
                    self.collect_expr(guard)?;
                }
                self.collect_body(&clause.body)?;
            }
        }
        loop {
            let before = self.types.len();
            let types: Vec<_> = self.types.iter().cloned().collect();
            for ty in types {
                if let Type::Named(_, _) = &ty {
                    for (_, fields) in self.constructors_of(&ty)? {
                        for field in fields {
                            self.collect_type(&field)?;
                        }
                    }
                }
            }
            let variants: Vec<_> = self
                .closures
                .values()
                .flat_map(|variants| variants.iter())
                .cloned()
                .collect();
            for variant in variants {
                for (_, ty) in variant.captures {
                    self.collect_type(&ty)?;
                }
            }
            if self.types.len() == before {
                return Ok(());
            }
        }
    }

    fn collect_body(&mut self, body: &specialize::Body) -> Result<(), LowerError> {
        for binding in &body.bindings {
            self.collect_expr(&binding.value)?;
            if !matches!(binding.pattern, Pattern::Wild | Pattern::Bind(_)) {
                return Err(error(
                    "refutable local bindings are not supported by Barb lowering yet",
                ));
            }
        }
        self.collect_expr(&body.result)
    }

    fn collect_expr(&mut self, expression: &Expr) -> Result<(), LowerError> {
        self.collect_type(&expression.ty)?;
        match &expression.kind {
            ExprKind::Local(_) | ExprKind::Natural(_) => {}
            ExprKind::Function(key) => {
                self.add_closure(
                    expression.ty.clone(),
                    ClosureVariant {
                        key: ClosureKey::Global(key.clone()),
                        captures: Vec::new(),
                        lambda: None,
                    },
                );
            }
            ExprKind::ConstructorFunction(constructor) => {
                self.add_closure(
                    expression.ty.clone(),
                    ClosureVariant {
                        key: ClosureKey::Constructor(*constructor, expression.ty.clone()),
                        captures: Vec::new(),
                        lambda: None,
                    },
                );
            }
            ExprKind::Construct(_, fields) | ExprKind::DirectCall(_, fields) => {
                for field in fields {
                    self.collect_expr(field)?;
                }
            }
            ExprKind::Invoke(head, arguments) => {
                self.invoked.insert(head.ty.clone());
                self.collect_expr(head)?;
                for argument in arguments {
                    self.collect_expr(argument)?;
                }
            }
            ExprKind::Lambda(patterns, body) => {
                let captures = captures(patterns, body);
                let variant = ClosureVariant {
                    key: ClosureKey::Lambda(
                        expression.module,
                        expression.span,
                        expression.ty.clone(),
                    ),
                    captures,
                    lambda: Some((patterns.clone(), (**body).clone())),
                };
                self.add_closure(expression.ty.clone(), variant);
                self.collect_expr(body)?;
            }
        }
        Ok(())
    }

    fn add_closure(&mut self, ty: Type, variant: ClosureVariant) {
        let variants = self.closures.entry(ty).or_default();
        if !variants.iter().any(|held| held.key == variant.key) {
            variants.push(variant);
        }
    }

    fn collect_type(&mut self, ty: &Type) -> Result<(), LowerError> {
        if !self.types.insert(ty.clone()) {
            return Ok(());
        }
        match ty {
            Type::Named(name, _) => {
                if !self.specialized.data.contains_key(name) {
                    return Err(error(format!(
                        "type `{}` has no data declaration",
                        self.resolved.symbols.text(*name)
                    )));
                }
            }
            Type::Function(parameters, result) => {
                for parameter in parameters {
                    self.collect_type(parameter)?;
                }
                self.collect_type(result)?;
            }
        }
        Ok(())
    }

    fn declare_types(&mut self) {
        for ty in &self.types {
            let name = type_name(ty, &self.resolved.symbols);
            let id = self.output.declare_type(&name);
            self.type_ids.insert(ty.clone(), id);
        }
    }

    fn define_types(&mut self) -> Result<(), LowerError> {
        let types: Vec<_> = self.types.iter().cloned().collect();
        for ty in types {
            let id = self.type_ids[&ty];
            match &ty {
                Type::Named(_, _) => {
                    let constructors = self.constructors_of(&ty)?;
                    let held: Vec<_> = constructors
                        .iter()
                        .map(|(name, fields)| {
                            (
                                self.resolved.symbols.text(*name).to_string(),
                                fields
                                    .iter()
                                    .map(|field| self.type_ids[field])
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .collect();
                    let borrowed: Vec<_> = held
                        .iter()
                        .map(|(name, fields)| (name.as_str(), fields.as_slice()))
                        .collect();
                    self.output.define_type(id, &borrowed);
                    for (tag, (name, _)) in constructors.iter().enumerate() {
                        let tag = u32::try_from(tag).expect("a sane constructor count");
                        self.constructor_ids
                            .insert((*name, ty.clone()), self.output.ctor_at(id, tag));
                    }
                }
                Type::Function(_, _) => {
                    let variants = self.closures.get(&ty).cloned().unwrap_or_default();
                    let held: Vec<_> = variants
                        .iter()
                        .map(|variant| {
                            (
                                closure_name(&variant.key, &self.resolved.symbols),
                                variant
                                    .captures
                                    .iter()
                                    .map(|(_, ty)| self.type_ids[ty])
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .collect();
                    let borrowed: Vec<_> = held
                        .iter()
                        .map(|(name, fields)| (name.as_str(), fields.as_slice()))
                        .collect();
                    self.output.define_type(id, &borrowed);
                    for (tag, variant) in variants.iter().enumerate() {
                        let tag = u32::try_from(tag).expect("a sane closure count");
                        self.closure_constructor_ids
                            .insert(variant.key.clone(), self.output.ctor_at(id, tag));
                    }
                }
            }
        }
        let nat = Type::Named(self.prelude.nat, Vec::new());
        if let Some(&nat) = self.type_ids.get(&nat) {
            self.output
                .intern_number(nat, 0)
                .map_err(|cause| error(cause.to_string()))?;
        }
        Ok(())
    }

    fn declare_functions(&mut self) -> Result<(), LowerError> {
        for function in &self.specialized.functions {
            let (parameters, result) = function
                .key
                .ty
                .function()
                .ok_or_else(|| error("specialized global is not a function"))?;
            let parameters: Vec<_> = parameters
                .iter()
                .map(|parameter| self.type_ids[parameter])
                .collect();
            let result = self.type_ids[result];
            let name = function_name(&function.key, &self.resolved.symbols);
            let id = self.output.declare(&name, &parameters, result);
            if let Some(provider) = function.provider {
                self.output
                    .answered_by(id, self.resolved.symbols.text(provider));
            }
            self.function_ids.insert(function.key.clone(), id);
        }
        for ty in &self.invoked {
            let (parameters, result) = ty
                .function()
                .ok_or_else(|| error("invoked value is not a function"))?;
            if self.closures.get(ty).is_none_or(Vec::is_empty) {
                return Err(error("an invoked function type has no reachable closures"));
            }
            let mut signature = Vec::with_capacity(parameters.len() + 1);
            signature.push(self.type_ids[ty]);
            signature.extend(parameters.iter().map(|parameter| self.type_ids[parameter]));
            let name = format!("apply$${}", type_name(ty, &self.resolved.symbols));
            let id = self
                .output
                .declare(&name, &signature, self.type_ids[result]);
            self.apply_ids.insert(ty.clone(), id);
        }
        Ok(())
    }

    fn define_functions(&mut self) -> Result<(), LowerError> {
        let functions = std::mem::take(&mut self.specialized.functions);
        for function in functions {
            if function.provider.is_some() {
                continue;
            }
            let (parameters, _) = function
                .key
                .ty
                .function()
                .expect("specialized global is a function");
            let subjects: Vec<_> = parameters
                .iter()
                .enumerate()
                .map(|(index, ty)| Subject {
                    value: Value(u32::try_from(index).expect("a sane arity")),
                    ty: ty.clone(),
                })
                .collect();
            let rows: Vec<Row> = function
                .clauses
                .into_iter()
                .map(|clause| Row {
                    patterns: clause.patterns,
                    guard: clause.guard,
                    body: clause.body,
                    locals: HashMap::new(),
                })
                .collect();
            let mut next = u32::try_from(subjects.len()).expect("a sane arity");
            let decision = self.plan(&rows, &subjects, &mut next)?;
            let function_id = self.function_ids[&function.key];
            let context = EmitContext {
                type_ids: &self.type_ids,
                constructor_ids: &self.constructor_ids,
                closure_constructor_ids: &self.closure_constructor_ids,
                function_ids: &self.function_ids,
                apply_ids: &self.apply_ids,
                closures: &self.closures,
                prelude: self.prelude,
            };
            self.output.define(function_id, |builder, parameters| {
                let values = parameters
                    .iter()
                    .enumerate()
                    .map(|(index, atom)| {
                        (Value(u32::try_from(index).expect("a sane arity")), *atom)
                    })
                    .collect();
                emit_decision(&context, builder, &decision, &values)
            });
        }
        Ok(())
    }

    fn define_apply_functions(&mut self) -> Result<(), LowerError> {
        let invoked: Vec<_> = self.invoked.iter().cloned().collect();
        for ty in invoked {
            let variants = self.closures[&ty].clone();
            let apply = self.apply_ids[&ty];
            let closure_type = self.type_ids[&ty];
            let context = EmitContext {
                type_ids: &self.type_ids,
                constructor_ids: &self.constructor_ids,
                closure_constructor_ids: &self.closure_constructor_ids,
                function_ids: &self.function_ids,
                apply_ids: &self.apply_ids,
                closures: &self.closures,
                prelude: self.prelude,
            };
            let mut lambda_plans = HashMap::new();
            for variant in &variants {
                let Some((patterns, body)) = &variant.lambda else {
                    continue;
                };
                let Type::Function(parameters, _) = &ty else {
                    unreachable!()
                };
                let captured = u32::try_from(variant.captures.len()).expect("sane captures");
                let subjects: Vec<_> = parameters
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| Subject {
                        value: Value(captured + u32::try_from(index).expect("a sane arity")),
                        ty: ty.clone(),
                    })
                    .collect();
                let locals = variant
                    .captures
                    .iter()
                    .enumerate()
                    .map(|(index, (local, _))| {
                        (*local, Value(u32::try_from(index).expect("sane captures")))
                    })
                    .collect();
                let row = Row {
                    patterns: patterns.clone(),
                    guard: None,
                    body: specialize::Body {
                        bindings: Vec::new(),
                        result: body.clone(),
                    },
                    locals,
                };
                let mut next =
                    captured + u32::try_from(parameters.len()).expect("a sane closure arity");
                lambda_plans.insert(
                    variant.key.clone(),
                    self.plan(&[row], &subjects, &mut next)?,
                );
            }
            self.output.define(apply, |builder, parameters| {
                let closure = parameters[0];
                let arguments = &parameters[1..];
                builder.match_(closure, closure_type, |builder, constructor, fields| {
                    let variant = variants
                        .iter()
                        .find(|variant| {
                            context.closure_constructor_ids[&variant.key] == constructor
                        })
                        .expect("each closure constructor has a variant");
                    match &variant.key {
                        ClosureKey::Global(key) => {
                            builder.call(context.function_ids[key], arguments)
                        }
                        ClosureKey::Constructor(source, function_type) => {
                            let Type::Function(_, result) = function_type else {
                                unreachable!()
                            };
                            builder.con(
                                context.constructor_ids[&(*source, (**result).clone())],
                                arguments,
                            )
                        }
                        ClosureKey::Lambda(_, _, _) => {
                            let plan = &lambda_plans[&variant.key];
                            let mut values: HashMap<_, _> = fields
                                .iter()
                                .enumerate()
                                .map(|(index, atom)| {
                                    (Value(u32::try_from(index).expect("sane captures")), *atom)
                                })
                                .collect();
                            let offset = u32::try_from(fields.len()).expect("sane captures");
                            for (index, atom) in arguments.iter().enumerate() {
                                values.insert(
                                    Value(offset + u32::try_from(index).expect("a sane arity")),
                                    *atom,
                                );
                            }
                            emit_decision(&context, builder, plan, &values)
                        }
                    }
                })
            });
        }
        Ok(())
    }

    fn plan(
        &self,
        rows: &[Row],
        subjects: &[Subject],
        next: &mut u32,
    ) -> Result<Decision, LowerError> {
        if rows.is_empty() {
            return Err(error("function clauses are not exhaustive"));
        }
        let mut first = rows[0].clone();
        if first.patterns.iter().all(irrefutable) {
            for (pattern, subject) in first.patterns.iter().zip(subjects) {
                if let Pattern::Bind(local) = pattern {
                    first.locals.insert(*local, subject.value);
                }
            }
            let answer = Decision::Body {
                body: first.body,
                locals: first.locals.clone(),
            };
            let Some(condition) = first.guard else {
                return Ok(answer);
            };
            let booleans = self.constructors_of(&Type::Named(self.prelude.bool_, Vec::new()))?;
            if booleans.len() != 2
                || booleans.iter().any(|(_, fields)| !fields.is_empty())
                || !booleans
                    .iter()
                    .any(|(name, _)| *name == self.prelude.bool_false)
                || !booleans
                    .iter()
                    .any(|(name, _)| *name == self.prelude.bool_true)
            {
                return Err(error(
                    "Bool must have fieldless False and True constructors",
                ));
            }
            return Ok(Decision::Guard {
                condition,
                locals: first.locals,
                false_constructor: self.prelude.bool_false,
                true_constructor: self.prelude.bool_true,
                otherwise: Box::new(self.plan(&rows[1..], subjects, next)?),
                answer: Box::new(answer),
            });
        }
        let column = rows
            .iter()
            .flat_map(|row| row.patterns.iter().enumerate())
            .find(|(_, pattern)| !irrefutable(pattern))
            .map(|(column, _)| column)
            .expect("a refutable pattern exists");
        let subject = &subjects[column];
        let constructors = self.constructors_of(&subject.ty)?;
        let mut arms = Vec::with_capacity(constructors.len());
        for (constructor, field_types) in constructors {
            let fields: Vec<_> = field_types
                .iter()
                .map(|_| {
                    let value = Value(*next);
                    *next = next.checked_add(1).expect("fewer than 2^32 plan values");
                    value
                })
                .collect();
            let mut specialized = Vec::new();
            for mut row in rows.iter().cloned() {
                let normalized =
                    self.normalize_pattern(row.patterns[column].clone(), &subject.ty)?;
                let replacement = match normalized {
                    Pattern::Wild => vec![Pattern::Wild; fields.len()],
                    Pattern::Bind(local) => {
                        row.locals.insert(local, subject.value);
                        vec![Pattern::Wild; fields.len()]
                    }
                    Pattern::Constructor(found, patterns) if found == constructor => patterns,
                    Pattern::Constructor(_, _) => continue,
                    _ => unreachable!("patterns normalize to wildcard, bind, or constructor"),
                };
                if replacement.len() != fields.len() {
                    return Err(error("constructor pattern has the wrong field count"));
                }
                row.patterns.splice(column..=column, replacement);
                specialized.push(row);
            }
            let mut arm_subjects = subjects.to_vec();
            arm_subjects.splice(
                column..=column,
                fields
                    .iter()
                    .copied()
                    .zip(field_types)
                    .map(|(value, ty)| Subject { value, ty }),
            );
            arms.push(DecisionArm {
                constructor,
                fields,
                decision: Box::new(self.plan(&specialized, &arm_subjects, next)?),
            });
        }
        Ok(Decision::Match {
            subject: subject.value,
            owner: subject.ty.clone(),
            arms,
        })
    }

    fn normalize_pattern(&self, pattern: Pattern, expected: &Type) -> Result<Pattern, LowerError> {
        match pattern {
            Pattern::Number {
                magnitude,
                negative,
            } => self.number_pattern(magnitude, negative, expected),
            Pattern::Range(start, end) => Err(error(format!(
                "range pattern {start}..{end} is not supported by Barb lowering"
            ))),
            Pattern::List(elements, rest) => {
                let mut tail = rest.map_or(
                    Pattern::Constructor(self.prelude.list_nil, Vec::new()),
                    |rest| *rest,
                );
                for element in elements.into_iter().rev() {
                    tail = Pattern::Constructor(self.prelude.list_cons, vec![element, tail]);
                }
                Ok(tail)
            }
            other => Ok(other),
        }
    }

    fn number_pattern(
        &self,
        magnitude: num_bigint::BigUint,
        negative: bool,
        expected: &Type,
    ) -> Result<Pattern, LowerError> {
        let Type::Named(name, arguments) = expected else {
            return Err(error("numeric pattern does not have a named type"));
        };
        if !arguments.is_empty() {
            return Err(error("numeric pattern type unexpectedly has arguments"));
        }
        if *name == self.prelude.nat {
            if negative {
                return Err(error("a negative pattern cannot match Nat"));
            }
            return self.natural_pattern(&magnitude);
        }
        if *name == self.prelude.int {
            let constructors = &self.specialized.data[name].constructors;
            if constructors.len() != 2 {
                return Err(error("Int must have positive and negative constructors"));
            }
            if negative && magnitude != num_bigint::BigUint::ZERO {
                let predecessor = magnitude - 1u8;
                return Ok(Pattern::Constructor(
                    constructors[1].name,
                    vec![self.natural_pattern(&predecessor)?],
                ));
            }
            return Ok(Pattern::Constructor(
                constructors[0].name,
                vec![self.natural_pattern(&magnitude)?],
            ));
        }
        Err(error("a numeric pattern must infer as Nat or Int"))
    }

    fn natural_pattern(&self, magnitude: &num_bigint::BigUint) -> Result<Pattern, LowerError> {
        const MAX_PATTERN_MAGNITUDE: usize = 1_024;
        let count = magnitude
            .to_usize()
            .filter(|count| *count <= MAX_PATTERN_MAGNITUDE)
            .ok_or_else(|| error("numeric pattern is too large to lower structurally"))?;
        let constructors = &self.specialized.data[&self.prelude.nat].constructors;
        if constructors.len() != 2
            || !constructors[0].fields.is_empty()
            || constructors[1].fields.len() != 1
        {
            return Err(error("Nat does not have the required zero/successor shape"));
        }
        let mut pattern = Pattern::Constructor(constructors[0].name, Vec::new());
        for _ in 0..count {
            pattern = Pattern::Constructor(constructors[1].name, vec![pattern]);
        }
        Ok(pattern)
    }

    fn constructors_of(&self, ty: &Type) -> Result<Vec<(Symbol, Vec<Type>)>, LowerError> {
        let Type::Named(name, arguments) = ty else {
            return Err(error("pattern matching requires a named data type"));
        };
        let data = self
            .specialized
            .data
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
                    .map(|field| specialize::surface_type(field, &variables).map_err(Into::into))
                    .collect::<Result<_, LowerError>>()?,
            ));
        }
        if let Some(wrapper) = &data.wrapper {
            constructors.push((
                wrapper.constructor,
                vec![specialize::surface_type(&wrapper.field, &variables)?],
            ));
        }
        Ok(constructors)
    }
}

struct EmitContext<'a> {
    type_ids: &'a HashMap<Type, TypeId>,
    constructor_ids: &'a HashMap<(Symbol, Type), CtorId>,
    closure_constructor_ids: &'a HashMap<ClosureKey, CtorId>,
    function_ids: &'a HashMap<FunctionKey, FnId>,
    apply_ids: &'a HashMap<Type, FnId>,
    closures: &'a BTreeMap<Type, Vec<ClosureVariant>>,
    prelude: &'a PreludeIds,
}

fn emit_decision(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    decision: &Decision,
    values: &HashMap<Value, Atom>,
) -> Atom {
    match decision {
        Decision::Body { body, locals } => {
            let locals = locals
                .iter()
                .map(|(local, value)| (*local, values[value]))
                .collect();
            emit_body(context, builder, body, locals)
        }
        Decision::Match {
            subject,
            owner,
            arms,
        } => {
            let owner_id = context.type_ids[owner];
            builder.match_(values[subject], owner_id, |builder, constructor, fields| {
                let arm = arms
                    .iter()
                    .find(|arm| {
                        context.constructor_ids[&(arm.constructor, owner.clone())] == constructor
                    })
                    .expect("the plan has one arm per constructor");
                let mut nested = values.clone();
                for (value, atom) in arm.fields.iter().zip(fields) {
                    nested.insert(*value, *atom);
                }
                emit_decision(context, builder, &arm.decision, &nested)
            })
        }
        Decision::Guard {
            condition,
            locals,
            false_constructor,
            true_constructor,
            otherwise,
            answer,
        } => {
            let locals: HashMap<_, _> = locals
                .iter()
                .map(|(local, value)| (*local, values[value]))
                .collect();
            let condition = emit_expr(context, builder, condition, &locals);
            let bool_ty = Type::Named(context.prelude.bool_, Vec::new());
            let bool_id = context.type_ids[&bool_ty];
            let false_id = context.constructor_ids[&(*false_constructor, bool_ty.clone())];
            let true_id = context.constructor_ids[&(*true_constructor, bool_ty)];
            builder.match_(condition, bool_id, |builder, constructor, _| {
                if constructor == false_id {
                    emit_decision(context, builder, otherwise, values)
                } else {
                    assert_eq!(constructor, true_id, "Bool has exactly two constructors");
                    emit_decision(context, builder, answer, values)
                }
            })
        }
    }
}

fn emit_body(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    body: &specialize::Body,
    mut locals: HashMap<LocalId, Atom>,
) -> Atom {
    for binding in &body.bindings {
        let value = emit_expr(context, builder, &binding.value, &locals);
        match binding.pattern {
            Pattern::Wild => {}
            Pattern::Bind(local) => {
                locals.insert(local, value);
            }
            _ => unreachable!("refutable bindings were rejected before emission"),
        }
    }
    emit_expr(context, builder, &body.result, &locals)
}

fn emit_expr(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    expression: &Expr,
    locals: &HashMap<LocalId, Atom>,
) -> Atom {
    match &expression.kind {
        ExprKind::Local(local) => locals[local],
        ExprKind::Natural(magnitude) => {
            let nat = context.type_ids[&Type::Named(context.prelude.nat, Vec::new())];
            let constant = builder
                .natural(nat, magnitude)
                .expect("the Nat shape was validated before emission");
            builder.known(constant)
        }
        ExprKind::Function(key) => builder.con(
            context.closure_constructor_ids[&ClosureKey::Global(key.clone())],
            &[],
        ),
        ExprKind::ConstructorFunction(constructor) => builder.con(
            context.closure_constructor_ids
                [&ClosureKey::Constructor(*constructor, expression.ty.clone())],
            &[],
        ),
        ExprKind::Lambda(_, _) => {
            let key = ClosureKey::Lambda(expression.module, expression.span, expression.ty.clone());
            let captures = captures_for_key(context, &key, locals);
            builder.con(context.closure_constructor_ids[&key], &captures)
        }
        ExprKind::Construct(constructor, fields) => {
            let fields = fields
                .iter()
                .map(|field| emit_expr(context, builder, field, locals))
                .collect::<Vec<_>>();
            builder.con(
                context.constructor_ids[&(*constructor, expression.ty.clone())],
                &fields,
            )
        }
        ExprKind::DirectCall(key, arguments) => {
            let arguments = arguments
                .iter()
                .map(|argument| emit_expr(context, builder, argument, locals))
                .collect::<Vec<_>>();
            builder.call(context.function_ids[key], &arguments)
        }
        ExprKind::Invoke(head, arguments) => {
            let mut lowered = Vec::with_capacity(arguments.len() + 1);
            lowered.push(emit_expr(context, builder, head, locals));
            for argument in arguments {
                lowered.push(emit_expr(context, builder, argument, locals));
            }
            builder.call(context.apply_ids[&head.ty], &lowered)
        }
    }
}

fn captures_for_key(
    context: &EmitContext<'_>,
    key: &ClosureKey,
    locals: &HashMap<LocalId, Atom>,
) -> Vec<Atom> {
    let ClosureKey::Lambda(_, _, ty) = key else {
        return Vec::new();
    };
    let variant = context
        .closures
        .get(ty)
        .and_then(|variants| variants.iter().find(|variant| &variant.key == key))
        .expect("each emitted lambda has a discovered closure variant");
    variant
        .captures
        .iter()
        .map(|(local, _)| locals[local])
        .collect()
}

fn captures(patterns: &[Pattern], body: &Expr) -> Vec<(LocalId, Type)> {
    let mut bound = HashSet::new();
    for pattern in patterns {
        pattern_locals(pattern, &mut bound);
    }
    let mut found = BTreeMap::new();
    free_locals(body, &bound, &mut found);
    found.into_iter().collect()
}

fn free_locals(expression: &Expr, bound: &HashSet<LocalId>, found: &mut BTreeMap<LocalId, Type>) {
    match &expression.kind {
        ExprKind::Local(local) => {
            if !bound.contains(local) {
                found.entry(*local).or_insert_with(|| expression.ty.clone());
            }
        }
        ExprKind::Function(_) | ExprKind::ConstructorFunction(_) | ExprKind::Natural(_) => {}
        ExprKind::Construct(_, fields) | ExprKind::DirectCall(_, fields) => {
            for field in fields {
                free_locals(field, bound, found);
            }
        }
        ExprKind::Invoke(head, arguments) => {
            free_locals(head, bound, found);
            for argument in arguments {
                free_locals(argument, bound, found);
            }
        }
        ExprKind::Lambda(patterns, body) => {
            let mut nested = bound.clone();
            for pattern in patterns {
                pattern_locals(pattern, &mut nested);
            }
            free_locals(body, &nested, found);
        }
    }
}

fn pattern_locals(pattern: &Pattern, output: &mut HashSet<LocalId>) {
    match pattern {
        Pattern::Bind(local) => {
            output.insert(*local);
        }
        Pattern::Constructor(_, fields) | Pattern::List(fields, None) => {
            for field in fields {
                pattern_locals(field, output);
            }
        }
        Pattern::List(fields, Some(rest)) => {
            for field in fields {
                pattern_locals(field, output);
            }
            pattern_locals(rest, output);
        }
        Pattern::Wild | Pattern::Number { .. } | Pattern::Range(_, _) => {}
    }
}

const fn irrefutable(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Wild | Pattern::Bind(_))
}

fn type_name(ty: &Type, symbols: &crate::Symbols) -> String {
    match ty {
        Type::Named(name, arguments) if arguments.is_empty() => symbols.text(*name).to_string(),
        Type::Named(name, arguments) => format!(
            "{}$${}",
            symbols.text(*name),
            arguments
                .iter()
                .map(|argument| type_name(argument, symbols))
                .collect::<Vec<_>>()
                .join("$")
        ),
        Type::Function(parameters, result) => format!(
            "Fn$${}$to${}",
            parameters
                .iter()
                .map(|parameter| type_name(parameter, symbols))
                .collect::<Vec<_>>()
                .join("$"),
            type_name(result, symbols)
        ),
    }
}

fn function_name(key: &FunctionKey, symbols: &crate::Symbols) -> String {
    format!(
        "{}$${}",
        symbols.text(key.name),
        type_name(&key.ty, symbols)
    )
}

fn closure_name(key: &ClosureKey, symbols: &crate::Symbols) -> String {
    match key {
        ClosureKey::Global(function) => format!("Global$${}", symbols.text(function.name)),
        ClosureKey::Constructor(constructor, _) => {
            format!("Constructor$${}", symbols.text(*constructor))
        }
        ClosureKey::Lambda(module, span, _) => {
            format!("Lambda$${module:?}$${}", span.start)
        }
    }
}

fn error(message: impl Into<String>) -> LowerError {
    LowerError {
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn checked_example(name: &str) -> (ResolvedProgram, crate::check::CheckedProgram, PreludeIds) {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../notes/examples")
            .join(name);
        let loaded = crate::modules::load(&[entry], Some(&root)).unwrap();
        let prelude = PreludeIds::resolve(&loaded).unwrap();
        let resolved = crate::resolve::resolve(loaded).unwrap();
        let checked = crate::check::program(&resolved, &prelude).unwrap();
        (resolved, checked, prelude)
    }

    fn named(
        resolved: &ResolvedProgram,
        checked: &crate::check::CheckedProgram,
        suffix: &str,
    ) -> Symbol {
        checked
            .values
            .keys()
            .copied()
            .find(|symbol| resolved.symbols.text(*symbol).ends_with(suffix))
            .unwrap()
    }

    #[test]
    fn lowers_literals_to_valid_barb() {
        let (resolved, checked, prelude) = checked_example("literals.fn");
        for suffix in ["$$natural", "$$integer", "$$text"] {
            let entry = named(&resolved, &checked, suffix);
            let program = program(&resolved, &checked, &prelude, entry).unwrap();
            barb::validate(&program).unwrap();
        }
    }

    #[test]
    fn specializes_polymorphic_data_and_defunctionalizes_lambdas() {
        let (resolved, checked, prelude) = checked_example("utilities.fn");
        for suffix in ["$$mapped", "$$combined", "$$signed_sum"] {
            let entry = named(&resolved, &checked, suffix);
            let program = program(&resolved, &checked, &prelude, entry).unwrap();
            barb::validate(&program).unwrap();
        }
        let choose = named(&resolved, &checked, "$$choose");
        assert!(program(&resolved, &checked, &prelude, choose).is_err());

        let (resolved, checked, prelude) = checked_example("lowering.fn");
        for suffix in [
            "$$multi_specialized",
            "$$mapped_global",
            "$$mapped_capture",
            "$$wrapped",
            "$$wrapped_each",
            "$$from_external",
            "$$guarded_entry",
        ] {
            let entry = named(&resolved, &checked, suffix);
            let program = program(&resolved, &checked, &prelude, entry).unwrap();
            barb::validate(&program).unwrap();
        }
    }
}
