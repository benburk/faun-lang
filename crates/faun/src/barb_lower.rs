//! Emit a first-order program as Barb declarations and bodies, compiling
//! each function's clauses to a decision tree of matches.

#![allow(clippy::too_many_lines)]

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::fmt;

use faun_core::barb::{self, Atom, Builder, CtorId, FnId, TypeId};
use num_traits::ToPrimitive;

use crate::blessed::PreludeIds;
use crate::check::CheckedProgram;
use crate::diagnostic::Diagnostic;
use crate::first_order::{self as d, Expr, ExprKind};
use crate::hir as h;
use crate::hir::LocalId;
use crate::resolve::ResolvedProgram;
use crate::specialize::{self, FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowerError {
    pub message: String,
    /// Where in the source it is about, when that is known.
    pub at: Option<(ModuleId, crate::ast::Span)>,
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
            at: error.at,
        }
    }
}

/// Specialize the reachable program for its callbacks and emit Barb.
///
/// `entry` must name a monomorphic, parameterless function. The returned
/// program contains only concrete types and saturated first-order calls.
///
/// # Errors
///
/// Reports ambiguous specialization, unsupported structural types or ranges,
/// missing declarations, non-exhaustive clauses, and invalid literal shapes.
pub fn program(checked: &CheckedProgram, entry: Symbol) -> Result<barb::Program, LowerError> {
    let specialized = specialize::monomorphize_from_entry(checked, entry)?;
    let first_order = crate::first_order::first_order(specialized);
    Lowerer::new(checked, None, first_order)?.lower()
}

/// Emit a first-order package as Barb, starting at its `main! : Host -> []`
/// when it is an application.
///
/// The Barb entry is `main!` as written. `Host` holds its fields itself, each
/// named as the source spells it; machine lowering recognizes the startup
/// values among them, names the entry's parameters for them and drops those
/// nothing reads. `Host`'s bodyless methods are the target's routines, called
/// with the `Host` they were handed, as the source says.
///
/// # Errors
///
/// Reports Barb construction failures and a target without `exit!`.
pub(crate) fn lower_package_to_barb(
    checked: &CheckedProgram,
    first_order: d::Program,
    routines: &faun_core::platform::Routines,
) -> Result<barb::Program, Diagnostic> {
    Lowerer::new(checked, Some(routines), first_order)
        .and_then(Lowerer::lower)
        .map_err(|error| match error.at {
            Some((module, span)) => checked.resolved.diagnostic(module, span, error.message),
            None => Diagnostic::new(error.message),
        })
}

/// Select a uniquely named checked value and lower it as the entry.
///
/// # Errors
///
/// Reports a missing or ambiguous source-level name in addition to the errors
/// from [`program`].
pub fn named_program(checked: &CheckedProgram, entry: &str) -> Result<barb::Program, LowerError> {
    let resolved = &checked.resolved;
    let suffix = format!("$${entry}");
    let mut candidates = checked
        .types
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
    program(checked, selected)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Value(u32);

/// How a widening rebuilds a value: each constructor of the narrower type,
/// or none for a record, with each field's type there and in the wider one.
type Widening = Vec<(Option<Symbol>, Vec<(Type, Type)>)>;

#[derive(Clone, Debug)]
struct Subject {
    value: Value,
    ty: Type,
}

#[derive(Clone, Debug)]
struct Row {
    patterns: Vec<Pattern>,
    guard: Option<Expr>,
    body: d::Body,
    locals: HashMap<LocalId, Value>,
}

#[derive(Clone, Debug)]
enum Decision {
    Body {
        body: d::Body,
        locals: HashMap<LocalId, Value>,
    },
    Match {
        subject: Value,
        owner: Type,
        arms: Vec<DecisionArm>,
    },
    Record {
        subject: Value,
        owner: Type,
        fields: Vec<Value>,
        decision: Box<Self>,
    },
    Guard {
        condition: Expr,
        locals: HashMap<LocalId, Value>,
        false_constructor: Symbol,
        true_constructor: Symbol,
        otherwise: Box<Self>,
        answer: Box<Self>,
    },
    /// Whether a natural is a numeral: one test, where taking the numeral's
    /// successors off one at a time would be as many matches as it counts.
    Numeral {
        subject: Value,
        number: num_bigint::BigUint,
        equal: Box<Self>,
        otherwise: Box<Self>,
    },
}

impl Decision {
    fn tests_numerals(&self) -> bool {
        match self {
            Self::Body { .. } => false,
            Self::Numeral { .. } => true,
            Self::Match { arms, .. } => arms.iter().any(|arm| arm.decision.tests_numerals()),
            Self::Record { decision, .. } => decision.tests_numerals(),
            Self::Guard {
                otherwise, answer, ..
            } => otherwise.tests_numerals() || answer.tests_numerals(),
        }
    }
}

#[derive(Clone, Debug)]
struct DecisionArm {
    constructor: Symbol,
    fields: Vec<Value>,
    decision: Box<Decision>,
}

/// The largest numeral a column of naturals is taken apart for rather than
/// tested against. See [`Lowerer::numeral_column`].
const PEELED_NUMERALS: u8 = 8;

struct Lowerer<'a> {
    resolved: &'a ResolvedProgram,
    prelude: &'a PreludeIds,
    /// The target's routines, present when lowering an application.
    routines: Option<&'a faun_core::platform::Routines>,
    program: d::Program,
    types: BTreeSet<Type>,
    type_ids: HashMap<Type, TypeId>,
    constructor_ids: HashMap<(Symbol, Type), CtorId>,
    record_constructor_ids: HashMap<Type, CtorId>,
    record_wrappers: HashMap<Type, Type>,
    function_ids: HashMap<FunctionKey, FnId>,
    /// Each pair of types a value is widened between, which one function
    /// rebuilding it answers for.
    widenings: BTreeSet<(Type, Type)>,
    widen_ids: HashMap<(Type, Type), FnId>,
    /// Where each call emitted was written, so a refusal naming the call
    /// can point at it. Barb's ids hold until the program is rewritten,
    /// which is after it is validated.
    call_sites: RefCell<HashMap<barb::ExprId, (ModuleId, crate::ast::Span)>>,
    /// Whether two naturals are equal, written once where a numeral is
    /// matched, in the shape Barb recognizes as that comparison.
    numeral_equals: Option<FnId>,
    output: barb::Program,
}

impl<'a> Lowerer<'a> {
    fn new(
        checked: &'a CheckedProgram,
        routines: Option<&'a faun_core::platform::Routines>,
        program: d::Program,
    ) -> Result<Self, LowerError> {
        let mut lowerer = Self {
            resolved: &checked.resolved,
            prelude: &checked.prelude,
            routines,
            program,
            types: BTreeSet::new(),
            type_ids: HashMap::new(),
            constructor_ids: HashMap::new(),
            record_constructor_ids: HashMap::new(),
            record_wrappers: HashMap::new(),
            function_ids: HashMap::new(),
            widenings: BTreeSet::new(),
            widen_ids: HashMap::new(),
            call_sites: RefCell::default(),
            numeral_equals: None,
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
        self.define_widenings()?;
        if let Some(routines) = self.routines
            && routines.get("exit!").is_none()
        {
            return Err(error("the selected target does not provide `exit!`"));
        }
        if let Some(entry) = &self.program.entry {
            self.output.set_entry(self.function_ids[entry]);
        }
        barb::validate(&self.output).map_err(|refusal| self.refused(refusal))?;
        Ok(self.output)
    }

    /// A refusal, placed at the call it names, or else at the definition.
    fn refused(&self, refusal: barb::Refusal) -> LowerError {
        let call = refusal
            .call
            .and_then(|call| self.call_sites.borrow().get(&call).copied());
        let definition = || {
            let function = refusal.function?;
            let (key, _) = self.function_ids.iter().find(|(_, id)| **id == function)?;
            self.definition_site(key.name)
        };
        LowerError {
            at: call.or_else(definition),
            message: refusal.message,
        }
    }

    /// Where the first clause defining `name` is written.
    fn definition_site(&self, name: Symbol) -> Option<(ModuleId, crate::ast::Span)> {
        self.resolved.program.modules.iter().find_map(|module| {
            module.items.iter().find_map(|item| match item {
                h::Item::Clause(clause) if clause.name == name => {
                    Some((module.source, clause.span))
                }
                h::Item::Data(data) => data.methods.iter().find_map(|method| match method {
                    h::MethodItem::Clause(clause) if clause.name == name => {
                        Some((module.source, clause.span))
                    }
                    _ => None,
                }),
                _ => None,
            })
        })
    }

    /// Find every type the program holds, each of which Barb declares.
    fn discover(&mut self) -> Result<(), LowerError> {
        let functions = std::mem::take(&mut self.program.functions);
        let found = self.discover_in(&functions);
        self.program.functions = functions;
        found
    }

    fn discover_in(&mut self, functions: &[d::Function]) -> Result<(), LowerError> {
        for function in functions {
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
                // A numeral is tested for, and a test answers a `Bool`.
                if clause.patterns.iter().any(holds_numeral) {
                    self.collect_type(&Type::Named(self.prelude.bool_, Vec::new()))?;
                }
                if let Some(guard) = &clause.guard {
                    self.collect_expr(guard, result)?;
                }
                self.collect_body(&clause.body, result)?;
            }
        }
        loop {
            let before = self.types.len();
            let types: Vec<_> = self.types.iter().cloned().collect();
            for ty in types {
                if let Type::Named(name, _) = &ty {
                    let constructors = self.constructors_of(&ty)?;
                    for (_, fields) in &constructors {
                        for field in fields {
                            self.collect_type(field)?;
                        }
                    }
                    if self.program.data[name].wrapper.is_some()
                        && let [(_, fields)] = constructors.as_slice()
                        && let [field @ Type::Record(_)] = fields.as_slice()
                    {
                        self.record_wrappers.insert(ty, field.clone());
                    }
                }
            }
            if self.types.len() == before {
                return Ok(());
            }
        }
    }

    /// Find what `body` holds, where its function or lambda answers
    /// `answer`, which a `?` in it answers early with.
    fn collect_body(&mut self, body: &d::Body, answer: &Type) -> Result<(), LowerError> {
        for binding in &body.bindings {
            self.collect_expr(&binding.value, answer)?;
            if !takes_apart(&binding.pattern) {
                return Err(error(
                    "a binding takes a value apart only as records and tuples, which always match",
                ));
            }
        }
        self.collect_expr(&body.result, answer)
    }

    fn collect_expr(&mut self, expression: &Expr, answer: &Type) -> Result<(), LowerError> {
        self.collect_type(&expression.ty)?;
        match &expression.kind {
            ExprKind::Local(_) | ExprKind::Natural(_) => {}
            ExprKind::Construct(_, fields) | ExprKind::DirectCall(_, fields) => {
                for field in fields {
                    self.collect_expr(field, answer)?;
                }
            }
            ExprKind::Record(fields) => {
                for (_, field) in fields {
                    self.collect_expr(field, answer)?;
                }
            }
            ExprKind::Tuple(members) => {
                for member in members {
                    self.collect_expr(member, answer)?;
                }
            }
            ExprKind::Update(base, fields) => {
                self.collect_expr(base, answer)?;
                for (_, field) in fields {
                    self.collect_expr(field, answer)?;
                }
            }
            ExprKind::Project(receiver, _) => self.collect_expr(receiver, answer)?,
            // An `Err` answered early is widened into what is answered.
            ExprKind::Try(value) => {
                self.collect_expr(value, answer)?;
                if let (Type::Named(_, taken), Type::Named(_, answered)) = (&value.ty, answer)
                    && let ([_, from], [_, to]) = (taken.as_slice(), answered.as_slice())
                {
                    self.collect_type(answer)?;
                    self.collect_widening(from, to)?;
                }
            }
            ExprKind::Widen(value) => {
                self.collect_expr(value, answer)?;
                self.collect_widening(&value.ty, &expression.ty)?;
            }
        }
        Ok(())
    }

    /// Note that values of `from` are widened to `to`, and so are whatever
    /// of their fields differ between the two.
    fn collect_widening(&mut self, from: &Type, to: &Type) -> Result<(), LowerError> {
        if from == to || !self.widenings.insert((from.clone(), to.clone())) {
            return Ok(());
        }
        self.collect_type(from)?;
        self.collect_type(to)?;
        for (source, target) in self
            .widening_fields(from, to)?
            .into_iter()
            .flat_map(|(_, pairs)| pairs)
        {
            self.collect_widening(&source, &target)?;
        }
        Ok(())
    }

    /// Each constructor of `from` with its fields' types there and in `to`,
    /// which holds every one of them. A record is one constructor, named
    /// by nothing.
    fn widening_fields(&self, from: &Type, to: &Type) -> Result<Widening, LowerError> {
        if let (Some(source), Some(target)) = (members(from), members(to)) {
            return Ok(vec![(None, source.into_iter().zip(target).collect())]);
        }
        let target = self.constructors_of(to)?;
        self.constructors_of(from)?
            .into_iter()
            .map(|(constructor, fields)| {
                let (_, widened) = target
                    .iter()
                    .find(|(found, _)| *found == constructor)
                    .ok_or_else(|| {
                        error("a widened type lacks one of its source's constructors")
                    })?;
                Ok((
                    Some(constructor),
                    fields.into_iter().zip(widened.iter().cloned()).collect(),
                ))
            })
            .collect()
    }

    fn collect_type(&mut self, ty: &Type) -> Result<(), LowerError> {
        if !self.types.insert(ty.clone()) {
            return Ok(());
        }
        match ty {
            Type::Named(name, _) => {
                if !self.program.data.contains_key(name) {
                    return Err(error(format!(
                        "type `{}` has no data declaration",
                        self.resolved.symbols.text(*name)
                    )));
                }
            }
            Type::Function(..) => {
                return Err(error(
                    "a function is never a value once its callbacks are specialized",
                ));
            }
            Type::Variants(tags) => {
                for field in tags.iter().flat_map(|(_, fields)| fields) {
                    self.collect_type(field)?;
                }
            }
            Type::Record(fields) => {
                for (_, field) in fields {
                    self.collect_type(field)?;
                }
            }
            Type::Tuple(members) => {
                for member in members {
                    self.collect_type(member)?;
                }
            }
        }
        Ok(())
    }

    fn declare_types(&mut self) {
        for ty in &self.types {
            let name = type_name(ty, &self.resolved.symbols);
            let id = if matches!(ty, Type::Variants(_) | Type::Record(_) | Type::Tuple(_)) {
                self.output.declare_inline_type(&name)
            } else {
                self.output.declare_type(&name)
            };
            self.type_ids.insert(ty.clone(), id);
        }
    }

    fn define_types(&mut self) -> Result<(), LowerError> {
        let types: Vec<_> = self.types.iter().cloned().collect();
        for ty in types {
            let id = self.type_ids[&ty];
            match &ty {
                Type::Named(_, _) if self.record_wrappers.contains_key(&ty) => {
                    self.define_record_wrapper(&ty, id);
                }
                Type::Named(_, _) | Type::Variants(_) => {
                    let constructors = self.constructors_of(&ty)?;
                    let held: Vec<_> = constructors
                        .iter()
                        .map(|(name, fields)| {
                            (
                                source_name(*name, &self.resolved.symbols).to_string(),
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
                Type::Record(fields) => {
                    let fields = self.named_fields(fields);
                    self.output
                        .define_fields(id, &[("Record", fields.as_slice())]);
                    self.record_constructor_ids
                        .insert(ty.clone(), self.output.ctor_at(id, 0));
                }
                Type::Tuple(members) => {
                    let members: Vec<_> =
                        members.iter().map(|member| self.type_ids[member]).collect();
                    self.output
                        .define_type(id, &[("Tuple", members.as_slice())]);
                    self.record_constructor_ids
                        .insert(ty.clone(), self.output.ctor_at(id, 0));
                }
                Type::Function(..) => unreachable!("collection refuses a function type"),
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

    /// A record's fields, each named as the program spells it.
    fn named_fields(&self, fields: &[(Symbol, Type)]) -> Vec<barb::Field<'a>> {
        fields
            .iter()
            .map(|(name, ty)| {
                barb::Field::of(self.type_ids[ty]).named(self.resolved.symbols.text(*name))
            })
            .collect()
    }

    /// A nominal wrapper around a record holds the record's fields itself,
    /// each named as the program spells it. `Host`'s are the startup values
    /// its target produces, which the target recognizes by those names.
    fn define_record_wrapper(&mut self, ty: &Type, id: TypeId) {
        let Type::Named(name, _) = ty else {
            unreachable!("a record wrapper is a named type")
        };
        let Type::Record(fields) = self.record_wrappers[ty].clone() else {
            unreachable!("record wrappers map to record types")
        };
        let held = self.named_fields(&fields);
        let wrapper = self.program.data[name]
            .wrapper
            .as_ref()
            .expect("a record wrapper")
            .constructor;
        let spelled = source_name(wrapper, &self.resolved.symbols).to_owned();
        self.output
            .define_fields(id, &[(spelled.as_str(), held.as_slice())]);
        self.constructor_ids
            .insert((wrapper, ty.clone()), self.output.ctor_at(id, 0));
    }

    fn declare_functions(&mut self) -> Result<(), LowerError> {
        for function in &self.program.functions {
            let (parameters, result) = function
                .key
                .ty
                .function()
                .ok_or_else(|| error("specialized global is not a function"))?;
            let parameters: Vec<_> = parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| (format!("v{index}"), self.type_ids[parameter]))
                .collect();
            let borrowed: Vec<_> = parameters
                .iter()
                .map(|(name, ty)| (name.as_str(), *ty))
                .collect();
            let result = self.type_ids[result];
            let name = function_name(&function.key, &self.resolved.symbols);
            let id = self.output.declare_named(&name, &borrowed, result);
            if let Some(provider) = function.provider {
                let provider = self.resolved.symbols.text(provider);
                self.output.answered_by(id, provider);
            }
            self.function_ids.insert(function.key.clone(), id);
        }
        for (from, to) in &self.widenings {
            let id = self
                .output
                .declare("widen", &[self.type_ids[from]], self.type_ids[to]);
            self.widen_ids.insert((from.clone(), to.clone()), id);
        }
        Ok(())
    }

    /// Each widening rebuilds a value in the wider type: the constructor it
    /// was built with, each field widened in turn where its type differs.
    fn define_widenings(&mut self) -> Result<(), LowerError> {
        let widenings: Vec<_> = self.widenings.iter().cloned().collect();
        for (from, to) in widenings {
            let plan = self.widening_fields(&from, &to)?;
            let id = self.widen_ids[&(from.clone(), to.clone())];
            let context = EmitContext {
                type_ids: &self.type_ids,
                constructor_ids: &self.constructor_ids,
                record_constructor_ids: &self.record_constructor_ids,
                record_wrappers: &self.record_wrappers,
                function_ids: &self.function_ids,
                widen_ids: &self.widen_ids,
                call_sites: &self.call_sites,
                prelude: self.prelude,
                numeral_equals: self.numeral_equals,
                answer: &to,
            };
            self.output.define(id, |builder, parameters| {
                builder.match_(
                    parameters[0],
                    context.type_ids[&from],
                    |builder, built, fields| {
                        let (constructor, pairs) = plan
                            .iter()
                            .find(|(constructor, _)| {
                                constructor.is_none_or(|constructor| {
                                    context.constructor_ids[&(constructor, from.clone())] == built
                                })
                            })
                            .expect("the plan has every constructor of its source");
                        let fields = match constructor {
                            Some(_) => context.arm_fields(builder, &from, fields),
                            None => fields.to_vec(),
                        };
                        let widened: Vec<_> = fields
                            .iter()
                            .zip(pairs)
                            .map(|(field, (source, target))| {
                                context.widen(builder, *field, source, target)
                            })
                            .collect();
                        match constructor {
                            Some(constructor) => {
                                context.construct(builder, *constructor, &to, &widened)
                            }
                            None => builder.con(context.record_constructor_ids[&to], &widened),
                        }
                    },
                )
            });
        }
        Ok(())
    }

    fn define_functions(&mut self) -> Result<(), LowerError> {
        let functions = std::mem::take(&mut self.program.functions);
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
            if decision.tests_numerals() && self.numeral_equals.is_none() {
                self.numeral_equals = Some(self.define_numeral_equals());
            }
            let function_id = self.function_ids[&function.key];
            let (_, answer) = function
                .key
                .ty
                .function()
                .expect("specialized global is a function");
            let context = EmitContext {
                type_ids: &self.type_ids,
                constructor_ids: &self.constructor_ids,
                record_constructor_ids: &self.record_constructor_ids,
                record_wrappers: &self.record_wrappers,
                function_ids: &self.function_ids,
                widen_ids: &self.widen_ids,
                call_sites: &self.call_sites,
                prelude: self.prelude,
                numeral_equals: self.numeral_equals,
                answer,
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
        if let Some(member_types) = members(&subject.ty) {
            let fields: Vec<_> = member_types
                .iter()
                .map(|_| {
                    let value = Value(*next);
                    *next = next.checked_add(1).expect("fewer than 2^32 plan values");
                    value
                })
                .collect();
            let mut specialized = Vec::with_capacity(rows.len());
            for mut row in rows.iter().cloned() {
                let normalized =
                    self.normalize_pattern(row.patterns[column].clone(), &subject.ty)?;
                let replacement = match normalized {
                    Pattern::Wild => vec![Pattern::Wild; fields.len()],
                    Pattern::Bind(local) => {
                        row.locals.insert(local, subject.value);
                        vec![Pattern::Wild; fields.len()]
                    }
                    Pattern::Product(patterns) => patterns,
                    _ => unreachable!("record and tuple patterns normalize to a product"),
                };
                if replacement.len() != fields.len() {
                    return Err(error("a product pattern has the wrong field count"));
                }
                row.patterns.splice(column..=column, replacement);
                specialized.push(row);
            }
            let mut nested_subjects = subjects.to_vec();
            nested_subjects.splice(
                column..=column,
                fields
                    .iter()
                    .copied()
                    .zip(member_types)
                    .map(|(value, ty)| Subject { value, ty }),
            );
            return Ok(Decision::Record {
                subject: subject.value,
                owner: subject.ty.clone(),
                fields,
                decision: Box::new(self.plan(&specialized, &nested_subjects, next)?),
            });
        }
        if let Some(number) = self.numeral_column(rows, column, &subject.ty) {
            let mut equal = Vec::new();
            let mut otherwise = Vec::new();
            for row in rows {
                match &row.patterns[column] {
                    Pattern::Number { magnitude, .. } if *magnitude == number => {
                        let mut row = row.clone();
                        row.patterns[column] = Pattern::Wild;
                        equal.push(row);
                    }
                    Pattern::Number { .. } => otherwise.push(row.clone()),
                    _ => {
                        equal.push(row.clone());
                        otherwise.push(row.clone());
                    }
                }
            }
            return Ok(Decision::Numeral {
                subject: subject.value,
                number,
                equal: Box::new(self.plan(&equal, subjects, next)?),
                otherwise: Box::new(self.plan(&otherwise, subjects, next)?),
            });
        }
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

    /// The numeral a column of naturals is first tested for, where every
    /// pattern in it is a numeral or takes anything, and some numeral is
    /// past [`PEELED_NUMERALS`]: then each is one test.
    ///
    /// A small numeral is taken apart instead, a successor at a time. That
    /// is as few matches as tests, and what it says is more: past `0` a
    /// number is a successor, which is how a definition counting down is
    /// seen to stop. A column also taking successors apart is taken apart,
    /// numerals and all, since a test says nothing about what a successor
    /// holds.
    fn numeral_column(
        &self,
        rows: &[Row],
        column: usize,
        ty: &Type,
    ) -> Option<num_bigint::BigUint> {
        if *ty != Type::Named(self.prelude.nat, Vec::new())
            || !self
                .type_ids
                .contains_key(&Type::Named(self.prelude.bool_, Vec::new()))
        {
            return None;
        }
        let mut first = None;
        let mut largest = num_bigint::BigUint::ZERO;
        for row in rows {
            match &row.patterns[column] {
                Pattern::Number {
                    magnitude,
                    negative: false,
                } => {
                    first.get_or_insert_with(|| magnitude.clone());
                    largest = largest.max(magnitude.clone());
                }
                Pattern::Wild | Pattern::Bind(_) => {}
                _ => return None,
            }
        }
        first.filter(|_| largest > num_bigint::BigUint::from(PEELED_NUMERALS))
    }

    /// Declare and write whether two naturals are equal: nought is nought,
    /// a successor is one if what they succeed is.
    fn define_numeral_equals(&mut self) -> FnId {
        let nat_ty = Type::Named(self.prelude.nat, Vec::new());
        let bool_ty = Type::Named(self.prelude.bool_, Vec::new());
        let (nat, bool_) = (self.type_ids[&nat_ty], self.type_ids[&bool_ty]);
        let yes = self.constructor_ids[&(self.prelude.bool_true, bool_ty.clone())];
        let no = self.constructor_ids[&(self.prelude.bool_false, bool_ty)];
        let id = self.output.declare("numeral.equals", &[nat, nat], bool_);
        self.output.define(id, |b, args| {
            let other = args[1];
            b.match_(args[0], nat, |b, _, fields| {
                let first = fields.first().copied();
                b.match_(other, nat, |b, _, rest| match (first, rest.first()) {
                    (None, None) => b.con(yes, &[]),
                    (Some(a), Some(&c)) => b.call(id, &[a, c]),
                    _ => b.con(no, &[]),
                })
            })
        });
        id
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
            Pattern::String => Err(error(
                "a string pattern is a test, which only a clause's guard makes",
            )),
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
            // A field the pattern does not name is taken whatever it is.
            Pattern::Record(mut fields) => {
                let Type::Record(expected) = expected else {
                    return Err(error("record pattern does not have a record type"));
                };
                if fields
                    .iter()
                    .any(|(found, _)| !expected.iter().any(|(wanted, _)| wanted == found))
                {
                    return Err(error("record pattern names a field its type lacks"));
                }
                Ok(Pattern::Product(
                    expected
                        .iter()
                        .map(|(wanted, _)| {
                            fields
                                .iter()
                                .position(|(found, _)| found == wanted)
                                .map_or(Pattern::Wild, |at| fields.swap_remove(at).1)
                        })
                        .collect(),
                ))
            }
            product @ Pattern::Product(_) => Ok(product),
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
            let constructors = &self.program.data[name].constructors;
            if constructors.len() != 2 {
                return Err(error("Int must have positive and negative constructors"));
            }
            // The natural inside is a numeral too, tested where it is taken
            // apart rather than counted down here.
            if negative && magnitude != num_bigint::BigUint::ZERO {
                let predecessor = magnitude - 1u8;
                return Ok(Pattern::Constructor(
                    constructors[1].name,
                    vec![Pattern::Number {
                        magnitude: predecessor,
                        negative: false,
                    }],
                ));
            }
            return Ok(Pattern::Constructor(
                constructors[0].name,
                vec![Pattern::Number {
                    magnitude,
                    negative: false,
                }],
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
        let constructors = &self.program.data[&self.prelude.nat].constructors;
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

    /// Each constructor of `ty` with its fields' types. A tag row's are its
    /// tags, named by their spellings.
    fn constructors_of(&self, ty: &Type) -> Result<Vec<(Symbol, Vec<Type>)>, LowerError> {
        if let Type::Variants(tags) = ty {
            return Ok(tags.clone());
        }
        let Type::Named(name, arguments) = ty else {
            return Err(error("pattern matching requires a named data type"));
        };
        let data = self
            .program
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
    record_constructor_ids: &'a HashMap<Type, CtorId>,
    record_wrappers: &'a HashMap<Type, Type>,
    function_ids: &'a HashMap<FunctionKey, FnId>,
    widen_ids: &'a HashMap<(Type, Type), FnId>,
    call_sites: &'a RefCell<HashMap<barb::ExprId, (ModuleId, crate::ast::Span)>>,
    prelude: &'a PreludeIds,
    numeral_equals: Option<FnId>,
    /// What the function or lambda being emitted answers, which a `?` in
    /// it answers an `Err` early as.
    answer: &'a Type,
}

impl EmitContext<'_> {
    /// `value`, of type `from`, as a value of the wider `to`.
    fn widen(&self, builder: &mut Builder<'_>, value: Atom, from: &Type, to: &Type) -> Atom {
        if from == to {
            return value;
        }
        builder.call(self.widen_ids[&(from.clone(), to.clone())], &[value])
    }

    /// Build a value of `ty` with `constructor` from `fields`. A record
    /// wrapper holds its record's fields itself, so its one field, the
    /// record, is taken apart into them.
    fn construct(
        &self,
        builder: &mut Builder<'_>,
        constructor: Symbol,
        ty: &Type,
        fields: &[Atom],
    ) -> Atom {
        let id = self.constructor_ids[&(constructor, ty.clone())];
        let Some(record) = self.record_wrappers.get(ty) else {
            return builder.con(id, fields);
        };
        let [record_value] = fields else {
            unreachable!("a record wrapper is built from one record")
        };
        builder.match_(*record_value, self.type_ids[record], |builder, _, held| {
            builder.con(id, held)
        })
    }

    /// What an arm of `owner` binds: its fields, except that a record
    /// wrapper's arm binds the one record its fields make.
    fn arm_fields(&self, builder: &mut Builder<'_>, owner: &Type, fields: &[Atom]) -> Vec<Atom> {
        self.record_wrappers.get(owner).map_or_else(
            || fields.to_vec(),
            |record| vec![builder.con(self.record_constructor_ids[record], fields)],
        )
    }

    /// Emit a call to `function` written as `expression`, noting where.
    fn call_written(
        &self,
        builder: &mut Builder<'_>,
        function: FnId,
        arguments: &[Atom],
        expression: &Expr,
    ) -> Atom {
        let (atom, site) = builder.call_site(function, arguments);
        self.call_sites
            .borrow_mut()
            .insert(site, (expression.module, expression.span));
        atom
    }
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
                let fields = context.arm_fields(builder, owner, fields);
                let mut nested = values.clone();
                for (value, atom) in arm.fields.iter().zip(fields) {
                    nested.insert(*value, atom);
                }
                emit_decision(context, builder, &arm.decision, &nested)
            })
        }
        Decision::Record {
            subject,
            owner,
            fields,
            decision,
        } => builder.match_(
            values[subject],
            context.type_ids[owner],
            |builder, _, atoms| {
                let mut nested = values.clone();
                for (value, atom) in fields.iter().zip(atoms) {
                    nested.insert(*value, *atom);
                }
                emit_decision(context, builder, decision, &nested)
            },
        ),
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
        Decision::Numeral {
            subject,
            number,
            equal,
            otherwise,
        } => {
            let nat_ty = Type::Named(context.prelude.nat, Vec::new());
            let known = builder
                .natural(context.type_ids[&nat_ty], number)
                .expect("Nat has a natural's shape");
            let known = builder.known(known);
            let equals = context
                .numeral_equals
                .expect("a numeral's test is written before it is read");
            let test = builder.call(equals, &[values[subject], known]);
            let bool_ty = Type::Named(context.prelude.bool_, Vec::new());
            let true_id = context.constructor_ids[&(context.prelude.bool_true, bool_ty.clone())];
            builder.match_(
                test,
                context.type_ids[&bool_ty],
                |builder, constructor, _| {
                    if constructor == true_id {
                        emit_decision(context, builder, equal, values)
                    } else {
                        emit_decision(context, builder, otherwise, values)
                    }
                },
            )
        }
    }
}

fn emit_body(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    body: &d::Body,
    locals: HashMap<LocalId, Atom>,
) -> Atom {
    let body = hoisted(body);
    emit_bindings(context, builder, &body.bindings, &body.result, locals)
}

/// Emit bindings in order, then the answer. A binding of `value?` takes the
/// value apart: its `Ok` goes on to the rest of the body, and its `Err` is
/// what this answers, at once.
fn emit_bindings(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    bindings: &[d::Binding],
    result: &Expr,
    mut locals: HashMap<LocalId, Atom>,
) -> Atom {
    let Some((binding, rest)) = bindings.split_first() else {
        return emit_expr(context, builder, result, &locals);
    };
    let bind = |locals: &mut HashMap<LocalId, Atom>, value| match binding.pattern {
        Pattern::Wild => {}
        Pattern::Bind(local) => {
            locals.insert(local, value);
        }
        _ => unreachable!("a pattern taking a value apart is bound by `destructure`"),
    };
    let ExprKind::Try(taken) = &binding.value.kind else {
        let value = emit_expr(context, builder, &binding.value, &locals);
        if !matches!(binding.pattern, Pattern::Wild | Pattern::Bind(_)) {
            return destructure(
                context,
                builder,
                (value, &binding.value.ty),
                &binding.pattern,
                locals,
                &|builder, locals| emit_bindings(context, builder, rest, result, locals),
            );
        }
        bind(&mut locals, value);
        return emit_bindings(context, builder, rest, result, locals);
    };
    let value = emit_expr(context, builder, taken, &locals);
    let (Type::Named(_, taken_types), Type::Named(_, answered_types)) = (&taken.ty, context.answer)
    else {
        unreachable!("`?` takes and answers results")
    };
    let ok = context.constructor_ids[&(context.prelude.result_ok, taken.ty.clone())];
    builder.match_(
        value,
        context.type_ids[&taken.ty],
        |builder, built, fields| {
            if built == ok {
                let mut locals = locals.clone();
                bind(&mut locals, fields[0]);
                emit_bindings(context, builder, rest, result, locals)
            } else {
                let error = context.widen(builder, fields[0], &taken_types[1], &answered_types[1]);
                context.construct(
                    builder,
                    context.prelude.result_err,
                    context.answer,
                    &[error],
                )
            }
        },
    )
}

/// Take `value` apart as `pattern`, a record or tuple of names, then go on.
fn destructure(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    (value, ty): (Atom, &Type),
    pattern: &Pattern,
    mut locals: HashMap<LocalId, Atom>,
    then: &dyn Fn(&mut Builder<'_>, HashMap<LocalId, Atom>) -> Atom,
) -> Atom {
    let parts: Vec<(Pattern, Type)> = match (pattern, ty) {
        (Pattern::Wild, _) => return then(builder, locals),
        (Pattern::Bind(local), _) => {
            locals.insert(*local, value);
            return then(builder, locals);
        }
        (Pattern::Record(named), Type::Record(fields)) => fields
            .iter()
            .map(|(name, ty)| {
                let part = named
                    .iter()
                    .find(|(found, _)| found == name)
                    .map_or(Pattern::Wild, |(_, pattern)| pattern.clone());
                (part, ty.clone())
            })
            .collect(),
        (Pattern::Product(members), Type::Tuple(types)) => {
            members.iter().cloned().zip(types.iter().cloned()).collect()
        }
        _ => unreachable!("a binding takes apart only records and tuples"),
    };
    builder.match_(value, context.type_ids[ty], |builder, _, held| {
        let held = held.to_vec();
        destructure_each(context, builder, &held, &parts, locals.clone(), then)
    })
}

fn destructure_each(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    held: &[Atom],
    parts: &[(Pattern, Type)],
    locals: HashMap<LocalId, Atom>,
    then: &dyn Fn(&mut Builder<'_>, HashMap<LocalId, Atom>) -> Atom,
) -> Atom {
    let (Some((&value, held)), Some(((pattern, ty), parts))) =
        (held.split_first(), parts.split_first())
    else {
        return then(builder, locals);
    };
    destructure(
        context,
        builder,
        (value, ty),
        pattern,
        locals,
        &|builder, locals| destructure_each(context, builder, held, parts, locals, then),
    )
}

/// Whether a binding's pattern is one lowering takes a value apart with:
/// names, and records and tuples of them, which always match.
fn takes_apart(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wild | Pattern::Bind(_) => true,
        Pattern::Record(fields) => fields.iter().all(|(_, pattern)| takes_apart(pattern)),
        Pattern::Product(members) => members.iter().all(takes_apart),
        _ => false,
    }
}

/// `body` with every `value?` in it bound on its own, in the order it is
/// evaluated, and read back where it was written: what follows a `?` runs
/// only on its `Ok`. Evaluation is pure but for effects, which stand on
/// their own, so taking a `?` out ahead of the rest of its expression
/// changes nothing a program can see.
fn hoisted(body: &d::Body) -> d::Body {
    let mut fresh = 0;
    let mut bindings = Vec::with_capacity(body.bindings.len());
    for binding in &body.bindings {
        let value = lifted(&binding.value, &mut bindings, &mut fresh);
        bindings.push(d::Binding {
            pattern: binding.pattern.clone(),
            value,
        });
    }
    let result = lifted(&body.result, &mut bindings, &mut fresh);
    d::Body { bindings, result }
}

/// `expression` with each `?` in it replaced by a local bound before it.
fn lifted(expression: &Expr, bindings: &mut Vec<d::Binding>, fresh: &mut u32) -> Expr {
    let mut lift = |inner: &Expr| lifted(inner, bindings, fresh);
    let kind = match &expression.kind {
        ExprKind::Local(_) | ExprKind::Natural(_) => {
            return expression.clone();
        }
        ExprKind::Construct(constructor, fields) => {
            ExprKind::Construct(*constructor, fields.iter().map(&mut lift).collect())
        }
        ExprKind::Record(fields) => ExprKind::Record(
            fields
                .iter()
                .map(|(name, field)| (*name, lift(field)))
                .collect(),
        ),
        ExprKind::Tuple(members) => ExprKind::Tuple(members.iter().map(&mut lift).collect()),
        ExprKind::Update(base, fields) => {
            let base = lift(base);
            ExprKind::Update(
                Box::new(base),
                fields
                    .iter()
                    .map(|(name, field)| (*name, lift(field)))
                    .collect(),
            )
        }
        ExprKind::Project(receiver, field) => ExprKind::Project(Box::new(lift(receiver)), *field),
        ExprKind::DirectCall(key, arguments) => {
            ExprKind::DirectCall(key.clone(), arguments.iter().map(&mut lift).collect())
        }
        ExprKind::Widen(value) => ExprKind::Widen(Box::new(lift(value))),
        ExprKind::Try(value) => {
            let value = lift(value);
            // Past any local a clause can have: they are numbered from nought.
            let local = LocalId(u32::MAX - *fresh);
            *fresh += 1;
            bindings.push(d::Binding {
                pattern: Pattern::Bind(local),
                value: Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::Try(Box::new(value)),
                },
            });
            ExprKind::Local(local)
        }
    };
    Expr {
        module: expression.module,
        span: expression.span,
        ty: expression.ty.clone(),
        kind,
    }
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
        ExprKind::Construct(constructor, fields) => {
            let fields = fields
                .iter()
                .map(|field| emit_expr(context, builder, field, locals))
                .collect::<Vec<_>>();
            context.construct(builder, *constructor, &expression.ty, &fields)
        }
        ExprKind::Record(fields) => {
            let mut fields = fields
                .iter()
                .map(|(name, field)| (*name, emit_expr(context, builder, field, locals)))
                .collect::<Vec<_>>();
            fields.sort_by_key(|(name, _)| *name);
            let fields: Vec<_> = fields.into_iter().map(|(_, field)| field).collect();
            builder.con(context.record_constructor_ids[&expression.ty], &fields)
        }
        ExprKind::Tuple(members) => {
            let members: Vec<_> = members
                .iter()
                .map(|member| emit_expr(context, builder, member, locals))
                .collect();
            builder.con(context.record_constructor_ids[&expression.ty], &members)
        }
        // The replacements are worked out first, in the order written, then
        // the record is taken apart and built again with them in their places.
        ExprKind::Update(base, fields) => {
            let record = emit_expr(context, builder, base, locals);
            let replaced: Vec<_> = fields
                .iter()
                .map(|(name, field)| (*name, emit_expr(context, builder, field, locals)))
                .collect();
            let Type::Record(layout) = &expression.ty else {
                unreachable!("an update builds a record")
            };
            let constructor = context.record_constructor_ids[&expression.ty];
            builder.match_(
                record,
                context.type_ids[&expression.ty],
                |builder, _, held| {
                    let rebuilt: Vec<_> = layout
                        .iter()
                        .zip(held)
                        .map(|((name, _), kept)| {
                            replaced
                                .iter()
                                .find(|(found, _)| found == name)
                                .map_or(*kept, |(_, value)| *value)
                        })
                        .collect();
                    builder.con(constructor, &rebuilt)
                },
            )
        }
        ExprKind::Project(receiver, field) => {
            let atom = emit_expr(context, builder, receiver, locals);
            emit_projection(context, builder, atom, &receiver.ty, *field)
        }
        ExprKind::DirectCall(key, arguments) => {
            let arguments = arguments
                .iter()
                .map(|argument| emit_expr(context, builder, argument, locals))
                .collect::<Vec<_>>();
            context.call_written(builder, context.function_ids[key], &arguments, expression)
        }
        ExprKind::Widen(value) => {
            let atom = emit_expr(context, builder, value, locals);
            context.widen(builder, atom, &value.ty, &expression.ty)
        }
        ExprKind::Try(_) => unreachable!("every `?` is bound on its own before emission"),
    }
}

fn emit_projection(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    receiver: Atom,
    receiver_ty: &Type,
    field: Symbol,
) -> Atom {
    if let Type::Record(fields) = receiver_ty {
        let index = fields
            .iter()
            .position(|(name, _)| *name == field)
            .expect("checked projection names a record field");
        return builder.match_(receiver, context.type_ids[receiver_ty], |_, _, values| {
            values[index]
        });
    }
    // A record wrapper holds its record's fields itself.
    let Type::Record(fields) = &context.record_wrappers[receiver_ty] else {
        unreachable!("record wrappers map to record types")
    };
    let index = fields
        .iter()
        .position(|(name, _)| *name == field)
        .expect("checked projection names a record field");
    builder.match_(receiver, context.type_ids[receiver_ty], |_, _, values| {
        values[index]
    })
}

/// The types of a record's fields, in their order, or a tuple's members:
/// the columns a product is taken apart into.
fn members(ty: &Type) -> Option<Vec<Type>> {
    match ty {
        Type::Record(fields) => Some(fields.iter().map(|(_, ty)| ty.clone()).collect()),
        Type::Tuple(members) => Some(members.clone()),
        _ => None,
    }
}

/// Whether a pattern matches a numeral anywhere in it.
fn holds_numeral(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Number { .. } => true,
        Pattern::Constructor(_, inner) | Pattern::Product(inner) => inner.iter().any(holds_numeral),
        Pattern::List(inner, rest) => {
            inner.iter().any(holds_numeral) || rest.as_deref().is_some_and(holds_numeral)
        }
        Pattern::Record(fields) => fields.iter().any(|(_, inner)| holds_numeral(inner)),
        Pattern::Wild | Pattern::Bind(_) | Pattern::Range(..) | Pattern::String => false,
    }
}

const fn irrefutable(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Wild | Pattern::Bind(_))
}

fn source_name(symbol: Symbol, symbols: &crate::Symbols) -> &str {
    // Resolution prefixes globals with a module identity separated by `$$`.
    // Barb IDs retain identity, while signatures show each specialization, so
    // the diagnostic name can return to the spelling the programmer wrote.
    let canonical = symbols.text(symbol);
    canonical
        .rsplit_once("$$")
        .map_or(canonical, |(_, spelling)| spelling)
}

fn type_name(ty: &Type, symbols: &crate::Symbols) -> String {
    match ty {
        Type::Named(name, arguments) if arguments.is_empty() => {
            source_name(*name, symbols).to_string()
        }
        Type::Named(name, arguments) => format!(
            "{}<{}>",
            source_name(*name, symbols),
            arguments
                .iter()
                .map(|argument| type_name(argument, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Function(parameters, result) => format!(
            "({}) -> {}",
            parameters
                .iter()
                .map(|parameter| type_name(parameter, symbols))
                .collect::<Vec<_>>()
                .join(", "),
            type_name(result, symbols)
        ),
        Type::Variants(tags) => format!(
            "[{}]",
            tags.iter()
                .map(|(label, fields)| if fields.is_empty() {
                    symbols.text(*label).to_owned()
                } else {
                    format!(
                        "{}({})",
                        symbols.text(*label),
                        fields
                            .iter()
                            .map(|field| type_name(field, symbols))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                })
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Type::Tuple(members) => format!(
            "({})",
            members
                .iter()
                .map(|member| type_name(member, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, ty)| format!(
                    "{}: {}",
                    source_name(*name, symbols),
                    type_name(ty, symbols)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn function_name(key: &FunctionKey, symbols: &crate::Symbols) -> String {
    let name = source_name(key.name, symbols);
    match key.instance {
        specialize::Instance::Lambda(_) => format!("lambda in {name}"),
        specialize::Instance::Written | specialize::Instance::Called(_) => name.to_owned(),
    }
}

fn error(message: impl Into<String>) -> LowerError {
    LowerError {
        message: message.into(),
        at: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn checked_example(name: &str) -> CheckedProgram {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        let loaded = crate::modules::load_program(&entry, &root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = crate::resolve::resolve_names(loaded).unwrap();
        crate::check::type_check(resolved, prelude).unwrap()
    }

    /// The example's own definition spelled `suffix`, not the standard
    /// library's.
    fn named(checked: &CheckedProgram, suffix: &str) -> Symbol {
        checked
            .types
            .values
            .keys()
            .copied()
            .find(|symbol| {
                let text = checked.resolved.symbols.text(*symbol);
                text.ends_with(suffix) && !text.starts_with("Mstd_")
            })
            .unwrap()
    }

    #[test]
    fn lowers_literals_to_valid_barb() {
        let checked = checked_example("literals.fn");
        for suffix in ["$$natural", "$$integer", "$$text"] {
            let entry = named(&checked, suffix);
            let program = program(&checked, entry).unwrap();
            barb::validate(&program).unwrap();
        }
    }

    #[test]
    fn lowers_the_host_entry_through_the_machine_boundary() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/main.fn");
        let loaded = crate::modules::load_program(&entry, &root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let host = crate::host::HostIds::find_in(&loaded).unwrap();
        let main = crate::host::Main::find_in(&loaded).unwrap().unwrap();
        let resolved = crate::resolve::resolve_names(loaded).unwrap();
        let checked = crate::check::type_check(resolved, prelude).unwrap();
        crate::check::check_application_abi(&checked, &host, &main).unwrap();
        for bits in [16, 32, 64] {
            let routines = faun_core::platform::Routines::builtin().with_word(bits);
            let specialized =
                specialize::monomorphize_package(&checked, &host, Some(&main)).unwrap();
            let first_order = crate::first_order::first_order(specialized);
            let mut program = lower_package_to_barb(&checked, first_order, &routines).unwrap();
            barb::optimize(&mut program);
            let rendered = program.render();
            // `Host` holds what its target hands the program; `main!` is the
            // entry as written, and a routine is asked with the `Host` it
            // was handed, as the source says.
            assert!(
                rendered.contains("\nHost = Host(args: List<Str>)\n"),
                "{rendered}"
            );
            assert!(rendered.contains("main!(v0: Host) -> [] ="), "{rendered}");
            assert!(rendered.contains("Host.exit!(v0: Host, v1: Nat) -> [] = <elsewhere>"));
            assert!(rendered.contains("Host.exit!(v0, v2)"), "{rendered}");
            assert!(!rendered.contains("start"));
            assert!(!rendered.contains('$'));
            let machine = faun_core::lower_to_machine_ir(&mut program.clone(), &routines).unwrap();
            // A program reading only how many arguments it has is handed
            // `argc` alone, into the entry's frame, as wide as its word.
            let entry = machine.entry();
            assert_eq!(machine.parameter_names(entry).collect::<Vec<_>>(), ["argc"]);
            let body = machine.function(entry).body().unwrap();
            let argc = machine.values(machine.region(body).params)[0];
            assert_eq!(machine.class(argc), faun_core::ir::Class::fixed(bits));
            let rendered = machine.render();
            assert!(rendered.contains("call exit!(v0)"), "{rendered}");
        }
    }

    #[test]
    fn folds_standard_division_remainder_and_their_zero_cases() {
        let checked = checked_example("arithmetic.fn");
        for (suffix, expected) in [("$$natural_arithmetic", 14), ("$$signed_arithmetic", 10)] {
            let entry = named(&checked, suffix);
            let mut program = program(&checked, entry).unwrap();
            barb::optimize(&mut program);
            barb::validate(&program).unwrap();
            let body = program.function(program.entry().unwrap()).body().unwrap();
            let barb::Expr::Static(value) = program.expr(body.tail) else {
                panic!("{suffix} did not fold\n{}", program.render());
            };
            let barb::ConstantView::Natural(value) = program.constant(value).view() else {
                panic!("{suffix} did not return a natural");
            };
            assert_eq!(value.try_u64(), Ok(expected));
        }
    }

    #[test]
    fn specializes_polymorphic_data_and_lambdas_for_their_callbacks() {
        let checked = checked_example("utilities.fn");
        for suffix in ["$$mapped", "$$combined", "$$signed_sum"] {
            let entry = named(&checked, suffix);
            let program = program(&checked, entry).unwrap();
            barb::validate(&program).unwrap();
        }
        let choose = named(&checked, "$$choose");
        assert!(program(&checked, choose).is_err());

        let checked = checked_example("lowering.fn");
        for suffix in [
            "$$multi_specialized",
            "$$mapped_global",
            "$$mapped_capture",
            "$$wrapped",
            "$$wrapped_each",
            "$$from_external",
            "$$guarded_entry",
            "$$record_entry",
        ] {
            let entry = named(&checked, suffix);
            let program = program(&checked, entry).unwrap();
            barb::validate(&program).unwrap();
            if suffix == "$$record_entry" {
                let rendered = program.render();
                assert!(rendered.find("= 22").unwrap() < rendered.find("= 20").unwrap());
            }
        }
    }
}
