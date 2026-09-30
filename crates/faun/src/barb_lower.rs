//! Emit pattern-compiled decisions as Barb declarations and bodies.
//!
//! Source patterns and clause selection are gone before this pass. The emitter
//! assigns Barb IDs, chooses constructor layouts and records diagnostic sites.

#![allow(clippy::too_many_lines)]

use std::collections::{BTreeSet, HashMap};

use faun_core::barb::{self, Atom, Builder, CtorId, FnId, TypeId};

use crate::blessed::PreludeIds;
use crate::check::CheckedProgram;
use crate::diagnostic::{Diagnostic, LowerError};
use crate::first_order::{Expr, ExprKind};
use crate::hir::LocalId;
use crate::pattern_compile::{self as p, Decision, Unpack, Value};
use crate::resolve::ResolvedProgram;
use crate::specialize::{self, FunctionKey, Type};
use crate::{ModuleId, Symbol};

/// Specialize what `entry`, a monomorphic parameterless function, reaches
/// and emit Barb, for a test to read one definition's lowering.
#[cfg(test)]
fn program(checked: &CheckedProgram, entry: Symbol) -> Result<barb::Program, LowerError> {
    let specialized = specialize::monomorphize_from_entry(checked, entry)?;
    crate::second_class::check(&specialized, &checked.resolved.package)?;
    let program = crate::callbacks::lower(specialized)?;
    let program = p::compile(program, &checked.prelude, &checked.resolved.symbols)?;
    Lowerer::new(checked, None, program)?.lower()
}

/// Emit a pattern-compiled package as Barb, starting at its `main! : Host -> []`
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
    program: p::Program,
    routines: &faun_core::platform::Routines,
) -> Result<barb::Program, Diagnostic> {
    Lowerer::new(checked, Some(routines), program)
        .and_then(Lowerer::lower)
        .map_err(|error| checked.resolved.told(error))
}

/// How a widening rebuilds each constructor, or a product's fields.
type Widening = Vec<(Option<Symbol>, Vec<(Type, Type)>)>;

struct Lowerer<'a> {
    resolved: &'a ResolvedProgram<crate::typed::Program>,
    prelude: &'a PreludeIds,
    /// The target's routines, present when lowering an application.
    routines: Option<&'a faun_core::platform::Routines>,
    program: p::Program,
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
    /// Whether two naturals are equal, written once where a numeral is
    /// matched, in the shape Barb recognizes as that comparison.
    numeral_equals: Option<FnId>,
    output: barb::Program,
}

impl<'a> Lowerer<'a> {
    fn new(
        checked: &'a CheckedProgram,
        routines: Option<&'a faun_core::platform::Routines>,
        program: p::Program,
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
            numeral_equals: None,
            output: barb::Program::default(),
        };
        lowerer.discover()?;
        Ok(lowerer)
    }

    fn lower(mut self) -> Result<barb::Program, LowerError> {
        self.declare_types();
        self.define_types()?;
        self.declare_functions();
        self.define_functions();
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

    /// A refusal, placed at the definition it names.
    fn refused(&self, refusal: barb::Refusal) -> LowerError {
        let definition = refusal.function.and_then(|function| {
            let (key, _) = self.function_ids.iter().find(|(_, id)| **id == function)?;
            self.definition_site(key.name)
        });
        LowerError::new(refusal.message, definition)
    }

    /// Where the first clause defining `name` is written.
    fn definition_site(&self, name: Symbol) -> Option<(ModuleId, crate::ast::Span)> {
        self.resolved
            .program
            .functions
            .iter()
            .find(|function| function.name == name)
            .map(|function| (function.module, function.span))
    }

    /// Find every type the program holds, each of which Barb declares.
    fn discover(&mut self) -> Result<(), LowerError> {
        let functions = std::mem::take(&mut self.program.functions);
        let found = self.discover_in(&functions);
        self.program.functions = functions;
        found
    }

    fn discover_in(&mut self, functions: &[p::Function]) -> Result<(), LowerError> {
        for function in functions {
            let parameters = &function.key.signature.parameters;
            let result = function.key.signature.result.as_ref();
            for parameter in parameters {
                self.collect_type(parameter)?;
            }
            self.collect_type(result)?;
            if let p::Definition::Body(decision) = &function.definition {
                self.collect_decision(decision, result)?;
            }
        }
        loop {
            let before = self.types.len();
            let types: Vec<_> = self.types.iter().cloned().collect();
            for ty in types {
                if let Type::Named(name, _) = &ty {
                    let constructors = ty.constructors(&self.program.data)?;
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

    fn collect_decision(&mut self, decision: &Decision, answer: &Type) -> Result<(), LowerError> {
        match decision {
            Decision::Body { body, .. } => {
                for binding in &body.bindings {
                    self.collect_expr(&binding.value, answer)?;
                }
                self.collect_expr(&body.result, answer)?;
            }
            Decision::Match { owner, arms, .. } => {
                self.collect_type(owner)?;
                for arm in arms {
                    self.collect_decision(&arm.decision, answer)?;
                }
            }
            Decision::Record {
                owner, decision, ..
            } => {
                self.collect_type(owner)?;
                self.collect_decision(decision, answer)?;
            }
            Decision::Guard {
                condition,
                otherwise,
                answer: yes,
                ..
            } => {
                for binding in &condition.bindings {
                    self.collect_expr(&binding.value, answer)?;
                }
                self.collect_expr(&condition.result, answer)?;
                self.collect_decision(otherwise, answer)?;
                self.collect_decision(yes, answer)?;
            }
            Decision::Numeral {
                equal, otherwise, ..
            } => {
                self.collect_type(&Type::Named(self.prelude.bool_, Vec::new()))?;
                self.collect_decision(equal, answer)?;
                self.collect_decision(otherwise, answer)?;
            }
        }
        Ok(())
    }

    fn collect_expr(&mut self, expression: &Expr, answer: &Type) -> Result<(), LowerError> {
        self.collect_type(&expression.ty)?;
        match &expression.kind {
            ExprKind::Block(_) => unreachable!("pattern compiling takes a block's bindings out"),
            ExprKind::Local(_) | ExprKind::Natural(_) | ExprKind::Bytes(_) => {}
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
        if let (Some(source), Some(target)) = (from.members(), to.members()) {
            return Ok(vec![(None, source.into_iter().zip(target).collect())]);
        }
        let target = to.constructors(&self.program.data)?;
        from.constructors(&self.program.data)?
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
                    let constructors = ty.constructors(&self.program.data)?;
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

    /// The IEEE 754 operation `key` computes, where it is one of the
    /// standard floats' own, at the float's type: the one place a float's
    /// meaning is taken from its name, since no equation says it.
    fn float(&self, key: &FunctionKey) -> Option<faun_core::float::Float> {
        let parameters = &key.signature.parameters;
        self.prelude.floats.iter().find_map(|float| {
            let (_, operation) = float
                .operations
                .iter()
                .find(|(method, _)| *method == key.name)?;
            parameters
                .iter()
                .all(|ty| matches!(ty, Type::Named(name, arguments) if *name == float.ty && arguments.is_empty()))
                .then_some(faun_core::float::Float {
                    operation: *operation,
                    format: float.format,
                })
        })
    }

    fn declare_functions(&mut self) {
        for function in &self.program.functions {
            let parameters = &function.key.signature.parameters;
            let result = function.key.signature.result.as_ref();
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
            if let p::Definition::External(provider) = function.definition {
                let provider = self.resolved.symbols.text(provider);
                self.output.answered_by(id, provider);
            }
            if let Some(float) = self.float(&function.key) {
                self.output.claim(id, float);
            }
            self.function_ids.insert(function.key.clone(), id);
        }
        for (from, to) in &self.widenings {
            let id = self
                .output
                .declare("widen", &[self.type_ids[from]], self.type_ids[to]);
            self.widen_ids.insert((from.clone(), to.clone()), id);
        }
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

    fn define_functions(&mut self) {
        let functions = std::mem::take(&mut self.program.functions);
        for function in functions {
            let p::Definition::Body(decision) = function.definition else {
                continue;
            };
            if decision.tests_numerals() && self.numeral_equals.is_none() {
                self.numeral_equals = Some(self.define_numeral_equals());
            }
            let function_id = self.function_ids[&function.key];
            let answer = &function.key.signature.result;
            let context = EmitContext {
                type_ids: &self.type_ids,
                constructor_ids: &self.constructor_ids,
                record_constructor_ids: &self.record_constructor_ids,
                record_wrappers: &self.record_wrappers,
                function_ids: &self.function_ids,
                widen_ids: &self.widen_ids,
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
}

struct EmitContext<'a> {
    type_ids: &'a HashMap<Type, TypeId>,
    constructor_ids: &'a HashMap<(Symbol, Type), CtorId>,
    record_constructor_ids: &'a HashMap<Type, CtorId>,
    record_wrappers: &'a HashMap<Type, Type>,
    function_ids: &'a HashMap<FunctionKey, FnId>,
    widen_ids: &'a HashMap<(Type, Type), FnId>,
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
            let condition = emit_body(context, builder, condition, locals);
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
    body: &p::Body,
    locals: HashMap<LocalId, Atom>,
) -> Atom {
    emit_bindings(context, builder, &body.bindings, &body.result, locals)
}

/// Emit bindings in order, then the answer. A binding of `value?` takes the
/// value apart: its `Ok` goes on to the rest of the body, and its `Err` is
/// what this answers, at once.
fn emit_bindings(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    bindings: &[p::Binding],
    result: &Expr,
    mut locals: HashMap<LocalId, Atom>,
) -> Atom {
    let Some((binding, rest)) = bindings.split_first() else {
        return emit_expr(context, builder, result, &locals);
    };
    let bind = |locals: &mut HashMap<LocalId, Atom>, value| match binding.unpack {
        Unpack::Ignore => {}
        Unpack::Bind(local) => {
            locals.insert(local, value);
        }
        Unpack::Fields { .. } => unreachable!("an unpack is emitted by `destructure`"),
    };
    let ExprKind::Try(taken) = &binding.value.kind else {
        let value = emit_expr(context, builder, &binding.value, &locals);
        if !matches!(binding.unpack, Unpack::Ignore | Unpack::Bind(_)) {
            return destructure(
                context,
                builder,
                value,
                &binding.unpack,
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

/// Execute an unpack already validated and ordered by pattern compilation.
fn destructure(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    value: Atom,
    unpack: &Unpack,
    mut locals: HashMap<LocalId, Atom>,
    then: &dyn Fn(&mut Builder<'_>, HashMap<LocalId, Atom>) -> Atom,
) -> Atom {
    match unpack {
        Unpack::Ignore => then(builder, locals),
        Unpack::Bind(local) => {
            locals.insert(*local, value);
            then(builder, locals)
        }
        Unpack::Fields { owner, fields } => {
            builder.match_(value, context.type_ids[owner], |builder, _, held| {
                let held = context.arm_fields(builder, owner, held);
                destructure_each(context, builder, &held, fields, locals.clone(), then)
            })
        }
    }
}

fn destructure_each(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    held: &[Atom],
    fields: &[Unpack],
    locals: HashMap<LocalId, Atom>,
    then: &dyn Fn(&mut Builder<'_>, HashMap<LocalId, Atom>) -> Atom,
) -> Atom {
    let (Some((&value, held)), Some((unpack, fields))) = (held.split_first(), fields.split_first())
    else {
        return then(builder, locals);
    };
    destructure(
        context,
        builder,
        value,
        unpack,
        locals,
        &|builder, locals| destructure_each(context, builder, held, fields, locals, then),
    )
}

fn emit_expr(
    context: &EmitContext<'_>,
    builder: &mut Builder<'_>,
    expression: &Expr,
    locals: &HashMap<LocalId, Atom>,
) -> Atom {
    match &expression.kind {
        ExprKind::Block(_) => unreachable!("pattern compiling takes a block's bindings out"),
        ExprKind::Local(local) => locals[local],
        ExprKind::Natural(magnitude) => {
            let nat = context.type_ids[&Type::Named(context.prelude.nat, Vec::new())];
            let constant = builder
                .natural(nat, magnitude)
                .expect("the Nat shape was validated before emission");
            builder.known(constant)
        }
        ExprKind::Bytes(bytes) => {
            let list = context.type_ids[&expression.ty];
            let constant = builder
                .bytes(list, bytes)
                .expect("a byte list's shape was validated before emission");
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
            builder.call(context.function_ids[key], &arguments)
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
        Type::Function(signature) => format!(
            "({}) -> {}",
            signature
                .parameters
                .iter()
                .map(|parameter| type_name(parameter, symbols))
                .collect::<Vec<_>>()
                .join(", "),
            type_name(&signature.result, symbols)
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
    LowerError::new(message.into(), None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn checked_example(name: &str) -> CheckedProgram {
        let root = crate::standard_path();
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        let loaded = crate::modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = crate::resolve::resolve_names(loaded).unwrap();
        crate::check::type_check(crate::declarations::normalize(resolved), prelude).unwrap()
    }

    /// The example's own definition spelled `suffix`, not the standard
    /// library's.
    fn named(checked: &CheckedProgram, suffix: &str) -> Symbol {
        checked
            .resolved
            .program
            .functions
            .iter()
            .map(|function| function.name)
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
        let root = crate::standard_path();
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/main.fn");
        let loaded = crate::modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let host = crate::host::HostIds::find_in(&loaded).unwrap();
        let main = crate::host::Main::find_in(&loaded).unwrap().unwrap();
        let resolved = crate::resolve::resolve_names(loaded).unwrap();
        let checked =
            crate::check::type_check(crate::declarations::normalize(resolved), prelude).unwrap();
        crate::check::check_application_abi(&checked, &host, &main).unwrap();
        for bits in [16, 32, 64] {
            let routines = faun_core::platform::Routines::builtin().with_word(bits);
            let specialized =
                specialize::monomorphize_package(&checked, &host, Some(&main)).unwrap();
            crate::second_class::check(&specialized, &checked.resolved.package).unwrap();
            let program = crate::callbacks::lower(specialized).unwrap();
            let program = p::compile(program, &checked.prelude, &checked.resolved.symbols).unwrap();
            let mut program = lower_package_to_barb(&checked, program, &routines).unwrap();
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
            assert!(rendered.contains("Host.exit!(v0: Host, v1: U8) -> [] = <elsewhere>"));
            assert!(rendered.contains("Host.exit!(v0, v5)"), "{rendered}");
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
            // A status is a byte, so the count is taken modulo 256 where the
            // program says so, rather than by whatever the target keeps.
            let rendered = machine.render();
            assert!(rendered.contains("= convert v0 to 0..255"), "{rendered}");
            assert!(rendered.contains("call exit!(v1)"), "{rendered}");
        }
    }

    #[test]
    fn folds_standard_division_remainder_and_their_zero_cases() {
        let checked = checked_example("arithmetic.fn");
        for (suffix, expected) in [("$$natural_arithmetic", 14), ("$$signed_arithmetic", 8)] {
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
