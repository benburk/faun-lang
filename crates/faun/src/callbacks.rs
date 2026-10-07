//! Specialize each definition for the callbacks it is handed, as Ori does.
//!
//! Functions are second class, so every function value is known where it
//! is passed: a global, a constructor, a lambda written there, or a callback
//! the caller was itself handed. A definition taking a function is made
//! once for each set of callbacks it is called with, and calling its
//! function parameter becomes a direct call of the callback. A lambda
//! becomes a definition of its own, taking what it reads from where it was
//! written ahead of its parameters; what a callback reads travels as
//! arguments in place of the function parameter, so no function value is
//! left for the program to hold.
//!
//! The call graph that remains says exactly which definition calls which,
//! which is what termination checking reads: `bytes.count(|b| vowels.contains(b))`
//! goes round through the lambda only as far as `contains` goes on its own
//! list, rather than through one `apply` shared by every function of a type.
//!
//! What cannot be made finitely is refused: a recursive call that wraps the
//! callback it was handed in a lambda of its own and hands that on, so each
//! round asks for one more definition.

// The passes over expressions are cohesive exhaustive matches, kept whole
// so a new kind of expression shows where it is missed.
#![allow(clippy::too_many_lines)]

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use crate::Symbol;
use crate::diagnostic::{Advised, LowerError};
use crate::first_order as d;
use crate::hir::{LocalId, SiteId};
use crate::specialize::{
    Body, Clause, Definition, Expr, ExprKind, Function, FunctionKey, Instance, Pattern, Program,
    Signature, Type,
};

/// Replace every function value in `program` with the callbacks it stands
/// for, specializing each definition taking one for each set it is handed.
///
/// Return first-order IR directly. The input must have passed
/// [`crate::second_class::check`]; source sites identify lambdas even when
/// generated lambdas share a diagnostic span. Failure exposes no partial output.
pub(crate) fn lower(program: Program) -> Result<d::Program, LowerError> {
    let mut pass = Callbacks::new(&program);
    let mut functions = Vec::with_capacity(program.functions.len());
    for function in &program.functions {
        if takes_function(&function.key) {
            continue;
        }
        let frame = Frame::written(function.key.clone(), function);
        functions.push(pass.function(function.key.clone(), function, &frame, &[])?);
    }
    while let Some((source, callbacks, key)) = pass.queue.pop_front() {
        functions.push(pass.instance(&source, &callbacks, key)?);
    }
    Ok(d::Program {
        entry: program.entry,
        functions,
        data: program.data,
    })
}

/// What a function value is, where it is known.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Callback {
    Function(FunctionKey),
    /// A constructor, and the function type it is used at.
    Constructor(Symbol, Type),
    Lambda(Box<LambdaCallback>),
}

/// A lambda written in `owner` at `site`, for the callbacks its function
/// captures are.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LambdaCallback {
    owner: FunctionKey,
    site: SiteId,
    callbacks: Vec<Callback>,
}

impl Callback {
    /// Whether the lambda written at `site` in `owner` is this callback or
    /// among the callbacks it holds, as a callback wrapping one it was
    /// handed is.
    fn holds(&self, owner: &FunctionKey, site: SiteId) -> bool {
        let Self::Lambda(lambda) = self else {
            return false;
        };
        (lambda.owner == *owner && lambda.site == site)
            || lambda.callbacks.iter().any(|held| held.holds(owner, site))
    }
}

/// What a definition is made from: one written, or a lambda written in one.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Source {
    Written(FunctionKey),
    Lambda(FunctionKey, SiteId),
}

/// A lambda as written: its parameters, its body and its function type.
struct LambdaSite<'a> {
    patterns: &'a [Pattern],
    body: &'a Expr,
    ty: &'a Type,
}

/// A definition being made: the definition its body was written in, the
/// callback and carried locals of each of its function locals, and the
/// next local no one has.
struct Frame {
    owner: FunctionKey,
    functions: HashMap<LocalId, (Callback, Vec<(LocalId, Type)>)>,
    next: u32,
}

impl Frame {
    fn written(owner: FunctionKey, function: &Function) -> Self {
        let mut highest = 0;
        if let Definition::Body(clauses) = &function.definition {
            for clause in clauses {
                highest = highest.max(clause_highest(clause));
            }
        }
        Self {
            owner,
            functions: HashMap::new(),
            next: highest + 1,
        }
    }

    /// A frame for another clause of the same definition.
    fn again(&self) -> Self {
        Self {
            owner: self.owner.clone(),
            functions: HashMap::new(),
            next: self.next,
        }
    }

    /// Fresh locals for what `callback` carries.
    fn carry(&mut self, callback: &Callback, lambdas: &Lambdas) -> Vec<(LocalId, Type)> {
        carried(callback, lambdas)
            .into_iter()
            .map(|ty| {
                let local = LocalId(self.next);
                self.next += 1;
                (local, ty)
            })
            .collect()
    }

    /// The parameters taking what `callback` carries in place of the
    /// function `pattern` took, which names it here, if it names it.
    fn bind(
        &mut self,
        pattern: &Pattern,
        callback: &Callback,
        lambdas: &Lambdas,
        parameters: &mut Vec<Pattern>,
    ) {
        let carried = self.carry(callback, lambdas);
        if let Pattern::Bind(local) | Pattern::As(local, _) = pattern {
            parameters.extend(carried.iter().map(|(local, _)| Pattern::Bind(*local)));
            self.functions.insert(*local, (callback.clone(), carried));
        } else {
            parameters.extend(carried.iter().map(|_| Pattern::Wild));
        }
    }
}

/// What a call hands on: the callbacks among its arguments, in order, and
/// the arguments with what each carries in its place.
struct Handed {
    callbacks: Vec<Callback>,
    arguments: Vec<d::Expr>,
}

impl Handed {
    fn types(&self) -> Vec<Type> {
        self.arguments.iter().map(|each| each.ty.clone()).collect()
    }
}

type Lambdas<'a> = HashMap<(FunctionKey, SiteId), LambdaSite<'a>>;

struct Callbacks<'a> {
    functions: HashMap<&'a FunctionKey, &'a Function>,
    lambdas: Lambdas<'a>,
    made: HashMap<(Source, Vec<Callback>), FunctionKey>,
    queue: VecDeque<(Source, Vec<Callback>, FunctionKey)>,
    next: u32,
}

impl<'a> Callbacks<'a> {
    fn new(program: &'a Program) -> Self {
        let mut lambdas = HashMap::new();
        for function in &program.functions {
            let Definition::Body(clauses) = &function.definition else {
                continue;
            };
            for clause in clauses {
                let mut found = |expression: &'a Expr| {
                    if let ExprKind::Lambda(site, patterns, body) = &expression.kind {
                        lambdas
                            .entry((function.key.clone(), *site))
                            .or_insert(LambdaSite {
                                patterns,
                                body,
                                ty: &expression.ty,
                            });
                    }
                };
                for_each_in_clause(clause, &mut found);
            }
        }
        Self {
            functions: program
                .functions
                .iter()
                .map(|function| (&function.key, function))
                .collect(),
            lambdas,
            made: HashMap::new(),
            queue: VecDeque::new(),
            next: 0,
        }
    }

    /// The definition `source` makes for `callbacks`, asked for once.
    fn request(
        &mut self,
        source: Source,
        callbacks: Vec<Callback>,
        signature: Signature,
    ) -> FunctionKey {
        if let Some(key) = self.made.get(&(source.clone(), callbacks.clone())) {
            return key.clone();
        }
        self.next += 1;
        let (name, instance) = match &source {
            Source::Written(key) => (key.name, Instance::Called(self.next)),
            Source::Lambda(owner, _) => (owner.name, Instance::Lambda(self.next)),
        };
        let key = FunctionKey {
            name,
            signature,
            instance,
        };
        self.made
            .insert((source.clone(), callbacks.clone()), key.clone());
        self.queue.push_back((source, callbacks, key.clone()));
        key
    }

    /// Make the definition `key` from `source` for `callbacks`.
    fn instance(
        &mut self,
        source: &Source,
        callbacks: &[Callback],
        key: FunctionKey,
    ) -> Result<d::Function, LowerError> {
        match source {
            Source::Written(written) => {
                let function = self.functions[written];
                let frame = Frame::written(written.clone(), function);
                self.function(key, function, &frame, callbacks)
            }
            Source::Lambda(owner, site) => self.lambda(key, owner, *site, callbacks),
        }
    }

    /// `function`'s clauses as `key`, each function parameter replaced by
    /// what the next of `callbacks` carries.
    fn function(
        &mut self,
        key: FunctionKey,
        function: &Function,
        frame: &Frame,
        callbacks: &[Callback],
    ) -> Result<d::Function, LowerError> {
        let written = match &function.definition {
            Definition::External(provider) => {
                return Ok(d::Function {
                    key,
                    definition: d::Definition::External(*provider),
                });
            }
            Definition::Body(clauses) => clauses,
        };
        let parameters = &function.key.signature.parameters;
        let mut clauses = Vec::with_capacity(written.len());
        for clause in written {
            let mut frame = frame.again();
            let mut handed = callbacks.iter();
            let mut patterns = Vec::with_capacity(clause.patterns.len());
            for (pattern, ty) in clause.patterns.iter().zip(parameters) {
                if matches!(ty, Type::Function(..)) {
                    let callback = handed
                        .next()
                        .ok_or_else(|| internal("a callback for each function parameter"))?;
                    frame.bind(pattern, callback, &self.lambdas, &mut patterns);
                } else {
                    patterns.push(pattern.clone());
                }
            }
            clauses.push(d::Clause {
                patterns,
                guard: clause
                    .guard
                    .as_ref()
                    .map(|guard| self.expr(&mut frame, guard))
                    .transpose()?,
                body: self.body(&mut frame, &clause.body)?,
            });
        }
        Ok(d::Function {
            key,
            definition: d::Definition::Body(clauses),
        })
    }

    /// The lambda written at `site` in `owner` as `key`: what it reads from
    /// where it was written first, then its parameters, a function among
    /// either replaced by what the next of `callbacks` carries.
    fn lambda(
        &mut self,
        key: FunctionKey,
        owner: &FunctionKey,
        site: SiteId,
        callbacks: &[Callback],
    ) -> Result<d::Function, LowerError> {
        let lambda = &self.lambdas[&(owner.clone(), site)];
        let (patterns, body, ty) = (lambda.patterns, lambda.body, lambda.ty);
        let captures = captures(patterns, body);
        let mut highest = expr_highest(body);
        for pattern in patterns {
            highest = highest.max(pattern_highest(pattern));
        }
        for (local, _) in &captures {
            highest = highest.max(local.0);
        }
        let mut frame = Frame {
            owner: owner.clone(),
            functions: HashMap::new(),
            next: highest + 1,
        };
        let mut handed = callbacks.iter();
        let mut parameters = Vec::new();
        for (local, ty) in &captures {
            if matches!(ty, Type::Function(..)) {
                let callback = handed
                    .next()
                    .ok_or_else(|| internal("a callback for each function capture"))?;
                frame.bind(
                    &Pattern::Bind(*local),
                    callback,
                    &self.lambdas,
                    &mut parameters,
                );
            } else {
                parameters.push(Pattern::Bind(*local));
            }
        }
        let Type::Function(signature) = ty else {
            return Err(internal("a lambda of a function type"));
        };
        for (pattern, ty) in patterns.iter().zip(&signature.parameters) {
            if matches!(ty, Type::Function(..)) {
                let callback = handed
                    .next()
                    .ok_or_else(|| internal("a callback for each function parameter"))?;
                frame.bind(pattern, callback, &self.lambdas, &mut parameters);
            } else {
                parameters.push(pattern.clone());
            }
        }
        let result = self.expr(&mut frame, body)?;
        Ok(d::Function {
            key,
            definition: d::Definition::Body(vec![d::Clause {
                patterns: parameters,
                guard: None,
                body: d::Body {
                    bindings: Vec::new(),
                    result,
                },
            }]),
        })
    }

    fn body(&mut self, frame: &mut Frame, body: &Body) -> Result<d::Body, LowerError> {
        let bindings = body
            .bindings
            .iter()
            .map(|binding| {
                Ok(d::Binding {
                    pattern: binding.pattern.clone(),
                    value: self.expr(frame, &binding.value)?,
                })
            })
            .collect::<Result<_, LowerError>>()?;
        Ok(d::Body {
            bindings,
            result: self.expr(frame, &body.result)?,
        })
    }

    fn exprs(&mut self, frame: &mut Frame, list: &[Expr]) -> Result<Vec<d::Expr>, LowerError> {
        list.iter().map(|each| self.expr(frame, each)).collect()
    }

    fn expr(&mut self, frame: &mut Frame, expression: &Expr) -> Result<d::Expr, LowerError> {
        let kind = match &expression.kind {
            ExprKind::Block(body) => d::ExprKind::Block(Box::new(self.body(frame, body)?)),
            ExprKind::Local(local) if frame.functions.contains_key(local) => {
                return Err(located(
                    expression,
                    "a function may only be passed straight into a call",
                ));
            }
            ExprKind::Function(_) | ExprKind::ConstructorFunction(_) | ExprKind::Lambda(..) => {
                return Err(located(
                    expression,
                    "a function may only be passed straight into a call",
                ));
            }
            ExprKind::Local(local) => d::ExprKind::Local(*local),
            ExprKind::Natural(magnitude) => d::ExprKind::Natural(magnitude.clone()),
            ExprKind::Bytes(bytes) => d::ExprKind::Bytes(bytes.clone()),
            ExprKind::Construct(constructor, fields) => {
                d::ExprKind::Construct(*constructor, self.exprs(frame, fields)?)
            }
            ExprKind::Record(fields) => d::ExprKind::Record(
                fields
                    .iter()
                    .map(|(name, field)| Ok((*name, self.expr(frame, field)?)))
                    .collect::<Result<_, LowerError>>()?,
            ),
            ExprKind::Update(base, fields) => d::ExprKind::Update(
                Box::new(self.expr(frame, base)?),
                fields
                    .iter()
                    .map(|(name, field)| Ok((*name, self.expr(frame, field)?)))
                    .collect::<Result<_, LowerError>>()?,
            ),
            ExprKind::Tuple(members) => d::ExprKind::Tuple(self.exprs(frame, members)?),
            ExprKind::Project(receiver, field) => {
                d::ExprKind::Project(Box::new(self.expr(frame, receiver)?), *field)
            }
            ExprKind::Widen(value) => d::ExprKind::Widen(Box::new(self.expr(frame, value)?)),
            ExprKind::Try(value) => d::ExprKind::Try(Box::new(self.expr(frame, value)?)),
            ExprKind::Is(value, rows) => d::ExprKind::Is(
                Box::new(self.expr(frame, value)?),
                rows.iter()
                    .map(|(pattern, guard)| {
                        let guard = guard
                            .as_ref()
                            .map(|guard| self.expr(frame, guard))
                            .transpose()?;
                        Ok((pattern.clone(), guard))
                    })
                    .collect::<Result<_, LowerError>>()?,
            ),
            ExprKind::If(condition, yes, no) => d::ExprKind::If(
                Box::new(self.expr(frame, condition)?),
                Box::new(self.expr(frame, yes)?),
                Box::new(self.expr(frame, no)?),
            ),
            ExprKind::Match(value, arms) => d::ExprKind::Match(
                Box::new(self.expr(frame, value)?),
                arms.iter()
                    .map(|arm| {
                        let rows = arm
                            .rows
                            .iter()
                            .map(|(pattern, guard)| {
                                let guard = guard
                                    .as_ref()
                                    .map(|guard| self.expr(frame, guard))
                                    .transpose()?;
                                Ok((pattern.clone(), guard))
                            })
                            .collect::<Result<_, LowerError>>()?;
                        Ok(d::Arm {
                            rows,
                            body: self.expr(frame, &arm.body)?,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
            ),
            ExprKind::DirectCall(key, arguments) => self.call(frame, key, arguments)?,
            ExprKind::Invoke(head, arguments) => {
                let (callback, carried) = callback(frame, head)?;
                self.invoke(frame, callback, carried, arguments, &expression.ty)?
            }
        };
        Ok(d::Expr {
            module: expression.module,
            span: expression.span,
            ty: expression.ty.clone(),
            kind,
        })
    }

    /// A call of `key`, made for the callbacks among `arguments` where it
    /// takes a function.
    fn call(
        &mut self,
        frame: &mut Frame,
        key: &FunctionKey,
        arguments: &[Expr],
    ) -> Result<d::ExprKind, LowerError> {
        if !takes_function(key) {
            return Ok(d::ExprKind::DirectCall(
                key.clone(),
                self.exprs(frame, arguments)?,
            ));
        }
        let handed = self.hand(frame, arguments)?;
        let signature = Signature {
            parameters: handed.types(),
            result: key.signature.result.clone(),
        };
        let made = self.request(Source::Written(key.clone()), handed.callbacks, signature);
        Ok(d::ExprKind::DirectCall(made, handed.arguments))
    }

    /// Call `callback`, carrying `carried`, with `arguments`.
    fn invoke(
        &mut self,
        frame: &mut Frame,
        callback: Callback,
        carried: Vec<d::Expr>,
        arguments: &[Expr],
        answer: &Type,
    ) -> Result<d::ExprKind, LowerError> {
        match callback {
            Callback::Function(key) => self.call(frame, &key, arguments),
            Callback::Constructor(constructor, _) => Ok(d::ExprKind::Construct(
                constructor,
                self.exprs(frame, arguments)?,
            )),
            Callback::Lambda(lambda) => {
                let handed = self.hand(frame, arguments)?;
                let mut types: Vec<Type> = carried.iter().map(|each| each.ty.clone()).collect();
                types.extend(handed.types());
                let signature = Signature {
                    parameters: types,
                    result: Box::new(answer.clone()),
                };
                let mut callbacks = lambda.callbacks;
                callbacks.extend(handed.callbacks);
                let made = self.request(
                    Source::Lambda(lambda.owner, lambda.site),
                    callbacks,
                    signature,
                );
                let mut passed = carried;
                passed.extend(handed.arguments);
                Ok(d::ExprKind::DirectCall(made, passed))
            }
        }
    }

    /// `arguments` as a call hands them: each function among them as its
    /// callback, and what it carries in its place.
    fn hand(&mut self, frame: &mut Frame, arguments: &[Expr]) -> Result<Handed, LowerError> {
        let mut handed = Handed {
            callbacks: Vec::new(),
            arguments: Vec::with_capacity(arguments.len()),
        };
        for argument in arguments {
            if matches!(argument.ty, Type::Function(..)) {
                let (callback, carried) = callback(frame, argument)?;
                handed.callbacks.push(callback);
                handed.arguments.extend(carried);
            } else {
                handed.arguments.push(self.expr(frame, argument)?);
            }
        }
        Ok(handed)
    }
}

/// The callback a function value is, and what it carries.
fn callback(frame: &Frame, expression: &Expr) -> Result<(Callback, Vec<d::Expr>), LowerError> {
    let local = |(local, ty): &(LocalId, Type)| d::Expr {
        module: expression.module,
        span: expression.span,
        ty: ty.clone(),
        kind: d::ExprKind::Local(*local),
    };
    match &expression.kind {
        ExprKind::Function(key) => Ok((Callback::Function(key.clone()), Vec::new())),
        ExprKind::ConstructorFunction(constructor) => Ok((
            Callback::Constructor(*constructor, expression.ty.clone()),
            Vec::new(),
        )),
        ExprKind::Local(held) => {
            let (callback, carried) = frame
                .functions
                .get(held)
                .ok_or_else(|| located(expression, "a function value no callback is known for"))?;
            Ok((callback.clone(), carried.iter().map(local).collect()))
        }
        ExprKind::Lambda(site, patterns, body) => {
            let site = *site;
            let mut callbacks = Vec::new();
            let mut carried = Vec::new();
            for (captured, ty) in captures(patterns, body) {
                match frame.functions.get(&captured) {
                    Some((callback, held)) => {
                        callbacks.push(callback.clone());
                        carried.extend(held.iter().map(local));
                    }
                    None => carried.push(local(&(captured, ty))),
                }
            }
            if callbacks
                .iter()
                .any(|callback| callback.holds(&frame.owner, site))
            {
                let message = "this lambda wraps the callback it was handed and hands itself on";
                return Err(located(expression, message)
                    .note("each round would ask for another definition, without end")
                    .help("recurse on data that says what to call instead"));
            }
            let lambda = LambdaCallback {
                owner: frame.owner.clone(),
                site,
                callbacks,
            };
            Ok((Callback::Lambda(Box::new(lambda)), carried))
        }
        _ => Err(located(
            expression,
            "a function may only be passed straight into a call",
        )),
    }
}

/// The types of the values `callback` carries in place of a function: what
/// a lambda reads from where it was written, in order, a function among it
/// as what its own callback carries.
fn carried(callback: &Callback, lambdas: &Lambdas) -> Vec<Type> {
    let Callback::Lambda(lambda) = callback else {
        return Vec::new();
    };
    let site = &lambdas[&(lambda.owner.clone(), lambda.site)];
    let mut callbacks = lambda.callbacks.iter();
    let mut types = Vec::new();
    for (_, ty) in captures(site.patterns, site.body) {
        if matches!(ty, Type::Function(..)) {
            if let Some(callback) = callbacks.next() {
                types.extend(carried(callback, lambdas));
            }
        } else {
            types.push(ty);
        }
    }
    types
}

fn takes_function(key: &FunctionKey) -> bool {
    key.signature
        .parameters
        .iter()
        .any(|parameter| matches!(parameter, Type::Function(_)))
}

/// Visit every expression in `clause`, lambdas' bodies included.
fn for_each_in_clause<'a>(clause: &'a Clause, visit: &mut impl FnMut(&'a Expr)) {
    if let Some(guard) = &clause.guard {
        for_each(guard, visit);
    }
    for binding in &clause.body.bindings {
        for_each(&binding.value, visit);
    }
    for_each(&clause.body.result, visit);
}

fn for_each<'a>(expression: &'a Expr, visit: &mut impl FnMut(&'a Expr)) {
    visit(expression);
    match &expression.kind {
        ExprKind::Local(_)
        | ExprKind::Function(_)
        | ExprKind::ConstructorFunction(_)
        | ExprKind::Natural(_)
        | ExprKind::Bytes(_) => {}
        ExprKind::Construct(_, list) | ExprKind::Tuple(list) | ExprKind::DirectCall(_, list) => {
            for each in list {
                for_each(each, visit);
            }
        }
        ExprKind::Record(fields) => {
            for (_, field) in fields {
                for_each(field, visit);
            }
        }
        ExprKind::Update(base, fields) => {
            for_each(base, visit);
            for (_, field) in fields {
                for_each(field, visit);
            }
        }
        ExprKind::Project(value, _) | ExprKind::Widen(value) | ExprKind::Try(value) => {
            for_each(value, visit);
        }
        ExprKind::If(condition, yes, no) => {
            for each in [condition, yes, no] {
                for_each(each, visit);
            }
        }
        ExprKind::Is(value, rows) => {
            for_each(value, visit);
            for guard in rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
                for_each(guard, visit);
            }
        }
        ExprKind::Match(value, arms) => {
            for_each(value, visit);
            for arm in arms {
                for guard in arm.rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
                    for_each(guard, visit);
                }
                for_each(&arm.body, visit);
            }
        }
        ExprKind::Invoke(head, arguments) => {
            for_each(head, visit);
            for each in arguments {
                for_each(each, visit);
            }
        }
        ExprKind::Lambda(_, _, body) => for_each(body, visit),
        ExprKind::Block(body) => {
            for binding in &body.bindings {
                for_each(&binding.value, visit);
            }
            for_each(&body.result, visit);
        }
    }
}

/// The highest local `clause` names anywhere.
fn clause_highest(clause: &Clause) -> u32 {
    let mut highest = clause
        .patterns
        .iter()
        .map(pattern_highest)
        .max()
        .unwrap_or(0);
    for binding in &clause.body.bindings {
        highest = highest.max(pattern_highest(&binding.pattern));
    }
    let mut visit = |expression: &Expr| {
        highest = highest.max(expr_local_highest(expression));
    };
    for_each_in_clause(clause, &mut visit);
    highest
}

fn expr_highest(expression: &Expr) -> u32 {
    let mut highest = 0;
    for_each(expression, &mut |each: &Expr| {
        highest = highest.max(expr_local_highest(each));
    });
    highest
}

/// The highest local `expression` itself names or binds, not its parts'.
fn expr_local_highest(expression: &Expr) -> u32 {
    match &expression.kind {
        ExprKind::Local(local) => local.0,
        ExprKind::Lambda(_, patterns, _) => patterns.iter().map(pattern_highest).max().unwrap_or(0),
        ExprKind::Block(body) => body
            .bindings
            .iter()
            .map(|binding| pattern_highest(&binding.pattern))
            .max()
            .unwrap_or(0),
        _ => 0,
    }
}

fn pattern_highest(pattern: &Pattern) -> u32 {
    match pattern {
        Pattern::Bind(local) => local.0,
        Pattern::As(local, pattern) => local.0.max(pattern_highest(pattern)),
        Pattern::Constructor(_, fields) | Pattern::Product(fields) => {
            fields.iter().map(pattern_highest).max().unwrap_or(0)
        }
        Pattern::List(elements, rest) => elements
            .iter()
            .chain(rest.as_deref())
            .map(pattern_highest)
            .max()
            .unwrap_or(0),
        Pattern::Record(fields) => fields
            .iter()
            .map(|(_, field)| pattern_highest(field))
            .max()
            .unwrap_or(0),
        Pattern::Split(split) => std::iter::once(&split.front)
            .chain(&split.last)
            .map(pattern_highest)
            .max()
            .unwrap_or(0),
        Pattern::Wild
        | Pattern::Number { .. }
        | Pattern::Range
        | Pattern::String
        | Pattern::Ending => 0,
    }
}

fn located(expression: &Expr, message: &str) -> LowerError {
    LowerError::new(message, Some((expression.module, expression.span)))
}

fn internal(what: &str) -> LowerError {
    LowerError::new(format!("callback specialization expected {what}"), None)
}

/// The locals a lambda's body reads that its parameters do not bind.
fn captures(patterns: &[Pattern], body: &Expr) -> Vec<(LocalId, Type)> {
    let mut bound = HashSet::new();
    for pattern in patterns {
        pattern_locals(pattern, &mut bound);
    }
    // What a test binds is bound inside the body, where resolution scoped it.
    for_each(body, &mut |expression| match &expression.kind {
        ExprKind::Is(_, rows) => {
            for (pattern, _) in rows {
                pattern_locals(pattern, &mut bound);
            }
        }
        ExprKind::Match(_, arms) => {
            for (pattern, _) in arms.iter().flat_map(|arm| &arm.rows) {
                pattern_locals(pattern, &mut bound);
            }
        }
        _ => {}
    });
    let mut found = BTreeMap::new();
    free_locals(body, &bound, &mut found);
    found.into_iter().collect()
}

fn free_locals(expression: &Expr, bound: &HashSet<LocalId>, found: &mut BTreeMap<LocalId, Type>) {
    use ExprKind as S;
    match &expression.kind {
        S::Local(local) => {
            if !bound.contains(local) {
                found.entry(*local).or_insert_with(|| expression.ty.clone());
            }
        }
        S::Function(_) | S::ConstructorFunction(_) | S::Natural(_) | S::Bytes(_) => {}
        S::Construct(_, fields) | S::DirectCall(_, fields) | S::Tuple(fields) => {
            for field in fields {
                free_locals(field, bound, found);
            }
        }
        S::Update(base, fields) => {
            free_locals(base, bound, found);
            for (_, field) in fields {
                free_locals(field, bound, found);
            }
        }
        S::Record(fields) => {
            for (_, field) in fields {
                free_locals(field, bound, found);
            }
        }
        S::Project(receiver, _) | S::Widen(receiver) | S::Try(receiver) => {
            free_locals(receiver, bound, found);
        }
        S::If(condition, yes, no) => {
            for each in [condition, yes, no] {
                free_locals(each, bound, found);
            }
        }
        S::Is(value, rows) => {
            free_locals(value, bound, found);
            for guard in rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
                free_locals(guard, bound, found);
            }
        }
        S::Match(value, arms) => {
            free_locals(value, bound, found);
            for arm in arms {
                for guard in arm.rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
                    free_locals(guard, bound, found);
                }
                free_locals(&arm.body, bound, found);
            }
        }
        S::Invoke(head, arguments) => {
            free_locals(head, bound, found);
            for argument in arguments {
                free_locals(argument, bound, found);
            }
        }
        S::Lambda(_, patterns, body) => {
            let mut nested = bound.clone();
            for pattern in patterns {
                pattern_locals(pattern, &mut nested);
            }
            free_locals(body, &nested, found);
        }
        // Each binding's value reads what came before it; what follows
        // reads what it binds.
        S::Block(body) => {
            let mut nested = bound.clone();
            for binding in &body.bindings {
                free_locals(&binding.value, &nested, found);
                pattern_locals(&binding.pattern, &mut nested);
            }
            free_locals(&body.result, &nested, found);
        }
    }
}

fn pattern_locals(pattern: &Pattern, output: &mut HashSet<LocalId>) {
    match pattern {
        Pattern::Bind(local) => {
            output.insert(*local);
        }
        Pattern::As(local, pattern) => {
            output.insert(*local);
            pattern_locals(pattern, output);
        }
        Pattern::Constructor(_, fields)
        | Pattern::List(fields, None)
        | Pattern::Product(fields) => {
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
        Pattern::Record(fields) => {
            for (_, pattern) in fields {
                pattern_locals(pattern, output);
            }
        }
        Pattern::Split(split) => {
            for pattern in std::iter::once(&split.front).chain(&split.last) {
                pattern_locals(pattern, output);
            }
        }
        Pattern::Wild
        | Pattern::Number { .. }
        | Pattern::Range
        | Pattern::String
        | Pattern::Ending => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retains_signatures_and_distinguishes_empty_bodies_from_externals() {
        let mut symbols = crate::Symbols::default();
        let provider = symbols.intern("provider");
        let key = |name| FunctionKey {
            name,
            signature: Signature {
                parameters: vec![Type::empty()],
                result: Box::new(Type::empty()),
            },
            instance: Instance::Written,
        };
        let external = key(symbols.intern("external"));
        let defined = key(symbols.intern("defined"));
        // No clause is needed for an uninhabited parameter. This is a body,
        // not a declaration that asks a provider to supply one.
        let program = lower(Program {
            entry: None,
            functions: vec![
                Function {
                    key: external.clone(),
                    definition: Definition::External(provider),
                },
                Function {
                    key: defined.clone(),
                    definition: Definition::Body(Vec::new()),
                },
            ],
            data: HashMap::new(),
        })
        .unwrap();
        assert!(program.entry.is_none());
        assert_eq!(program.functions.len(), 2);
        assert_eq!(program.functions[0].key, external);
        assert_eq!(program.functions[1].key, defined);
        assert!(
            matches!(program.functions[0].definition, d::Definition::External(found) if found == provider)
        );
        assert!(
            matches!(&program.functions[1].definition, d::Definition::Body(clauses) if clauses.is_empty())
        );
    }
}
