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

use crate::ast::Span;
use crate::hir::LocalId;
use crate::specialize::{
    Binding, Body, Clause, Expr, ExprKind, Function, FunctionKey, Instance, Pattern, Program,
    SpecializeError, Type,
};
use crate::{ModuleId, Symbol};

/// Replace every function value in `program` with the callbacks it stands
/// for, specializing each definition taking one for each set it is handed.
pub(crate) fn specialize(program: Program) -> Result<Program, SpecializeError> {
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
    Ok(Program {
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
    site: (ModuleId, Span),
    callbacks: Vec<Callback>,
}

impl Callback {
    /// Whether the lambda written at `site` in `owner` is this callback or
    /// among the callbacks it holds, as a callback wrapping one it was
    /// handed is.
    fn holds(&self, owner: &FunctionKey, site: (ModuleId, Span)) -> bool {
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
    Lambda(FunctionKey, (ModuleId, Span)),
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
        for clause in &function.clauses {
            highest = highest.max(clause_highest(clause));
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
        if let Pattern::Bind(local) = pattern {
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
    arguments: Vec<Expr>,
}

impl Handed {
    fn types(&self) -> Vec<Type> {
        self.arguments.iter().map(|each| each.ty.clone()).collect()
    }
}

type Lambdas<'a> = HashMap<(FunctionKey, (ModuleId, Span)), LambdaSite<'a>>;

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
            for clause in &function.clauses {
                let mut found = |expression: &'a Expr| {
                    if let ExprKind::Lambda(patterns, body) = &expression.kind {
                        lambdas
                            .entry((function.key.clone(), (expression.module, expression.span)))
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
    fn request(&mut self, source: Source, callbacks: Vec<Callback>, ty: Type) -> FunctionKey {
        if let Some(key) = self.made.get(&(source.clone(), callbacks.clone())) {
            return key.clone();
        }
        self.next += 1;
        let (name, instance) = match &source {
            Source::Written(key) => (key.name, Instance::Called(self.next)),
            Source::Lambda(owner, _) => (owner.name, Instance::Lambda(self.next)),
        };
        let key = FunctionKey { name, ty, instance };
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
    ) -> Result<Function, SpecializeError> {
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
    ) -> Result<Function, SpecializeError> {
        let parameters = function
            .key
            .ty
            .function()
            .map(|(parameters, _)| parameters.to_vec())
            .unwrap_or_default();
        let mut clauses = Vec::with_capacity(function.clauses.len());
        for clause in &function.clauses {
            let mut frame = frame.again();
            let mut handed = callbacks.iter();
            let mut patterns = Vec::with_capacity(clause.patterns.len());
            for (pattern, ty) in clause.patterns.iter().zip(&parameters) {
                if matches!(ty, Type::Function(..)) {
                    let callback = handed
                        .next()
                        .ok_or_else(|| internal("a callback for each function parameter"))?;
                    frame.bind(pattern, callback, &self.lambdas, &mut patterns);
                } else {
                    patterns.push(pattern.clone());
                }
            }
            clauses.push(Clause {
                patterns,
                guard: clause
                    .guard
                    .as_ref()
                    .map(|guard| self.expr(&mut frame, guard))
                    .transpose()?,
                body: self.body(&mut frame, &clause.body)?,
            });
        }
        Ok(Function {
            key,
            clauses,
            provider: function.provider,
        })
    }

    /// The lambda written at `site` in `owner` as `key`: what it reads from
    /// where it was written first, then its parameters, a function among
    /// either replaced by what the next of `callbacks` carries.
    fn lambda(
        &mut self,
        key: FunctionKey,
        owner: &FunctionKey,
        site: (ModuleId, Span),
        callbacks: &[Callback],
    ) -> Result<Function, SpecializeError> {
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
        let (types, _) = ty
            .function()
            .ok_or_else(|| internal("a lambda of a function type"))?;
        for (pattern, ty) in patterns.iter().zip(types) {
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
        Ok(Function {
            key,
            clauses: vec![Clause {
                patterns: parameters,
                guard: None,
                body: Body {
                    bindings: Vec::new(),
                    result,
                },
            }],
            provider: None,
        })
    }

    fn body(&mut self, frame: &mut Frame, body: &Body) -> Result<Body, SpecializeError> {
        let bindings = body
            .bindings
            .iter()
            .map(|binding| {
                Ok(Binding {
                    pattern: binding.pattern.clone(),
                    value: self.expr(frame, &binding.value)?,
                })
            })
            .collect::<Result<_, SpecializeError>>()?;
        Ok(Body {
            bindings,
            result: self.expr(frame, &body.result)?,
        })
    }

    fn exprs(&mut self, frame: &mut Frame, list: &[Expr]) -> Result<Vec<Expr>, SpecializeError> {
        list.iter().map(|each| self.expr(frame, each)).collect()
    }

    fn expr(&mut self, frame: &mut Frame, expression: &Expr) -> Result<Expr, SpecializeError> {
        let kind = match &expression.kind {
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
            ExprKind::Local(local) => ExprKind::Local(*local),
            ExprKind::Natural(magnitude) => ExprKind::Natural(magnitude.clone()),
            ExprKind::Bytes(bytes) => ExprKind::Bytes(bytes.clone()),
            ExprKind::Construct(constructor, fields) => {
                ExprKind::Construct(*constructor, self.exprs(frame, fields)?)
            }
            ExprKind::Record(fields) => ExprKind::Record(
                fields
                    .iter()
                    .map(|(name, field)| Ok((*name, self.expr(frame, field)?)))
                    .collect::<Result<_, SpecializeError>>()?,
            ),
            ExprKind::Update(base, fields) => ExprKind::Update(
                Box::new(self.expr(frame, base)?),
                fields
                    .iter()
                    .map(|(name, field)| Ok((*name, self.expr(frame, field)?)))
                    .collect::<Result<_, SpecializeError>>()?,
            ),
            ExprKind::Tuple(members) => ExprKind::Tuple(self.exprs(frame, members)?),
            ExprKind::Project(receiver, field) => {
                ExprKind::Project(Box::new(self.expr(frame, receiver)?), *field)
            }
            ExprKind::Widen(value) => ExprKind::Widen(Box::new(self.expr(frame, value)?)),
            ExprKind::Try(value) => ExprKind::Try(Box::new(self.expr(frame, value)?)),
            ExprKind::DirectCall(key, arguments) => self.call(frame, key, arguments)?,
            ExprKind::Invoke(head, arguments) => {
                let (callback, carried) = callback(frame, head)?;
                self.invoke(frame, callback, carried, arguments, &expression.ty)?
            }
        };
        Ok(Expr {
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
    ) -> Result<ExprKind, SpecializeError> {
        if !takes_function(key) {
            return Ok(ExprKind::DirectCall(
                key.clone(),
                self.exprs(frame, arguments)?,
            ));
        }
        let handed = self.hand(frame, arguments)?;
        let result = key
            .ty
            .function()
            .map(|(_, result)| result.clone())
            .ok_or_else(|| internal("a called definition of a function type"))?;
        let ty = Type::Function(handed.types(), Box::new(result));
        let made = self.request(Source::Written(key.clone()), handed.callbacks, ty);
        Ok(ExprKind::DirectCall(made, handed.arguments))
    }

    /// Call `callback`, carrying `carried`, with `arguments`.
    fn invoke(
        &mut self,
        frame: &mut Frame,
        callback: Callback,
        carried: Vec<Expr>,
        arguments: &[Expr],
        answer: &Type,
    ) -> Result<ExprKind, SpecializeError> {
        match callback {
            Callback::Function(key) => self.call(frame, &key, arguments),
            Callback::Constructor(constructor, _) => Ok(ExprKind::Construct(
                constructor,
                self.exprs(frame, arguments)?,
            )),
            Callback::Lambda(lambda) => {
                let handed = self.hand(frame, arguments)?;
                let mut types: Vec<Type> = carried.iter().map(|each| each.ty.clone()).collect();
                types.extend(handed.types());
                let ty = Type::Function(types, Box::new(answer.clone()));
                let mut callbacks = lambda.callbacks;
                callbacks.extend(handed.callbacks);
                let made = self.request(Source::Lambda(lambda.owner, lambda.site), callbacks, ty);
                let mut passed = carried;
                passed.extend(handed.arguments);
                Ok(ExprKind::DirectCall(made, passed))
            }
        }
    }

    /// `arguments` as a call hands them: each function among them as its
    /// callback, and what it carries in its place.
    fn hand(&mut self, frame: &mut Frame, arguments: &[Expr]) -> Result<Handed, SpecializeError> {
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
fn callback(frame: &Frame, expression: &Expr) -> Result<(Callback, Vec<Expr>), SpecializeError> {
    let local = |(local, ty): &(LocalId, Type)| Expr {
        module: expression.module,
        span: expression.span,
        ty: ty.clone(),
        kind: ExprKind::Local(*local),
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
        ExprKind::Lambda(patterns, body) => {
            let site = (expression.module, expression.span);
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
                return Err(located(
                    expression,
                    "this lambda wraps the callback it was handed and hands itself on, so each round asks for another definition: recurse on data that says what to call instead",
                ));
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
    key.ty.function().is_some_and(|(parameters, _)| {
        parameters
            .iter()
            .any(|parameter| matches!(parameter, Type::Function(..)))
    })
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
        ExprKind::Invoke(head, arguments) => {
            for_each(head, visit);
            for each in arguments {
                for_each(each, visit);
            }
        }
        ExprKind::Lambda(_, body) => for_each(body, visit),
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
        ExprKind::Lambda(patterns, _) => patterns.iter().map(pattern_highest).max().unwrap_or(0),
        _ => 0,
    }
}

fn pattern_highest(pattern: &Pattern) -> u32 {
    match pattern {
        Pattern::Bind(local) => local.0,
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
        Pattern::Wild | Pattern::Number { .. } | Pattern::Range | Pattern::String => 0,
    }
}

fn located(expression: &Expr, message: &str) -> SpecializeError {
    SpecializeError {
        message: message.to_owned(),
        at: Some((expression.module, expression.span)),
    }
}

fn internal(what: &str) -> SpecializeError {
    SpecializeError {
        message: format!("callback specialization expected {what}"),
        at: None,
    }
}

/// The locals a lambda's body reads that its parameters do not bind.
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
        S::Invoke(head, arguments) => {
            free_locals(head, bound, found);
            for argument in arguments {
                free_locals(argument, bound, found);
            }
        }
        S::Lambda(patterns, body) => {
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
        Pattern::Wild | Pattern::Number { .. } | Pattern::Range | Pattern::String => {}
    }
}
