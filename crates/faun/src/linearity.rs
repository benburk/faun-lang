//! Resources: what a program must use up exactly once.
//!
//! A resource is a value naming something outside the program that the
//! program is answerable for, such as an open file. A routine the target
//! declares as using up what it is handed first makes the type of that
//! argument a resource; nothing else does, and no syntax says so. A type
//! whose fields hold a resource carries one: a list of files, a result
//! holding one.
//!
//! What holds a resource must use it up exactly once on every way the
//! function goes on: hand it to something that uses it up, or answer it.
//! Dropping one, using one after it is used up, or leaving by `?` while one
//! is held is refused. There is no destructor and no cleanup on `?`: a
//! hidden close would be an effect nobody wrote.
//!
//! What a function does with each resource it is handed is found from its
//! body rather than written: a parameter only looked at, on every way the
//! function goes on, is lent, and the caller still holds it; one used up or
//! answered on every way is taken. Ways that disagree are refused. Every
//! call names its callee, so each call site knows which it is. Functions
//! calling each other are worked out together, from knowing nothing of
//! each, until nothing more is learned.
//!
//! This reads the first-order program, where every function value has
//! become the definition it was handed to and every type is known, so a
//! resource is never hidden behind a type variable or a callback.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use faun_core::platform::Routines;

use crate::diagnostic::Diagnostic;
use crate::first_order::{self as d, ExprKind};
use crate::hir::LocalId;
use crate::resolve::ResolvedProgram;
use crate::specialize::{FunctionKey, Pattern, Type, surface_type};
use crate::{ModuleId, Symbol};

/// Refuse a program that drops a resource, uses one twice, or leaves one
/// behind.
///
/// # Errors
/// The first such use, where it was written.
pub(crate) fn check(
    program: &d::Program,
    routines: &Routines,
    resolved: &ResolvedProgram<crate::typed::Program>,
) -> Result<(), Diagnostic> {
    let facts = Facts::of(program, routines, resolved);
    if facts.resources.is_empty() {
        return Ok(());
    }
    let settled = settle(&facts);
    for at in 0..program.functions.len() {
        let mut found = Vec::new();
        facts.walk(at, &settled, Some(&mut found));
        if let Some(first) = found.into_iter().next() {
            return Err(facts.diagnostic(first));
        }
    }
    Ok(())
}

/// What every function does with each parameter it is handed, learned
/// round by round until a round learns nothing. What is learned is never
/// unlearned: each round joins what it finds with what was known, so a
/// contract only moves up from knowing nothing, and there are only so many
/// steps up. What is still unknown then is never taken, so it is lent.
fn settle(facts: &Facts<'_>) -> Vec<Vec<Contract>> {
    let mut contracts = facts.given();
    loop {
        let learned: Vec<Vec<Contract>> = facts
            .contracts(&contracts)
            .into_iter()
            .zip(&contracts)
            .map(|(learned, known)| {
                learned
                    .into_iter()
                    .zip(known)
                    .map(|(learned, known)| known.and(learned))
                    .collect()
            })
            .collect();
        if learned == contracts {
            break;
        }
        contracts = learned;
    }
    contracts
        .into_iter()
        .map(|each| {
            each.into_iter()
                .map(|contract| match contract {
                    Contract::Unknown => Contract::Lent,
                    known => known,
                })
                .collect()
        })
        .collect()
}

/// Every type a routine uses up, as the program declares it, whether or not
/// anything reaches the declaration: a resource is one wherever a program
/// holds it, closed or not.
fn resources(
    resolved: &ResolvedProgram<crate::typed::Program>,
    routines: &Routines,
) -> HashSet<Symbol> {
    resolved
        .program
        .functions
        .iter()
        .filter_map(|function| {
            let crate::typed::Definition::External(provider) = function.definition else {
                return None;
            };
            let routine = routines.get(resolved.symbols.text(provider))?;
            let crate::check::InferredType::Function(parameters, _) = &function.scheme.ty else {
                unreachable!("every definition has a function scheme")
            };
            match parameters.first() {
                Some(crate::check::InferredType::Named(resource, _)) if routine.consumes => {
                    Some(*resource)
                }
                _ => None,
            }
        })
        .collect()
}

/// What a function does with one parameter's resources.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Contract {
    /// Nothing is known yet: every way it goes on so far hands it to
    /// something not yet known either, or holds none of it.
    Unknown,
    /// Only looked at: the caller still holds it.
    Lent,
    /// Used up or answered: the caller holds it no longer.
    Taken,
    /// Lent on one way the function goes on and taken on another.
    Disagrees,
}

impl Contract {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unknown, other) | (other, Self::Unknown) => other,
            (same, other) if same == other => same,
            _ => Self::Disagrees,
        }
    }
}

/// What the whole program says: which types are resources, where each
/// function is, and how to read the source back for a diagnostic.
struct Facts<'a> {
    program: &'a d::Program,
    resolved: &'a ResolvedProgram<crate::typed::Program>,
    resources: HashSet<Symbol>,
    /// Which function each key is.
    functions: HashMap<&'a FunctionKey, usize>,
    /// Each constructor's owner and fields, as its declaration says.
    constructors: HashMap<Symbol, (Symbol, Vec<crate::hir::Type>)>,
    /// Which parameter of each routine a target answers for is used up.
    uses_up: Vec<Option<usize>>,
    carries: RefCell<HashMap<Type, bool>>,
}

impl<'a> Facts<'a> {
    fn of(
        program: &'a d::Program,
        routines: &Routines,
        resolved: &'a ResolvedProgram<crate::typed::Program>,
    ) -> Self {
        let uses_up = program
            .functions
            .iter()
            .map(|function| {
                let d::Definition::External(provider) = function.definition else {
                    return None;
                };
                let routine = routines.get(resolved.symbols.text(provider))?;
                routine.consumes.then_some(0)
            })
            .collect();
        let mut constructors = HashMap::new();
        for (owner, data) in &program.data {
            for constructor in &data.constructors {
                constructors.insert(constructor.name, (*owner, constructor.fields.clone()));
            }
            if let Some(wrapper) = &data.wrapper {
                constructors.insert(wrapper.constructor, (*owner, vec![wrapper.field.clone()]));
            }
        }
        Self {
            program,
            resolved,
            resources: resources(resolved, routines),
            functions: program
                .functions
                .iter()
                .enumerate()
                .map(|(at, function)| (&function.key, at))
                .collect(),
            constructors,
            uses_up,
            carries: RefCell::default(),
        }
    }

    /// What is known before any body is read: what each routine a target
    /// answers for does with what it is handed.
    fn given(&self) -> Vec<Vec<Contract>> {
        self.program
            .functions
            .iter()
            .zip(&self.uses_up)
            .map(|(function, uses_up)| {
                let count = function.key.signature.parameters.len();
                (0..count)
                    .map(|at| match (&function.definition, uses_up) {
                        (d::Definition::External(_), Some(taken)) if *taken == at => {
                            Contract::Taken
                        }
                        (d::Definition::External(_), _) => Contract::Lent,
                        (d::Definition::Body(_), _) => Contract::Unknown,
                    })
                    .collect()
            })
            .collect()
    }

    /// What each function does with each parameter, read from its body,
    /// given what each does as far as `known` says.
    fn contracts(&self, known: &[Vec<Contract>]) -> Vec<Vec<Contract>> {
        (0..self.program.functions.len())
            .map(|at| {
                let function = &self.program.functions[at];
                let takes_any = function
                    .key
                    .signature
                    .parameters
                    .iter()
                    .any(|p| self.carries(p));
                if matches!(function.definition, d::Definition::External(_)) || !takes_any {
                    known[at].clone()
                } else {
                    self.walk(at, known, None)
                }
            })
            .collect()
    }

    /// Walk every clause of function `at`, every way it goes on: what it
    /// does with each parameter, and, where `found` is asked for, every
    /// use refused.
    fn walk(
        &self,
        at: usize,
        known: &[Vec<Contract>],
        mut found: Option<&mut Vec<Refusal>>,
    ) -> Vec<Contract> {
        let function = &self.program.functions[at];
        let d::Definition::Body(clauses) = &function.definition else {
            return known[at].clone();
        };
        let parameters = &function.key.signature.parameters;
        let mut contracts = vec![Contract::Unknown; parameters.len()];
        let mut paths: Vec<Path> = Vec::new();
        for clause in clauses {
            let mut walk = Walk {
                facts: self,
                known,
                function: at,
                held: Vec::new(),
                locals: HashMap::new(),
                paths: Vec::new(),
                refused: Vec::new(),
                guarded: false,
            };
            walk.clause(clause, parameters);
            paths.append(&mut walk.paths);
            if let Some(found) = found.as_deref_mut() {
                found.append(&mut walk.refused);
            }
        }
        for path in &paths {
            for (parameter, contract) in contracts.iter_mut().enumerate() {
                *contract = contract.and(path.contract(parameter));
            }
        }
        if let Some(found) = found {
            for (parameter, contract) in contracts.iter().enumerate() {
                if *contract == Contract::Disagrees {
                    found.push(self.disagreement(at, parameter, &paths));
                }
            }
        }
        contracts
    }

    /// Where a parameter is taken on one way and kept on another: the
    /// first place it is taken, and the first way it is kept.
    fn disagreement(&self, function: usize, parameter: usize, paths: &[Path]) -> Refusal {
        let taken = paths.iter().find_map(|path| {
            path.taken
                .iter()
                .find_map(|(at, place)| place.filter(|_| *at == parameter))
        });
        let kept = paths
            .iter()
            .find_map(|path| path.kept.contains(&parameter).then_some(path.end));
        let name = self.name(function);
        let resource = self.program.functions[function]
            .key
            .signature
            .parameters
            .get(parameter)
            .and_then(|ty| self.resource_in(ty));
        Refusal {
            at: taken.or_else(|| kept.map(|(at, _)| at)),
            message: format!(
                "`{name}` uses up the {} its parameter {} holds on one way it goes on and not on another",
                self.called(resource, "resource"),
                parameter + 1
            ),
            also: kept.filter(|_| taken.is_some()).map(|(at, leaving)| {
                let still = match leaving {
                    Leaving::Asking => "it is still held where this `?` leaves".to_owned(),
                    Leaving::Answering => format!("it is still held where `{name}` answers"),
                };
                (at, still)
            }),
            help: Some(
                "use it up on every way the function goes on, or on none, where the caller does"
                    .to_owned(),
            ),
        }
    }

    /// Whether a value of `ty` holds a resource anywhere in it.
    fn carries(&self, ty: &Type) -> bool {
        if let Some(&known) = self.carries.borrow().get(ty) {
            return known;
        }
        // A type reaching itself holds a resource only where something
        // else in it does, so it is taken to hold none while it is asked.
        self.carries.borrow_mut().insert(ty.clone(), false);
        let carries = match ty {
            Type::Named(name, _) if self.resources.contains(name) => true,
            Type::Named(..) => self
                .fields_of_every(ty)
                .iter()
                .any(|field| self.carries(field)),
            Type::Function(..) => false,
            Type::Variants(tags) => tags.iter().flat_map(|(_, f)| f).any(|f| self.carries(f)),
            Type::Record(fields) => fields.iter().any(|(_, field)| self.carries(field)),
            Type::Tuple(members) => members.iter().any(|member| self.carries(member)),
        };
        self.carries.borrow_mut().insert(ty.clone(), carries);
        carries
    }

    /// Every field of every constructor of a named type, at its arguments.
    fn fields_of_every(&self, ty: &Type) -> Vec<Type> {
        let Type::Named(name, _) = ty else {
            return Vec::new();
        };
        let Some(data) = self.program.data.get(name) else {
            return Vec::new();
        };
        data.constructors
            .iter()
            .map(|each| each.name)
            .chain(data.wrapper.as_ref().map(|wrapper| wrapper.constructor))
            .flat_map(|constructor| self.fields(constructor, ty).unwrap_or_default())
            .collect()
    }

    /// What each pattern within `pattern` is matched against, of a value of
    /// `ty`: a constructor's fields, a tuple's members, or a list's
    /// elements and the rest of it.
    fn parts<'p>(&self, pattern: &'p Pattern, ty: &Type) -> Vec<(&'p Pattern, Type)> {
        match (pattern, ty) {
            (Pattern::Constructor(constructor, patterns), _) => patterns
                .iter()
                .zip(self.fields(*constructor, ty).unwrap_or_default())
                .collect(),
            (Pattern::Product(patterns), Type::Tuple(members)) => {
                patterns.iter().zip(members.iter().cloned()).collect()
            }
            (Pattern::List(elements, rest), Type::Named(_, arguments)) => {
                let element = arguments.first().cloned();
                elements
                    .iter()
                    .filter_map(|pattern| Some((pattern, element.clone()?)))
                    .chain(rest.as_deref().map(|rest| (rest, ty.clone())))
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    /// The fields of `constructor`, of type `ty`, at that type's arguments.
    fn fields(&self, constructor: Symbol, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Variants(tags) => tags
                .iter()
                .find(|(tag, _)| *tag == constructor)
                .map(|(_, fields)| fields.clone()),
            Type::Named(name, arguments) => {
                let (owner, fields) = self.constructors.get(&constructor)?;
                let data = self.program.data.get(name).filter(|_| owner == name)?;
                let variables: HashMap<_, _> = data
                    .parameters
                    .iter()
                    .copied()
                    .zip(arguments.iter().cloned())
                    .collect();
                fields
                    .iter()
                    .map(|field| surface_type(field, &variables).ok())
                    .collect()
            }
            _ => None,
        }
    }

    /// A function's name, as its program spells it.
    fn name(&self, function: usize) -> &str {
        self.spelled(self.program.functions[function].key.name)
    }

    /// A name as its program spells it, without its module's identity.
    fn spelled(&self, name: Symbol) -> &str {
        let canonical = self.resolved.symbols.text(name);
        canonical
            .rsplit_once("$$")
            .map_or(canonical, |(_, spelled)| spelled)
    }

    /// A resource type named as a program spells it, or `otherwise`.
    fn called(&self, resource: Option<Symbol>, otherwise: &str) -> String {
        resource.map_or_else(
            || otherwise.to_owned(),
            |resource| format!("`{}`", self.spelled(resource)),
        )
    }

    /// The first resource type a value of `ty` holds.
    fn resource_in(&self, ty: &Type) -> Option<Symbol> {
        let mut waiting = vec![ty.clone()];
        let mut seen = HashSet::new();
        while let Some(ty) = waiting.pop() {
            if !self.carries(&ty) || !seen.insert(ty.clone()) {
                continue;
            }
            match &ty {
                Type::Named(name, _) if self.resources.contains(name) => return Some(*name),
                Type::Named(..) => waiting.extend(self.fields_of_every(&ty)),
                Type::Variants(tags) => waiting.extend(tags.iter().flat_map(|(_, f)| f.clone())),
                Type::Record(fields) => waiting.extend(fields.iter().map(|(_, f)| f.clone())),
                Type::Tuple(members) => waiting.extend(members.iter().cloned()),
                Type::Function(..) => {}
            }
        }
        None
    }

    fn diagnostic(&self, refusal: Refusal) -> Diagnostic {
        let mut diagnostic = match refusal.at {
            Some((module, span)) => self.resolved.diagnostic(module, span, refusal.message),
            None => Diagnostic::new(refusal.message),
        };
        if let Some(((module, span), note)) = refusal.also {
            let location = self.resolved.location(module, span);
            diagnostic = diagnostic.note(format!("{note}, at line {}", location.line));
        }
        if let Some(help) = refusal.help {
            diagnostic = diagnostic.help(help);
        }
        diagnostic
    }
}

/// Where something was written.
type Place = (ModuleId, crate::ast::Span);

/// Where a held resource came from.
#[derive(Clone, Copy, Debug)]
enum Origin {
    /// Some of what the function's parameter at this place was handed.
    Parameter(usize),
    /// Made here: answered by the call, or built by the constructor, written
    /// at this place.
    Made(Place, Made),
}

/// What made a resource, for saying which one is meant.
#[derive(Clone, Copy, Debug)]
struct Made {
    /// The resource's type, the first one the value holds.
    resource: Option<Symbol>,
    /// The function whose answer holds it, or nothing where it was built.
    by: Option<Symbol>,
}

/// How one way a function goes on ends.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Leaving {
    /// With what the function answers.
    Answering,
    /// By `?`, with the error.
    Asking,
}

/// Something held that holds a resource: a local, or a part of a value
/// nothing names.
struct Held {
    origins: Vec<Origin>,
    state: State,
}

#[derive(Clone, Copy)]
enum State {
    Held,
    /// Used up, or answered, here.
    Gone(Place),
    /// Handed to a function nothing is known of yet.
    Unknown,
}

/// One way a function goes on, to its answer or out by `?`: which
/// parameters' resources it took, where, and which it kept.
struct Path {
    end: (Place, Leaving),
    taken: Vec<(usize, Option<Place>)>,
    kept: Vec<usize>,
}

impl Path {
    fn contract(&self, parameter: usize) -> Contract {
        let taken = self.taken.iter().any(|(at, _)| *at == parameter);
        let kept = self.kept.contains(&parameter);
        match (taken, kept) {
            (true, true) => Contract::Disagrees,
            (true, false) => Contract::Taken,
            (false, true) => Contract::Lent,
            (false, false) => Contract::Unknown,
        }
    }
}

/// A use refused: where, what is wrong, and where else to look.
struct Refusal {
    at: Option<Place>,
    message: String,
    also: Option<(Place, String)>,
    help: Option<String>,
}

/// One clause, walked in the order it is written.
struct Walk<'f, 'a> {
    facts: &'f Facts<'a>,
    known: &'f [Vec<Contract>],
    function: usize,
    held: Vec<Held>,
    locals: HashMap<LocalId, usize>,
    paths: Vec<Path>,
    refused: Vec<Refusal>,
    /// Whether a guard is being read, which may look and nothing more.
    guarded: bool,
}

impl Walk<'_, '_> {
    /// A clause: what its patterns bind of the parameters, what its guard
    /// looks at, and its body.
    fn clause(&mut self, clause: &d::Clause, parameters: &[Type]) {
        for (parameter, (pattern, ty)) in clause.patterns.iter().zip(parameters).enumerate() {
            self.bind(pattern, ty, &[Origin::Parameter(parameter)]);
        }
        if let Some(guard) = &clause.guard {
            self.guarded = true;
            let answer = self.value(guard);
            self.hold(&answer);
            self.guarded = false;
        }
        self.body(&clause.body);
    }

    fn body(&mut self, body: &d::Body) {
        for binding in &body.bindings {
            let origins = self.value(&binding.value);
            self.bind(&binding.pattern, &binding.value.ty, &origins);
        }
        let answer = self.value(&body.result);
        self.end(&answer, (place(&body.result), Leaving::Answering));
    }

    /// Bind what a pattern names of a value holding `origins`. A part it
    /// does not name is held all the same, by nothing, which is how a
    /// parameter's part is kept and a made one dropped. A resource taken
    /// apart, which only the module declaring it can, is looked at.
    fn bind(&mut self, pattern: &Pattern, ty: &Type, origins: &[Origin]) {
        if origins.is_empty() || !self.facts.carries(ty) {
            return;
        }
        match pattern {
            Pattern::Bind(local) => {
                self.held.push(Held {
                    origins: origins.to_vec(),
                    state: State::Held,
                });
                self.locals.insert(*local, self.held.len() - 1);
            }
            Pattern::Constructor(_, _) if self.is_resource(ty) => self.hold(origins),
            Pattern::Wild => self.hold(origins),
            Pattern::Record(patterns) => {
                if let Type::Record(fields) = ty {
                    self.bind_record(patterns, fields, origins);
                }
            }
            _ => {
                for (pattern, part) in self.facts.parts(pattern, ty) {
                    self.bind(pattern, &part, origins);
                }
            }
        }
    }

    /// Bind the fields a record pattern names. A field it leaves out is
    /// held by nothing.
    fn bind_record(
        &mut self,
        patterns: &[(Symbol, Pattern)],
        fields: &[(Symbol, Type)],
        origins: &[Origin],
    ) {
        for (name, pattern) in patterns {
            if let Some((_, field)) = fields.iter().find(|(each, _)| each == name) {
                self.bind(pattern, field, origins);
            }
        }
        let named = |each: &Symbol| patterns.iter().any(|(name, _)| name == each);
        if fields
            .iter()
            .any(|(name, field)| !named(name) && self.facts.carries(field))
        {
            self.hold(origins);
        }
    }

    fn is_resource(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named(name, _) if self.facts.resources.contains(name))
    }

    /// Held by nothing: kept where it is a parameter's, and dropped where
    /// it was made here.
    fn hold(&mut self, origins: &[Origin]) {
        if !origins.is_empty() {
            self.held.push(Held {
                origins: origins.to_vec(),
                state: State::Held,
            });
        }
    }

    /// What `expr` is worth, taken: the resources the value holds, which
    /// whoever receives it now holds. A local handed over whole is taken
    /// once everything written beside it has been worked out, so what
    /// looks at it first still sees it.
    fn value(&mut self, expr: &d::Expr) -> Vec<Origin> {
        match &expr.kind {
            ExprKind::Local(_) => self.take(expr),
            ExprKind::Natural(_) | ExprKind::Bytes(_) => Vec::new(),
            ExprKind::Construct(_, fields) | ExprKind::Tuple(fields) => {
                let mut origins = self.values(fields.iter());
                if self.is_resource(&expr.ty) {
                    let made = Made {
                        resource: self.facts.resource_in(&expr.ty),
                        by: None,
                    };
                    origins.push(Origin::Made(place(expr), made));
                }
                origins
            }
            ExprKind::Record(fields) => self.values(fields.iter().map(|(_, field)| field)),
            ExprKind::Update(base, fields) => self.values(
                std::iter::once(base.as_ref()).chain(fields.iter().map(|(_, field)| field)),
            ),
            ExprKind::Project(receiver, _) if !self.facts.carries(&expr.ty) => {
                self.lend(receiver);
                Vec::new()
            }
            ExprKind::Project(receiver, _) | ExprKind::Widen(receiver) => self.value(receiver),
            ExprKind::DirectCall(callee, arguments) => self.call(expr, callee, arguments),
            ExprKind::Try(tried) => {
                let origins = self.value(tried);
                self.end(&origins, (place(expr), Leaving::Asking));
                origins
            }
        }
    }

    /// The values of `exprs`, each taken, those that are locals last.
    fn values<'e>(&mut self, exprs: impl Iterator<Item = &'e d::Expr> + Clone) -> Vec<Origin> {
        let mut origins = Vec::new();
        for expr in exprs.clone().filter(|expr| !is_local(expr)) {
            origins.extend(self.value(expr));
        }
        for expr in exprs.filter(|expr| is_local(expr)) {
            origins.extend(self.take(expr));
        }
        origins
    }

    /// A call: each argument lent or taken as the callee does, and what it
    /// answers made here, where it holds a resource.
    fn call(&mut self, expr: &d::Expr, callee: &FunctionKey, arguments: &[d::Expr]) -> Vec<Origin> {
        let contracts = self
            .facts
            .functions
            .get(callee)
            .map(|&at| self.known[at].clone())
            .unwrap_or_default();
        let contract = |at: usize| contracts.get(at).copied().unwrap_or(Contract::Lent);
        // What each argument works out first, then what looks at a local,
        // then what takes one: all of it happens before the call does.
        self.work_out(arguments, contract);
        for (at, argument) in arguments.iter().enumerate() {
            if is_local(argument) && contract(at) != Contract::Taken {
                self.look(argument);
            }
        }
        self.hand_locals(arguments, contract);
        if self.facts.carries(&expr.ty) {
            let made = Made {
                resource: self.facts.resource_in(&expr.ty),
                by: Some(callee.name),
            };
            vec![Origin::Made(place(expr), made)]
        } else {
            Vec::new()
        }
    }

    /// Every argument but a local, worked out and lent or taken.
    fn work_out(&mut self, arguments: &[d::Expr], contract: impl Fn(usize) -> Contract) {
        for (at, argument) in arguments.iter().enumerate() {
            if is_local(argument) {
                continue;
            }
            match contract(at) {
                Contract::Lent => self.lend(argument),
                // A callee that takes it on only some ways is refused where
                // it is written; here it is taken, so the caller is not
                // refused for that too.
                Contract::Taken | Contract::Disagrees => {
                    let origins = self.value(argument);
                    self.used_up(&origins, place(argument));
                }
                Contract::Unknown => {
                    let origins = self.value(argument);
                    self.handed_on(&origins);
                }
            }
        }
    }

    /// Every local argument holding a resource, taken where the callee
    /// takes it.
    fn hand_locals(&mut self, arguments: &[d::Expr], contract: impl Fn(usize) -> Contract) {
        for (at, argument) in arguments.iter().enumerate() {
            if !is_local(argument) || !self.facts.carries(&argument.ty) {
                continue;
            }
            match contract(at) {
                Contract::Lent => {}
                Contract::Taken | Contract::Disagrees => {
                    let origins = self.take(argument);
                    self.used_up(&origins, place(argument));
                }
                Contract::Unknown => {
                    if let Some(held) = self.local(argument) {
                        self.held[held].state = State::Unknown;
                    }
                }
            }
        }
    }

    /// Resources `origins` names, used up by what `at` asks: taken from
    /// whatever held them. A guard may only look.
    fn used_up(&mut self, origins: &[Origin], at: Place) {
        if origins.is_empty() {
            return;
        }
        if self.guarded {
            self.refused.push(Refusal {
                at: Some(at),
                message: "a guard only looks, and this uses up a resource".to_owned(),
                also: None,
                help: Some("use it up in the clause's body".to_owned()),
            });
        }
        self.held.push(Held {
            origins: origins.to_vec(),
            state: State::Gone(at),
        });
    }

    /// Resources handed to a function nothing is known of yet.
    fn handed_on(&mut self, origins: &[Origin]) {
        if !origins.is_empty() {
            self.held.push(Held {
                origins: origins.to_vec(),
                state: State::Unknown,
            });
        }
    }

    /// Look at what `expr` is without taking it: what it works out that
    /// holds a resource, nobody holds afterwards.
    fn lend(&mut self, expr: &d::Expr) {
        if is_local(expr) {
            self.look(expr);
        } else {
            let origins = self.value(expr);
            self.hold(&origins);
        }
    }

    /// A local looked at, which must still be held.
    fn look(&mut self, expr: &d::Expr) {
        let Some(held) = self.local(expr) else {
            return;
        };
        if let State::Gone(gone) = self.held[held].state {
            let refusal = self.used_twice(expr, gone);
            self.refused.push(refusal);
        }
    }

    /// A local taken whole: what it held, which it holds no longer.
    fn take(&mut self, expr: &d::Expr) -> Vec<Origin> {
        let Some(held) = self.local(expr) else {
            return Vec::new();
        };
        match self.held[held].state {
            State::Held => {
                self.held[held].state = State::Gone(place(expr));
                self.held[held].origins.clone()
            }
            State::Gone(gone) => {
                let refusal = self.used_twice(expr, gone);
                self.refused.push(refusal);
                Vec::new()
            }
            State::Unknown => Vec::new(),
        }
    }

    /// A resource used again at `expr`, which was used up at `gone`.
    fn used_twice(&self, expr: &d::Expr, gone: Place) -> Refusal {
        let resource = self
            .facts
            .called(self.facts.resource_in(&expr.ty), "resource");
        Refusal {
            at: Some(place(expr)),
            message: format!("this {resource} has already been used up"),
            also: Some((gone, "it was used up".to_owned())),
            help: None,
        }
    }

    /// Which held thing a local expression names, where it holds any.
    fn local(&self, expr: &d::Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::Local(local) => self.locals.get(local).copied(),
            _ => None,
        }
    }

    /// One way the function goes on ends here, answering `answered`: what
    /// is still held is kept where it is a parameter's and dropped where
    /// it was made here.
    fn end(&mut self, answered: &[Origin], (at, leaving): (Place, Leaving)) {
        let mut path = Path {
            end: (at, leaving),
            taken: Vec::new(),
            kept: Vec::new(),
        };
        for origin in answered {
            if let Origin::Parameter(parameter) = origin {
                path.taken.push((*parameter, Some(at)));
            }
        }
        let mut dropped = Vec::new();
        for held in &self.held {
            for origin in &held.origins {
                match (held.state, origin) {
                    (State::Held, Origin::Parameter(parameter)) => path.kept.push(*parameter),
                    (State::Held, Origin::Made(place, made)) => dropped.push((*place, *made)),
                    (State::Gone(gone), Origin::Parameter(parameter)) => {
                        path.taken.push((*parameter, Some(gone)));
                    }
                    (State::Gone(_) | State::Unknown, _) => {}
                }
            }
        }
        for made in dropped {
            self.refused.push(self.dropped(made, (at, leaving)));
        }
        self.paths.push(path);
    }

    /// A resource made at `made` that nothing uses up before `end`.
    fn dropped(&self, (at, made): (Place, Made), (end, leaving): (Place, Leaving)) -> Refusal {
        let name = self.facts.name(self.function);
        let resource = self.facts.called(made.resource, "resource");
        let what = made.by.map_or_else(
            || format!("the {resource} built here"),
            |by| format!("the {resource} `{}` answers", self.facts.spelled(by)),
        );
        let (still, help) = match leaving {
            Leaving::Asking => (
                "it is still held where this `?` leaves".to_owned(),
                "use it up before asking `?` of anything: keep what a step answers, use it up, \
                 then ask `?` of what was kept",
            ),
            Leaving::Answering => (
                format!("it is still held where `{name}` answers"),
                "use it up, as `close!` does, or answer it",
            ),
        };
        Refusal {
            at: Some(at),
            message: format!(
                "{what} is neither used up nor answered on every way `{name}` goes on"
            ),
            also: (end != at).then_some((end, still)),
            help: Some(help.to_owned()),
        }
    }
}

const fn is_local(expr: &d::Expr) -> bool {
    matches!(expr.kind, ExprKind::Local(_))
}

const fn place(expr: &d::Expr) -> Place {
    (expr.module, expr.span)
}
