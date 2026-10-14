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
//! A test is two ways on, where it holds and where it fails. Where a
//! pattern names a part holding a resource, the value is taken apart there,
//! as a binding takes it; where it fails, the value is as it was, holding
//! none where the test shows it cannot. A loop's round must end as it began,
//! what it made used up or handed to the next round in a name the loop
//! carries, and every way out of the loop must agree.
//!
//! This reads the first-order program, where every function value has
//! become the definition it was handed to and every type is known, so a
//! resource is never hidden behind a type variable or a callback.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use faun_core::platform::Routines;

use crate::blessed::PreludeIds;
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
    prelude: &PreludeIds,
) -> Result<(), Diagnostic> {
    let facts = Facts::of(program, routines, resolved, prelude);
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
    /// `Bool`'s `&` and `|`, along which a test's names are seen.
    and: Symbol,
    or: Symbol,
}

impl<'a> Facts<'a> {
    fn of(
        program: &'a d::Program,
        routines: &Routines,
        resolved: &'a ResolvedProgram<crate::typed::Program>,
        prelude: &PreludeIds,
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
            and: prelude.bool_and,
            or: prelude.bool_or,
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
            let mut walk = Walk::new(self, known, at, place(&clause.body.result));
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
        let resource = self.called(resource, "resource");
        let label = if taken.is_some() {
            "used up here".to_owned()
        } else {
            "held here".to_owned()
        };
        Refusal {
            at: taken.or_else(|| kept.map(|(at, _)| at)),
            message: format!(
                "`{name}` uses up the {resource} in its {} parameter on some ways it goes on and not others",
                ordinal(parameter)
            ),
            label,
            also: kept.filter(|_| taken.is_some()).map(|(at, leaving)| {
                let still = match leaving {
                    Leaving::Asking => "still held where this `?` leaves".to_owned(),
                    Leaving::Answering => format!("still held where `{name}` answers"),
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
            (Pattern::Split(split), Type::Named(_, arguments)) => {
                let element = arguments.first().cloned();
                std::iter::once((&split.front, ty.clone()))
                    .chain(
                        split
                            .last
                            .iter()
                            .filter_map(|pattern| Some((pattern, element.clone()?))),
                    )
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    /// Every constructor of `ty`, where it is taken apart by constructors.
    fn constructors_of(&self, ty: &Type) -> Option<Vec<Symbol>> {
        match ty {
            Type::Variants(tags) => Some(tags.iter().map(|(tag, _)| *tag).collect()),
            Type::Named(name, _) if !self.resources.contains(name) => {
                let data = self.program.data.get(name)?;
                Some(
                    data.constructors
                        .iter()
                        .map(|each| each.name)
                        .chain(data.wrapper.as_ref().map(|wrapper| wrapper.constructor))
                        .collect(),
                )
            }
            _ => None,
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
        diagnostic = diagnostic.label(refusal.label);
        if let Some(((module, span), text)) = refusal.also {
            let location = self.resolved.location(module, span);
            diagnostic = diagnostic.secondary_at(location, text);
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
    by: Maker,
}

#[derive(Clone, Copy, Debug)]
enum Maker {
    /// Built by a constructor.
    Built,
    /// Answered by this function.
    Call(Symbol),
    /// Made in a loop's round and carried to the next, or out of it.
    Carried,
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Held,
    /// Used up, or answered, here.
    Gone(Place),
    /// Handed to a function nothing is known of yet.
    Unknown,
    /// Holding none: a test showed it is a value that holds no resource, or
    /// it is not there on this way, as what a test bound where it failed.
    Empty,
}

impl State {
    /// As a round leaving it would find it next: a value shown to hold
    /// nothing is the value it was.
    const fn settled(self) -> Self {
        match self {
            Self::Empty => Self::Held,
            other => other,
        }
    }
}

/// Where a condition holds and where it fails: the state of everything
/// held once it is worked out, each way.
struct Outcome {
    holds: Vec<State>,
    fails: Vec<State>,
    /// What its tests took apart where they held.
    apart: Apart,
}

impl Outcome {
    /// A condition holding no test, alike either way.
    fn alike(states: Vec<State>) -> Self {
        Self {
            holds: states.clone(),
            fails: states,
            apart: Apart::default(),
        }
    }
}

/// What tests took apart, where they held.
#[derive(Default)]
struct Apart {
    /// Each value taken apart, as it was before.
    took: Vec<(usize, State)>,
    /// What holds its parts.
    parts: Vec<usize>,
    /// The names bound to them, and what each is.
    bound: Vec<(LocalId, usize)>,
}

impl Apart {
    /// Both tests' parts.
    fn and(mut self, other: Self) -> Self {
        self.took.extend(other.took);
        self.parts.extend(other.parts);
        self.bound.extend(other.bound);
        self
    }

    /// `states`, as though the tests had not held: what they took apart
    /// whole again, and their parts held by none.
    fn undone(&self, mut states: Vec<State>) -> Vec<State> {
        for (whole, state) in &self.took {
            states[*whole] = *state;
        }
        for part in &self.parts {
            states[*part] = State::Empty;
        }
        states
    }
}

/// The loop being walked: how its round begins, and every way the round
/// ends, by `continue`, or the loop, by `break`.
struct Frame {
    /// What was held when the round begins.
    start: Vec<State>,
    /// How many things were held before the loop; the rest are its own.
    outer: usize,
    /// What holds the part of a list a `for` has not walked yet.
    walking: Option<usize>,
    continues: Vec<(Place, Vec<State>)>,
    /// Each `break`, with what each name the loop carries is handed.
    breaks: Vec<(Vec<State>, Vec<State>)>,
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
    /// What is at `at`.
    label: String,
    /// Another place explaining it, and what is there.
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
    /// Where the clause walked answers, for what its head is refused.
    answering: Option<Place>,
    /// Whether the branch walked last left by `return`, `continue` or
    /// `break`, so that nothing after it is held as it left things.
    left: bool,
    /// The loops being walked, the innermost last.
    loops: Vec<Frame>,
    /// Where a test took apart what it tested, which it holds no longer.
    taken_apart: HashSet<Place>,
}

impl<'f, 'a> Walk<'f, 'a> {
    /// Ready to walk a clause of `function` answering at `answering`,
    /// holding nothing yet.
    fn new(
        facts: &'f Facts<'a>,
        known: &'f [Vec<Contract>],
        function: usize,
        answering: Place,
    ) -> Self {
        Self {
            facts,
            known,
            function,
            held: Vec::new(),
            locals: HashMap::new(),
            paths: Vec::new(),
            refused: Vec::new(),
            guarded: false,
            answering: Some(answering),
            left: false,
            loops: Vec::new(),
            taken_apart: HashSet::new(),
        }
    }

    /// A clause: what its patterns bind of the parameters, what its guard
    /// looks at or its tests take apart, and its body.
    fn clause(&mut self, clause: &d::Clause, parameters: &[Type]) {
        for (parameter, (pattern, ty)) in clause.patterns.iter().zip(parameters).enumerate() {
            self.bind(pattern, ty, &[Origin::Parameter(parameter)]);
        }
        if let Some(guard) = &clause.guard {
            self.guarded(guard);
        }
        self.body(&clause.body);
    }

    /// A guard, which may look and take apart and nothing more, worked out:
    /// what follows it goes on where it holds.
    fn guarded(&mut self, guard: &d::Expr) {
        self.guarded = true;
        let outcome = self.condition(guard);
        self.guarded = false;
        self.set(&outcome.holds);
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
            // The whole and its parts would each hold what it holds.
            Pattern::As(_, pattern) => {
                let resource = self.facts.called(self.facts.resource_in(ty), "resource");
                self.refused.push(Refusal {
                    at: self.answering,
                    message: format!(
                        "a value holding a {resource} is named whole or taken apart, not both"
                    ),
                    label: "in the clause answering this".to_owned(),
                    also: None,
                    help: Some("name the whole, or its parts".to_owned()),
                });
                self.bind(pattern, ty, origins);
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
    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each kind of expression, each saying what it is worth"
    )]
    fn value(&mut self, expr: &d::Expr) -> Vec<Origin> {
        match &expr.kind {
            ExprKind::Local(_) => self.take(expr),
            ExprKind::Natural(_) | ExprKind::Bytes(_) => Vec::new(),
            ExprKind::Construct(_, fields) | ExprKind::Tuple(fields) => {
                let mut origins = self.values(fields.iter());
                if self.is_resource(&expr.ty) {
                    let made = Made {
                        resource: self.facts.resource_in(&expr.ty),
                        by: Maker::Built,
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
            // A way the function ends: what is held there is as at any
            // answer, and nothing goes on from it.
            ExprKind::Return(answered) => {
                let origins = self.value(answered);
                self.end(&origins, (place(expr), Leaving::Answering));
                self.left = true;
                Vec::new()
            }
            ExprKind::Try(tried) => {
                let origins = self.value(tried);
                self.end(&origins, (place(expr), Leaving::Asking));
                origins
            }
            ExprKind::If(condition, yes, no) => self.branches(expr, condition, yes, no),
            // A test whose names nothing sees only looks.
            ExprKind::Is(value, rows) => {
                self.subject(value);
                for guard in rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
                    self.lend(guard);
                }
                Vec::new()
            }
            ExprKind::Match(value, arms) => self.arms(expr, value, arms),
            // A block's bindings hold what they bind, as a body's do, and
            // its answer is what it is worth.
            ExprKind::Block(block) => self.block(block),
            ExprKind::Loop(looped) => self.looped(expr, looped),
            ExprKind::Continue(values) => {
                self.continued(expr, values);
                Vec::new()
            }
            ExprKind::Break(values) => {
                self.broke(expr, values);
                Vec::new()
            }
        }
    }

    fn block(&mut self, block: &d::Body) -> Vec<Origin> {
        for binding in &block.bindings {
            let origins = self.value(&binding.value);
            self.bind(&binding.pattern, &binding.value.ty, &origins);
        }
        self.value(&block.result)
    }

    /// A loop, whose round may run any number of times. What it carries is
    /// taken going in and held within a round, and what it walks is taken
    /// and held until walked. Each round must end as it began: what was held
    /// before the loop as it was, and what the round made used up or handed
    /// to the next. The lines after it go on from every way out, which must
    /// agree.
    fn looped(&mut self, expr: &d::Expr, looped: &d::Loop) -> Vec<Origin> {
        let outer = self.held.len();
        let within: Vec<Option<usize>> = looped
            .carried
            .iter()
            .map(|(initial, local, _)| self.carry(initial, *local))
            .collect();
        let walking = match &looped.head {
            d::LoopHead::For(_, list) => {
                let origins = self.value(list);
                self.held_by_none(origins)
            }
            d::LoopHead::While(_) => None,
        };
        self.loops.push(Frame {
            start: self.states(),
            outer,
            walking,
            continues: Vec::new(),
            breaks: Vec::new(),
        });
        let ended = self.round_begun(&looped.head, walking);
        let outer_left = std::mem::take(&mut self.left);
        self.block(&looped.body);
        self.left = outer_left;
        let frame = self.loops.pop().expect("the loop walked is the innermost");
        for (at, states) in &frame.continues {
            self.round_ended(&frame, *at, states);
        }
        self.after_loop(expr, looped, &within, ended, frame.breaks);
        self.block(&looped.rest)
    }

    /// A round begun by its head: a `while`'s condition holding, or a
    /// `for`'s next element bound. Answers how the loop ends, where the
    /// condition fails or nothing is left to walk.
    fn round_begun(&mut self, head: &d::LoopHead, walking: Option<usize>) -> Vec<State> {
        match head {
            d::LoopHead::While(condition) => {
                let outcome = self.condition(condition);
                self.set(&outcome.holds);
                outcome.fails
            }
            d::LoopHead::For(pattern, list) => {
                let mut ended = self.states();
                let mut origins = Vec::new();
                if let Some(walking) = walking {
                    ended[walking] = State::Empty;
                    origins.clone_from(&self.held[walking].origins);
                }
                if let Type::Named(_, arguments) = &list.ty
                    && let Some(element) = arguments.first()
                {
                    self.bind(pattern, element, &origins);
                }
                ended
            }
        }
    }

    /// Out of a loop, by its head as `ended` says or by each of `breaks`:
    /// what it carried held after it, by the names it binds there, and
    /// every way out met.
    fn after_loop(
        &mut self,
        expr: &d::Expr,
        looped: &d::Loop,
        within: &[Option<usize>],
        ended: Vec<State>,
        breaks: Vec<(Vec<State>, Vec<State>)>,
    ) {
        let after: Vec<Option<usize>> = within
            .iter()
            .zip(&looped.carried)
            .map(|(within, (_, _, after))| {
                let origins = self.held[(*within)?].origins.clone();
                let held = self.held_by_none(origins)?;
                self.locals.insert(*after, held);
                Some(held)
            })
            .collect();
        let mut states = self.extended(ended);
        for (within, after) in within.iter().zip(&after) {
            if let (Some(within), Some(after)) = (within, after) {
                states[*after] = states[*within];
                states[*within] = State::Empty;
            }
        }
        self.set(&states);
        for (states, handed) in breaks {
            let mut states = self.extended(states);
            for (after, state) in after.iter().zip(handed) {
                if let Some(after) = after {
                    states[*after] = state;
                }
            }
            self.agreed(expr, states);
        }
    }

    /// What a loop carries in `local`, taken from `initial`: held within
    /// each round, with whatever a round made and handed on.
    fn carry(&mut self, initial: &d::Expr, local: LocalId) -> Option<usize> {
        let mut origins = self.value(initial);
        if !self.facts.carries(&initial.ty) {
            return None;
        }
        let made = Made {
            resource: self.facts.resource_in(&initial.ty),
            by: Maker::Carried,
        };
        origins.push(Origin::Made(place(initial), made));
        let held = self.held_by_none(origins)?;
        self.locals.insert(local, held);
        Some(held)
    }

    /// `origins`, held by something not named, if there are any.
    fn held_by_none(&mut self, origins: Vec<Origin>) -> Option<usize> {
        if origins.is_empty() {
            return None;
        }
        self.held.push(Held {
            origins,
            state: State::Held,
        });
        Some(self.held.len() - 1)
    }

    /// `continue`: what the loop carries handed to the next round, which
    /// must begin as this one did.
    fn continued(&mut self, expr: &d::Expr, values: &[d::Expr]) {
        for value in values {
            let origins = self.value(value);
            if !is_local(value) {
                self.hold(&origins);
            }
        }
        let states = self.states();
        if let Some(frame) = self.loops.last_mut() {
            frame.continues.push((place(expr), states));
        }
        self.left = true;
    }

    /// `break`: what the loop carries handed to the lines after it. Any
    /// part of a list a `for` has not walked yet would be left held.
    fn broke(&mut self, expr: &d::Expr, values: &[d::Expr]) {
        let mut handed = Vec::new();
        for value in values {
            let state = if is_local(value) {
                let state = self
                    .local(value)
                    .map_or(State::Empty, |held| self.held[held].state);
                self.value(value);
                state
            } else if self.value(value).is_empty() {
                State::Empty
            } else {
                State::Held
            };
            handed.push(state);
        }
        let walking = self.loops.last().and_then(|frame| frame.walking);
        if let Some(walking) = walking
            && self.held[walking].state == State::Held
        {
            let resource = self.facts.called(self.resource_of(walking), "resource");
            self.refused.push(Refusal {
                at: Some(place(expr)),
                message: format!(
                    "a `break` leaves held the {resource}s its `for` has not walked yet"
                ),
                label: "leaves here".to_owned(),
                also: None,
                help: Some("walk every element, using each up".to_owned()),
            });
            self.held[walking].state = State::Empty;
        }
        let states = self.states();
        if let Some(frame) = self.loops.last_mut() {
            frame.breaks.push((states, handed));
        }
        self.left = true;
    }

    /// A round ending at `at` as `states` say: what was held before the
    /// loop must be as the round found it, and what the round made, and
    /// what the loop carried in, used up or handed on.
    fn round_ended(&mut self, frame: &Frame, at: Place, states: &[State]) {
        for (held, state) in states.iter().enumerate() {
            if Some(held) == frame.walking {
                continue;
            }
            if held < frame.outer {
                if frame.start[held].settled() != state.settled() {
                    let refusal = self.round_used_up(held, *state, at);
                    self.refused.push(refusal);
                }
            } else if *state == State::Held {
                let refusal = self.round_kept(held, at);
                self.refused.push(refusal);
            }
        }
    }

    /// What was held before a loop, used up by a round that goes on.
    fn round_used_up(&self, held: usize, state: State, at: Place) -> Refusal {
        let resource = self.facts.called(self.resource_of(held), "resource");
        let gone = match state {
            State::Gone(gone) => Some(gone),
            _ => None,
        };
        Refusal {
            at: gone.or(Some(at)),
            message: format!("a loop's round uses up a {resource} held before the loop"),
            label: "used up here".to_owned(),
            also: gone.map(|_| (at, "the next round would find it used up".to_owned())),
            help: Some("use it up after the loop, or `break` once it is used up".to_owned()),
        }
    }

    /// What a round made, or the loop carried in, still held where the
    /// round goes on.
    fn round_kept(&self, kept: usize, at: Place) -> Refusal {
        let made = self.held[kept]
            .origins
            .iter()
            .find_map(|origin| match origin {
                Origin::Made(place, made) => Some((*place, *made)),
                Origin::Parameter(_) => None,
            });
        let help =
            Some("use it up within the round, or hand it on in a name the loop carries".to_owned());
        let Some((made_at, made)) = made else {
            let resource = self.facts.called(self.resource_of(kept), "resource");
            return Refusal {
                at: Some(at),
                message: format!(
                    "a {resource} this round holds is neither used up nor carried to the next"
                ),
                label: "still held where the round goes on".to_owned(),
                also: None,
                help,
            };
        };
        let resource = self.facts.called(made.resource, "resource");
        let message = match made.by {
            Maker::Carried => format!(
                "the {resource} this loop carried into the round is neither used up nor handed to the next"
            ),
            Maker::Built | Maker::Call(_) => format!(
                "{} is neither used up nor carried to the next round",
                self.described(made)
            ),
        };
        Refusal {
            at: Some(made_at),
            message,
            label: made_label(made, &resource),
            also: (made_at != at).then(|| (at, "still held where the round goes on".to_owned())),
            help,
        }
    }

    /// The resource type what is held at `held` holds, as its origins say.
    fn resource_of(&self, held: usize) -> Option<Symbol> {
        self.held[held]
            .origins
            .iter()
            .find_map(|origin| match origin {
                Origin::Made(_, made) => made.resource,
                Origin::Parameter(parameter) => self.facts.program.functions[self.function]
                    .key
                    .signature
                    .parameters
                    .get(*parameter)
                    .and_then(|ty| self.facts.resource_in(ty)),
            })
    }

    /// A condition worked out: what is held where it holds, which a test
    /// in it holding takes apart into the names it binds, and where it
    /// fails. Along `&` and `|` each side is a condition, the right worked
    /// out only where the left has not decided.
    fn condition(&mut self, condition: &d::Expr) -> Outcome {
        match &condition.kind {
            ExprKind::Is(value, rows) => self.test(value, rows),
            ExprKind::DirectCall(callee, sides)
                if callee.name == self.facts.and
                    && let [left, right] = &sides[..] =>
            {
                self.both(condition, left, right)
            }
            ExprKind::DirectCall(callee, sides)
                if callee.name == self.facts.or
                    && let [left, right] = &sides[..] =>
            {
                self.either(condition, left, right)
            }
            _ => {
                self.lend(condition);
                Outcome::alike(self.states())
            }
        }
    }

    /// `left & right`: the right worked out where the left holds.
    fn both(&mut self, condition: &d::Expr, left: &d::Expr, right: &d::Expr) -> Outcome {
        let left = self.condition(left);
        self.set(&left.holds);
        let right = self.condition(right);
        // Where the right fails, the left's tests bound nothing anyone
        // sees: what they took apart is whole again, since a condition's
        // right side may use nothing up.
        let through = left.apart.undone(right.fails);
        let fails = self.met(condition, self.extended(left.fails), &through);
        Outcome {
            holds: right.holds,
            fails,
            apart: left.apart.and(right.apart),
        }
    }

    /// `left | right`: the right worked out where the left fails.
    fn either(&mut self, condition: &d::Expr, left: &d::Expr, right: &d::Expr) -> Outcome {
        let left = self.condition(left);
        self.set(&left.fails);
        let right = self.condition(right);
        let mut holds = self.met(condition, self.extended(left.holds), &right.holds);
        // A name both sides bind is one name past them, holding what
        // either side's test bound to it.
        for (local, from_left) in &left.apart.bound {
            if let Some((_, from_right)) = right.apart.bound.iter().find(|(each, _)| each == local)
            {
                let origins = self.held[*from_left].origins.clone();
                self.held[*from_right].origins.extend(origins);
                holds[*from_left] = State::Empty;
            }
        }
        Outcome {
            holds,
            fails: right.fails,
            apart: left.apart.and(right.apart),
        }
    }

    /// A test, `value is pattern`, its rows each a choice of the pattern's
    /// alternatives. Where it holds, the value is taken apart if the
    /// pattern names a part holding a resource; where it fails, it is as
    /// it was. Either way, a value the test shows to hold no resource holds
    /// none.
    fn test(&mut self, value: &d::Expr, rows: &[(Pattern, Option<d::Expr>)]) -> Outcome {
        let whole = self.subject(value);
        for guard in rows.iter().filter_map(|(_, guard)| guard.as_ref()) {
            self.lend(guard);
        }
        let mut fails = self.states();
        let Some(whole) = whole else {
            return Outcome::alike(fails);
        };
        if fails[whole] == State::Held && !self.remainder_carries(rows, &value.ty) {
            fails[whole] = State::Empty;
        }
        let patterns: Vec<&Pattern> = rows.iter().map(|(pattern, _)| pattern).collect();
        let apart = self.matched(whole, value, &patterns);
        Outcome {
            holds: self.states(),
            fails: self.extended(fails),
            apart,
        }
    }

    /// What a test or arms look at, held: the held thing a local names, or
    /// what the value works out, held by nothing named.
    fn subject(&mut self, value: &d::Expr) -> Option<usize> {
        if !self.facts.carries(&value.ty) {
            self.lend(value);
            return None;
        }
        if is_local(value) {
            self.look(value);
            return self.local(value);
        }
        let origins = self.value(value);
        self.held_by_none(origins)
    }

    /// The value held at `whole`, matched by one of `patterns`: taken
    /// apart, its parts held by the names one binds, where one names a part
    /// holding a resource, and otherwise left whole, holding none where no
    /// pattern matches a value holding one.
    fn matched(&mut self, whole: usize, value: &d::Expr, patterns: &[&Pattern]) -> Apart {
        let ty = &value.ty;
        let start = self.held.len();
        let mut took = Vec::new();
        if self.held[whole].state == State::Held {
            if let Some(pattern) = patterns.iter().find(|p| self.names_resource(p, ty)) {
                took.push((whole, State::Held));
                self.held[whole].state = State::Gone(place(value));
                self.taken_apart.insert(place(value));
                let origins = self.held[whole].origins.clone();
                self.bind(pattern, ty, &origins);
            } else if !patterns.iter().any(|p| self.matched_carries(p, ty)) {
                self.held[whole].state = State::Empty;
            }
        }
        let bound = self
            .locals
            .iter()
            .filter(|(_, held)| **held >= start)
            .map(|(local, held)| (*local, *held))
            .collect();
        Apart {
            took,
            parts: (start..self.held.len()).collect(),
            bound,
        }
    }

    /// Whether `pattern` binds a name to a part of a value of `ty` that
    /// holds a resource.
    fn names_resource(&self, pattern: &Pattern, ty: &Type) -> bool {
        match pattern {
            Pattern::Bind(_) => self.facts.carries(ty),
            Pattern::As(_, pattern) => self.facts.carries(ty) || self.names_resource(pattern, ty),
            Pattern::Constructor(..) if self.is_resource(ty) => false,
            Pattern::Record(patterns) => {
                let Type::Record(fields) = ty else {
                    return false;
                };
                patterns.iter().any(|(name, pattern)| {
                    fields
                        .iter()
                        .find(|(each, _)| each == name)
                        .is_some_and(|(_, field)| self.names_resource(pattern, field))
                })
            }
            _ => self
                .facts
                .parts(pattern, ty)
                .iter()
                .any(|(pattern, part)| self.names_resource(pattern, part)),
        }
    }

    /// Whether a value of `ty` that `pattern` matches may hold a resource.
    fn matched_carries(&self, pattern: &Pattern, ty: &Type) -> bool {
        match pattern {
            Pattern::As(_, pattern) => self.matched_carries(pattern, ty),
            Pattern::Constructor(constructor, patterns) if !self.is_resource(ty) => {
                self.facts.fields(*constructor, ty).map_or_else(
                    || self.facts.carries(ty),
                    |fields| {
                        patterns
                            .iter()
                            .zip(&fields)
                            .any(|(pattern, field)| self.matched_carries(pattern, field))
                    },
                )
            }
            Pattern::Product(patterns) => match ty {
                Type::Tuple(members) => patterns
                    .iter()
                    .zip(members)
                    .any(|(pattern, member)| self.matched_carries(pattern, member)),
                _ => self.facts.carries(ty),
            },
            _ => self.facts.carries(ty),
        }
    }

    /// Whether a value of `ty` that no row matches may hold a resource: a
    /// row taking apart a constructor leaves the others, and that one where
    /// its parts are tested; a row taking apart a list's first element and
    /// the rest leaves an empty list.
    fn remainder_carries(&self, rows: &[(Pattern, Option<d::Expr>)], ty: &Type) -> bool {
        if !self.facts.carries(ty) {
            return false;
        }
        let whole =
            |(pattern, guard): &(Pattern, Option<d::Expr>)| guard.is_none() && irrefutable(pattern);
        if rows.iter().any(whole) {
            return false;
        }
        let emptied = rows.iter().any(|(pattern, guard)| {
            guard.is_none()
                && matches!(pattern, Pattern::List(elements, Some(rest))
                    if elements.len() == 1 && irrefutable(&elements[0]) && irrefutable(rest))
        });
        if emptied {
            return false;
        }
        let Some(constructors) = self.facts.constructors_of(ty) else {
            return true;
        };
        constructors.iter().any(|constructor| {
            let covered = rows.iter().any(|(pattern, guard)| {
                guard.is_none()
                    && matches!(unnamed(pattern), Pattern::Constructor(each, patterns)
                        if each == constructor && patterns.iter().all(irrefutable))
            });
            !covered
                && self
                    .facts
                    .fields(*constructor, ty)
                    .is_none_or(|fields| fields.iter().any(|field| self.facts.carries(field)))
        })
    }

    /// The state of everything held.
    fn states(&self) -> Vec<State> {
        self.held.iter().map(|held| held.state).collect()
    }

    /// Everything held as `states` says, what came after them as it is.
    fn set(&mut self, states: &[State]) {
        for (held, state) in self.held.iter_mut().zip(states) {
            held.state = *state;
        }
    }

    /// `states`, with what was held since not there.
    fn extended(&self, mut states: Vec<State>) -> Vec<State> {
        states.resize(self.held.len(), State::Empty);
        states
    }

    /// Two ways a condition goes on, met: what one used up the other must
    /// have too.
    fn met(&mut self, condition: &d::Expr, one: Vec<State>, other: &[State]) -> Vec<State> {
        self.set(other);
        self.agreed(condition, one);
        self.states()
    }

    /// An `if`: its condition worked out, its `then` walked from where it
    /// holds and its `else` from where it fails, and what either answers is
    /// what the `if` is worth. What one branch uses up the other must too,
    /// since after the `if` it is gone or held, not both.
    fn branches(
        &mut self,
        expr: &d::Expr,
        condition: &d::Expr,
        yes: &d::Expr,
        no: &d::Expr,
    ) -> Vec<Origin> {
        let outcome = self.condition(condition);
        let outer = std::mem::take(&mut self.left);
        self.set(&outcome.holds);
        let mut answered = self.value(yes);
        let yes_left = std::mem::take(&mut self.left);
        let taken = self.restored(&outcome.fails);
        answered.extend(self.value(no));
        let no_left = std::mem::take(&mut self.left);
        self.joined(expr, vec![(taken, yes_left)], no_left);
        self.left = outer || (yes_left && no_left);
        answered
    }

    /// The branches walked, each what it left and whether it left the way
    /// it was on, met with the one walked last, whose states are the
    /// current ones: those that went on must agree, and one that left has
    /// no say.
    fn joined(&mut self, expr: &d::Expr, others: Vec<(Vec<State>, bool)>, last_left: bool) {
        let mut left = last_left;
        for (taken, other_left) in others {
            if other_left {
                continue;
            }
            if left {
                self.set(&taken);
                left = false;
                continue;
            }
            self.agreed(expr, taken);
        }
    }

    /// An `is` with arms: each arm walked from what was held before it, as
    /// an `if`'s branches are, its pattern taking the value apart as a
    /// test's does and its guard worked out; every arm must use up what
    /// the others do.
    fn arms(&mut self, expr: &d::Expr, value: &d::Expr, arms: &[d::Arm]) -> Vec<Origin> {
        let whole = self.subject(value);
        let before = self.states();
        let outer = std::mem::take(&mut self.left);
        let mut answered = Vec::new();
        let mut taken = Vec::new();
        let mut left = false;
        for (at, arm) in arms.iter().enumerate() {
            if at > 0 {
                taken.push((self.restored(&before), left));
            }
            // Each row asks the arm's guard after its own literals'; the
            // first is worked out as a condition, the others looked at.
            for guard in arm
                .rows
                .iter()
                .skip(1)
                .filter_map(|(_, guard)| guard.as_ref())
            {
                self.lend(guard);
            }
            if let Some(whole) = whole {
                let patterns: Vec<&Pattern> = arm.rows.iter().map(|(pattern, _)| pattern).collect();
                self.matched(whole, value, &patterns);
            }
            if let Some((_, Some(guard))) = arm.rows.first() {
                self.guarded(guard);
            }
            answered.extend(self.value(&arm.body));
            left = std::mem::take(&mut self.left);
        }
        let every = left && taken.iter().all(|(_, left)| *left);
        self.joined(expr, taken, left);
        self.left = outer || every;
        answered
    }

    /// What was held before a branch, and how a branch walked since left
    /// it, put back to what it was.
    fn restored(&mut self, before: &[State]) -> Vec<State> {
        let taken = self.held[..before.len()]
            .iter()
            .map(|held| held.state)
            .collect();
        for (held, state) in self.held.iter_mut().zip(before) {
            held.state = *state;
        }
        taken
    }

    /// What one branch left, `taken`, agreed with what the one walked last
    /// left, refusing what one used up and the other did not.
    fn agreed(&mut self, expr: &d::Expr, taken: Vec<State>) {
        for (at, yes) in taken.into_iter().enumerate() {
            self.held[at].state = match (yes, self.held[at].state) {
                (State::Empty, other) | (other, State::Empty) => other,
                (State::Held, State::Gone(gone)) | (State::Gone(gone), State::Held) => {
                    let refusal = self.one_branch(expr, at, gone);
                    self.refused.push(refusal);
                    State::Gone(gone)
                }
                (State::Gone(gone), _) | (_, State::Gone(gone)) => State::Gone(gone),
                (State::Unknown, _) | (_, State::Unknown) => State::Unknown,
                (State::Held, State::Held) => State::Held,
            };
        }
    }

    /// A resource held at `held` used up at `gone`, in one branch of the
    /// `if` at `expr` and not the other, one arm and not another, or on
    /// one way out of a loop and not another.
    fn one_branch(&self, expr: &d::Expr, held: usize, gone: Place) -> Refusal {
        let resource = self.facts.called(self.resource_of(held), "resource");
        if matches!(expr.kind, ExprKind::Loop(..)) {
            return Refusal {
                at: Some(gone),
                message: format!(
                    "this {resource} is used up on one way out of a loop and not another"
                ),
                label: self.gone_label(gone),
                also: Some((place(expr), "another way out still holds it".to_owned())),
                help: Some("use it up on every way out of the loop, or on none".to_owned()),
            };
        }
        if matches!(expr.kind, ExprKind::Match(..)) {
            return Refusal {
                at: Some(gone),
                message: format!(
                    "this {resource} is used up in one arm of an `is` and not another"
                ),
                label: self.gone_label(gone),
                also: Some((place(expr), "another arm still holds it".to_owned())),
                help: Some("use it up in every arm, or in none".to_owned()),
            };
        }
        Refusal {
            at: Some(gone),
            message: format!(
                "this {resource} is used up in one branch of an `if` and not the other"
            ),
            label: self.gone_label(gone),
            also: Some((place(expr), "the other branch still holds it".to_owned())),
            help: Some("use it up in both branches, or in neither".to_owned()),
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
                by: Maker::Call(callee.name),
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
                message: "a guard uses up a resource".to_owned(),
                label: "used up here".to_owned(),
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
            State::Unknown | State::Empty => Vec::new(),
        }
    }

    /// A resource used again at `expr`, which was used up at `gone`.
    fn used_twice(&self, expr: &d::Expr, gone: Place) -> Refusal {
        let resource = self
            .facts
            .called(self.facts.resource_in(&expr.ty), "resource");
        let message = if self.taken_apart.contains(&gone) {
            format!("this {resource} is read whole after a test took it apart")
        } else {
            format!("this {resource} is used after it was used up")
        };
        Refusal {
            at: Some(place(expr)),
            message,
            label: "used again here".to_owned(),
            also: Some((gone, self.gone_label(gone))),
            help: None,
        }
    }

    /// What happened where something held went: used up, or taken apart
    /// by a test, its parts held by the names it bound.
    fn gone_label(&self, gone: Place) -> String {
        if self.taken_apart.contains(&gone) {
            "taken apart here".to_owned()
        } else {
            "used up here".to_owned()
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
                    (State::Gone(_) | State::Unknown | State::Empty, _) => {}
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
        let what = self.described(made);
        let (still, help) = match leaving {
            Leaving::Asking => (
                "still held where this `?` leaves".to_owned(),
                "use it up before asking `?` of anything: keep what a step answers, use it up, \
                 then ask `?` of what was kept",
            ),
            Leaving::Answering => (
                format!("still held where `{name}` answers"),
                "use it up, as `close!` does, or answer it",
            ),
        };
        Refusal {
            at: Some(at),
            message: format!(
                "{what} is neither used up nor answered on every way `{name}` goes on"
            ),
            label: made_label(made, &resource),
            also: (end != at).then_some((end, still)),
            help: Some(help.to_owned()),
        }
    }

    /// Which resource `made` is, in words.
    fn described(&self, made: Made) -> String {
        let resource = self.facts.called(made.resource, "resource");
        match made.by {
            Maker::Built => format!("the {resource} built here"),
            Maker::Call(by) => format!("the {resource} from `{}`", self.facts.spelled(by)),
            Maker::Carried => format!("the {resource} this loop carries"),
        }
    }
}

/// A parameter's position as a word: `first` for nought.
fn ordinal(index: usize) -> String {
    const WORDS: [&str; 10] = [
        "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth",
        "tenth",
    ];
    WORDS
        .get(index)
        .map_or_else(|| format!("{}th", index + 1), |word| (*word).to_owned())
}

/// What is at the place `made` was made.
fn made_label(made: Made, resource: &str) -> String {
    match made.by {
        Maker::Carried => format!("this loop carries the {resource}"),
        Maker::Built | Maker::Call(_) => format!("this {resource} is made here"),
    }
}

/// Whether `pattern` matches every value of its type.
fn irrefutable(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Bind(_) | Pattern::Wild => true,
        Pattern::As(_, pattern) => irrefutable(pattern),
        Pattern::Product(patterns) => patterns.iter().all(irrefutable),
        Pattern::Record(patterns) => patterns.iter().all(|(_, pattern)| irrefutable(pattern)),
        _ => false,
    }
}

/// `pattern` without the names it gives the whole.
fn unnamed(pattern: &Pattern) -> &Pattern {
    match pattern {
        Pattern::As(_, pattern) => unnamed(pattern),
        other => other,
    }
}

const fn is_local(expr: &d::Expr) -> bool {
    matches!(expr.kind, ExprKind::Local(_))
}

const fn place(expr: &d::Expr) -> Place {
    (expr.module, expr.span)
}
