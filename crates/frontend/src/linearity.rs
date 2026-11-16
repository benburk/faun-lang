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
//! A name holding a record holds each field that holds a resource on its
//! own, so reading one field takes or lends that field alone, and a field
//! holding none is read freely.
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
//! none where the test shows it cannot. A branch of type `[]`
//! where the rest of its `if` or `is` answers never answers: it is a way the
//! function ends, as a `return` is, so it uses up what it holds there and has
//! no say in what the branches that answer agree on.
//!
//! This reads the first-order program, where every function value has
//! become the definition it was handed to and every type is known, so a
//! resource is never hidden behind a type variable or a callback.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use faun_core::platform::Routines;

use crate::context::Context;
use crate::diagnostic::Diagnostic;
use crate::first_order::{self as d, ExprKind};
use crate::hir::LocalId;
use crate::specialize::{Connective, FunctionKey, Pattern, Type, surface_type};
use crate::{ModuleId, Symbol, Symbols};

mod shapes;

/// Refuse a program that drops a resource, uses one twice, or leaves one
/// behind.
///
/// # Errors
/// The first such use, where it was written.
pub(crate) fn check(
    program: &d::Program,
    declared: &crate::typed::Program,
    cx: &Context,
    routines: &Routines,
) -> Result<(), Diagnostic> {
    let facts = Facts::of(program, declared, cx, routines);
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
    declared: &crate::typed::Program,
    symbols: &Symbols,
    routines: &Routines,
) -> HashSet<Symbol> {
    declared
        .functions
        .iter()
        .filter_map(|function| {
            let crate::typed::Definition::External(provider) = function.definition else {
                return None;
            };
            let routine = routines.get(symbols.text(provider))?;
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
    cx: &'a Context,
    resources: HashSet<Symbol>,
    /// Which function each key is.
    functions: HashMap<&'a FunctionKey, usize>,
    /// Each constructor's owner and fields, as its declaration says.
    constructors: HashMap<Symbol, (Symbol, Vec<crate::hir::Type>)>,
    /// Which parameter of each routine a target answers for is used up.
    uses_up: Vec<Option<usize>>,
    carries: RefCell<HashMap<Type, bool>>,
    /// A list's constructors, which a list pattern is written over.
    list_nil: Symbol,
    list_cons: Symbol,
}

impl<'a> Facts<'a> {
    fn of(
        program: &'a d::Program,
        declared: &crate::typed::Program,
        cx: &'a Context,
        routines: &Routines,
    ) -> Self {
        let prelude = &cx.prelude;
        let uses_up = program
            .functions
            .iter()
            .map(|function| {
                let d::Definition::External(provider) = function.definition else {
                    return None;
                };
                let routine = routines.get(cx.symbols.text(provider))?;
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
            cx,
            resources: resources(declared, &cx.symbols, routines),
            functions: program
                .functions
                .iter()
                .enumerate()
                .map(|(at, function)| (&function.key, at))
                .collect(),
            constructors,
            uses_up,
            carries: RefCell::default(),
            list_nil: prelude.list_nil,
            list_cons: prelude.list_cons,
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
            let mut walk = Walk::new(self, known, at, place(answering(&clause.body.result)));
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

    /// Where a parameter is taken on one way and kept on another, or
    /// partly taken on one way: the first place it is taken, and the first
    /// way it is kept.
    fn disagreement(&self, function: usize, parameter: usize, paths: &[Path]) -> Refusal {
        // A way that takes some of it and keeps the rest is the one to name.
        let partly = paths.iter().find(|path| path.partly.contains(&parameter));
        let paths = partly.map_or(paths, std::slice::from_ref);
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
        let (message, help) = disagreeing(name, &resource, parameter, partly.is_some());
        Refusal {
            at: taken.or_else(|| kept.map(|(at, _)| at)),
            message,
            label,
            also: kept.filter(|_| taken.is_some()).map(|(at, leaving)| {
                let still = match leaving {
                    Leaving::Asking => "still held where this `?` leaves".to_owned(),
                    Leaving::Answering => format!("still held where `{name}` answers"),
                    Leaving::Ending => "still held where this never answers".to_owned(),
                };
                (at, still)
            }),
            help: Some(help.to_owned()),
        }
    }

    fn is_resource(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named(name, _) if self.resources.contains(name))
    }

    /// Whether a value of `ty` holds a resource anywhere in it: whether any
    /// type its values are built of is one. Asked as a search over those
    /// types, so a type reaching itself is answered by what else it reaches,
    /// whichever is asked first. A search finding none has seen everything
    /// each type it passed reaches, so each of those holds none either.
    fn carries(&self, ty: &Type) -> bool {
        if let Some(&known) = self.carries.borrow().get(ty) {
            return known;
        }
        let mut waiting = vec![ty.clone()];
        let mut seen = HashSet::new();
        let mut found = false;
        while let Some(next) = waiting.pop() {
            if let Some(&known) = self.carries.borrow().get(&next) {
                found |= known;
                if found {
                    break;
                }
                continue;
            }
            if !seen.insert(next.clone()) {
                continue;
            }
            match &next {
                Type::Named(name, _) if self.resources.contains(name) => {
                    found = true;
                    break;
                }
                Type::Named(..) => waiting.extend(self.fields_of_every(&next)),
                Type::Function(..) => {}
                Type::Variants(tags) => {
                    waiting.extend(tags.iter().flat_map(|(_, fields)| fields.iter().cloned()));
                }
                Type::Record(fields) => waiting.extend(fields.iter().map(|(_, f)| f.clone())),
                Type::Tuple(members) => waiting.extend(members.iter().cloned()),
            }
        }
        let mut known = self.carries.borrow_mut();
        if found {
            known.insert(ty.clone(), true);
        } else {
            known.extend(seen.into_iter().map(|each| (each, false)));
        }
        found
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

    /// The fields of a record, or of a type wrapping one, which a value of
    /// `ty` has fields of.
    fn record_fields(&self, ty: &Type) -> Option<Vec<(Symbol, Type)>> {
        match ty {
            Type::Record(fields) => Some(fields.clone()),
            Type::Named(name, _) if !self.resources.contains(name) => {
                let wrapper = self.program.data.get(name)?.wrapper.as_ref()?;
                match self.fields(wrapper.constructor, ty)?.as_slice() {
                    [Type::Record(fields)] => Some(fields.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Whether a field of a value of `ty` other than `field` holds a
    /// resource.
    fn others_carry(&self, ty: &Type, field: Symbol) -> bool {
        self.record_fields(ty).is_some_and(|fields| {
            fields
                .iter()
                .any(|(each, ty)| *each != field && self.carries(ty))
        })
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
        self.cx.symbols.spelling(name)
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
            Some((module, span)) => self.cx.diagnostic(module, span, refusal.message),
            None => Diagnostic::new(refusal.message),
        };
        diagnostic = diagnostic.label(refusal.label);
        if let Some(((module, span), text)) = refusal.also {
            let location = self.cx.location(module, span);
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
#[derive(Clone, Copy, Debug, PartialEq)]
enum Origin {
    /// Some of what the function's parameter at this place was handed.
    Parameter(usize),
    /// Made here: answered by the call, or built by the constructor, written
    /// at this place.
    Made(Place, Made),
}

/// What made a resource, for saying which one is meant.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Made {
    /// The resource's type, the first one the value holds.
    resource: Option<Symbol>,
    by: Maker,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Maker {
    /// Built by a constructor.
    Built,
    /// Answered by this function.
    Call(Symbol),
}

/// How one way a function goes on ends.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Leaving {
    /// With what the function answers.
    Answering,
    /// By `?`, with the error.
    Asking,
    /// Where a branch never answers, as a call answering `[]` does.
    Ending,
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
    /// A record whose fields are held each on its own holds none itself.
    Empty,
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

/// One way a function goes on, to its answer or out by `?`: which
/// parameters' resources it took, where, and which it kept.
struct Path {
    end: (Place, Leaving),
    taken: Vec<(usize, Option<Place>)>,
    kept: Vec<usize>,
    /// Parameters a record of which is held in part: a field used up and
    /// another still held.
    partly: Vec<usize>,
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
    /// Whether the branch walked last left by `return`, so that nothing
    /// after it is held as it left things.
    left: bool,
    /// Where a test took apart what it tested, which it holds no longer.
    taken_apart: HashSet<Place>,
    /// A named record's fields holding a resource, each held on its own,
    /// so that reading one leaves the others.
    fields: HashMap<usize, Vec<(Symbol, usize)>>,
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
            taken_apart: HashSet::new(),
            fields: HashMap::new(),
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
        let answer = self.block(body);
        self.end(
            &answer,
            (place(answering(&body.result)), Leaving::Answering),
        );
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
                let held = self.named(origins, ty);
                self.locals.insert(*local, held);
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
            Pattern::Constructor(_, _) if self.facts.is_resource(ty) => self.hold(origins),
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

    /// What a name holds of a value of `ty` holding `origins`: a record's
    /// fields holding a resource each held on its own, and anything else
    /// whole.
    fn named(&mut self, origins: &[Origin], ty: &Type) -> usize {
        self.named_within(origins, ty, &mut Vec::new())
    }

    /// [`Self::named`], within the records `within` holds: a record found
    /// inside itself, which no value is, is held whole there.
    fn named_within(&mut self, origins: &[Origin], ty: &Type, within: &mut Vec<Type>) -> usize {
        self.held.push(Held {
            origins: origins.to_vec(),
            state: State::Held,
        });
        let held = self.held.len() - 1;
        if within.contains(ty) {
            return held;
        }
        let Some(fields) = self.facts.record_fields(ty) else {
            return held;
        };
        let fields: Vec<(Symbol, Type)> = fields
            .into_iter()
            .filter(|(_, field)| self.facts.carries(field))
            .collect();
        if fields.is_empty() {
            return held;
        }
        self.held[held].state = State::Empty;
        within.push(ty.clone());
        let parts = fields
            .into_iter()
            .map(|(name, field)| (name, self.named_within(origins, &field, within)))
            .collect();
        within.pop();
        self.fields.insert(held, parts);
        held
    }

    /// Where what is held at `held` is: its fields' places, where it is a
    /// record held field by field, and otherwise itself.
    fn leaves(&self, held: usize) -> Vec<usize> {
        self.fields.get(&held).map_or_else(
            || vec![held],
            |fields| {
                fields
                    .iter()
                    .flat_map(|(_, field)| self.leaves(*field))
                    .collect()
            },
        )
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
                if self.facts.is_resource(&expr.ty) {
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
            // A field holding no resource is read freely off a name.
            ExprKind::Project(receiver, _) if !self.facts.carries(&expr.ty) => {
                if !is_local(receiver) {
                    self.lend(receiver);
                }
                Vec::new()
            }
            ExprKind::Project(..) if is_local(expr) => self.take(expr),
            // The value read from is held by nothing named, and what its
            // other fields hold is dropped with it.
            ExprKind::Project(receiver, field) => {
                let origins = self.value(receiver);
                if self.facts.others_carry(&receiver.ty, *field) {
                    self.hold(&origins);
                }
                origins
            }
            ExprKind::Widen(receiver) => self.value(receiver),
            ExprKind::DirectCall(callee, arguments) => self.call(expr, callee, arguments),
            // Worked out for its value, what a test in it binds is seen by
            // nothing after it: each side only looks.
            ExprKind::Connective(_, left, right) => {
                self.lend(left);
                self.lend(right);
                Vec::new()
            }
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
        }
    }

    fn block(&mut self, block: &d::Body) -> Vec<Origin> {
        for binding in &block.bindings {
            if let Pattern::Bind(local) = &binding.pattern
                && let Some(held) = self.built(&binding.value)
            {
                self.locals.insert(*local, held);
                continue;
            }
            let origins = self.value(&binding.value);
            self.bind(&binding.pattern, &binding.value.ty, &origins);
        }
        self.value(&block.result)
    }

    /// A record written out, as a name holds it: each field holding a
    /// resource held on its own, holding what its own value does. `None`
    /// where `expr` is not a record with such a field.
    fn built(&mut self, expr: &d::Expr) -> Option<usize> {
        let ExprKind::Record(fields) = &expr.kind else {
            return None;
        };
        if !fields
            .iter()
            .any(|(_, field)| self.facts.carries(&field.ty))
        {
            return None;
        }
        let mut parts = Vec::new();
        let mut origins: Vec<Origin> = Vec::new();
        for (name, field) in fields {
            if !self.facts.carries(&field.ty) {
                let made = self.value(field);
                self.hold(&made);
                continue;
            }
            let held = self.built(field).unwrap_or_else(|| {
                let made = self.value(field);
                self.named(&made, &field.ty)
            });
            for origin in &self.held[held].origins {
                if !origins.contains(origin) {
                    origins.push(*origin);
                }
            }
            parts.push((*name, held));
        }
        self.held.push(Held {
            origins,
            state: State::Empty,
        });
        let held = self.held.len() - 1;
        self.fields.insert(held, parts);
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
            ExprKind::Connective(Connective::And, left, right) => self.both(condition, left, right),
            ExprKind::Connective(Connective::Or, left, right) => {
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
                let lefts = self.leaves(*from_left);
                let rights = self.leaves(*from_right);
                for (from_left, from_right) in lefts.into_iter().zip(rights) {
                    let origins = self.held[from_left].origins.clone();
                    self.held[from_right].origins.extend(origins);
                    holds[from_left] = State::Empty;
                }
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
        let unguarded = rows.iter().filter(|(_, guard)| guard.is_none());
        let unmatched = unguarded.map(|(pattern, _)| pattern);
        let leaves = self.leaves(whole);
        if leaves.iter().all(|leaf| fails[*leaf] == State::Held)
            && !self.facts.unmatched_carries(unmatched, &value.ty)
        {
            for leaf in leaves {
                fails[leaf] = State::Empty;
            }
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
        let leaves = self.leaves(whole);
        if leaves
            .iter()
            .all(|leaf| self.held[*leaf].state == State::Held)
        {
            if let Some(pattern) = patterns.iter().find(|p| self.names_resource(p, ty)) {
                for leaf in leaves {
                    took.push((leaf, State::Held));
                    self.held[leaf].state = State::Gone(place(value));
                }
                self.taken_apart.insert(place(value));
                let origins = self.held[whole].origins.clone();
                self.bind(pattern, ty, &origins);
            } else if !patterns.iter().any(|p| self.facts.matched_carries(p, ty)) {
                for leaf in leaves {
                    self.held[leaf].state = State::Empty;
                }
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
            Pattern::Constructor(..) if self.facts.is_resource(ty) => false,
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
        self.never_answered(expr, yes);
        let yes_left = std::mem::take(&mut self.left);
        let taken = self.restored(&outcome.fails);
        answered.extend(self.value(no));
        self.never_answered(expr, no);
        let no_left = std::mem::take(&mut self.left);
        self.joined(expr, vec![(taken, yes_left)], no_left);
        self.left = outer || (yes_left && no_left);
        answered
    }

    /// A branch of `join` whose type is `[]` where the join's is not: it
    /// never answers, so it is a way the function ends, as a `return` is.
    /// What it holds is held where it ends, and it has no say in what the
    /// branches that answer agree on. Where every branch is `[]`, they
    /// agree as any branches do, and the function ends after them.
    fn never_answered(&mut self, join: &d::Expr, branch: &d::Expr) {
        let empty = Type::empty();
        if self.left || branch.ty != empty || join.ty == empty {
            return;
        }
        self.end(&[], (place(answering(branch)), Leaving::Ending));
        self.left = true;
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
            // Each row asks the arm's guard after its own literals', and the
            // rows bind the same names, so what the first's guard takes
            // apart every row's does: it is worked out as a condition, and
            // the others looked at.
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
            self.never_answered(expr, &arm.body);
            left = std::mem::take(&mut self.left);
        }
        let every = left && taken.iter().all(|(_, left)| *left);
        self.joined(expr, taken, left);
        self.left = outer || every;
        answered
    }

    /// How a branch walked since left everything, and what was held before
    /// it put back to what it was: what the branch held since is not there
    /// for the next one.
    fn restored(&mut self, before: &[State]) -> Vec<State> {
        let taken = self.states();
        for (at, held) in self.held.iter_mut().enumerate() {
            held.state = before.get(at).copied().unwrap_or(State::Empty);
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
    /// `if` at `expr` and not the other, or one arm and not another.
    fn one_branch(&self, expr: &d::Expr, held: usize, gone: Place) -> Refusal {
        let resource = self.facts.called(self.resource_of(held), "resource");
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
                        for leaf in self.leaves(held) {
                            self.held[leaf].state = State::Unknown;
                        }
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
        let gone = self
            .leaves(held)
            .into_iter()
            .find_map(|leaf| match self.held[leaf].state {
                State::Gone(gone) => Some(gone),
                _ => None,
            });
        if let Some(gone) = gone {
            let refusal = self.used_twice(expr, gone);
            self.refused.push(refusal);
        }
    }

    /// A local taken whole: what it held, which it holds no longer.
    fn take(&mut self, expr: &d::Expr) -> Vec<Origin> {
        let Some(held) = self.local(expr) else {
            return Vec::new();
        };
        let mut origins = Vec::new();
        let mut used_twice = None;
        for leaf in self.leaves(held) {
            match self.held[leaf].state {
                State::Held => {
                    self.held[leaf].state = State::Gone(place(expr));
                    for origin in &self.held[leaf].origins {
                        if !origins.contains(origin) {
                            origins.push(*origin);
                        }
                    }
                }
                State::Gone(gone) => {
                    used_twice.get_or_insert(gone);
                }
                State::Unknown | State::Empty => {}
            }
        }
        if let Some(gone) = used_twice {
            let refusal = self.used_twice(expr, gone);
            self.refused.push(refusal);
        }
        origins
    }

    /// A resource used again at `expr`, which was used up at `gone`.
    fn used_twice(&self, expr: &d::Expr, gone: Place) -> Refusal {
        let resource = self
            .facts
            .called(self.facts.resource_in(&expr.ty), "resource");
        let partly = self
            .local(expr)
            .is_some_and(|held| self.fields.contains_key(&held));
        let message = if self.taken_apart.contains(&gone) {
            format!("this {resource} is read whole after a test took it apart")
        } else if partly {
            format!("this value is read whole after a {resource} in it was used up")
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

    /// Which held thing a name, or a field read off one, is, where it holds
    /// any.
    fn local(&self, expr: &d::Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::Local(local) => self.locals.get(local).copied(),
            ExprKind::Project(receiver, field) if self.facts.carries(&expr.ty) => {
                let whole = self.local(receiver)?;
                let Some(fields) = self.fields.get(&whole) else {
                    return Some(whole);
                };
                fields
                    .iter()
                    .find(|(each, _)| each == field)
                    .map(|(_, held)| *held)
            }
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
            partly: self.partly_held(),
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

    /// The parameters a record of which is held in part: a field holding a
    /// resource used up, and another still held.
    fn partly_held(&self) -> Vec<usize> {
        let mut partly = Vec::new();
        for record in self.fields.keys() {
            let states: Vec<State> = self
                .leaves(*record)
                .into_iter()
                .map(|leaf| self.held[leaf].state)
                .collect();
            let gone = states.iter().any(|state| matches!(state, State::Gone(_)));
            if gone && states.contains(&State::Held) {
                for origin in &self.held[*record].origins {
                    if let Origin::Parameter(parameter) = origin {
                        partly.push(*parameter);
                    }
                }
            }
        }
        partly
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
            Leaving::Ending => (
                "still held where this never answers".to_owned(),
                "use it up before, as `close!` does",
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

/// What a function taking its parameter's resource on some ways and not
/// others is told, or one taking some of what it holds and keeping the
/// rest, and how to mend it.
fn disagreeing(
    name: &str,
    resource: &str,
    parameter: usize,
    partly: bool,
) -> (String, &'static str) {
    let ordinal = ordinal(parameter);
    if partly {
        (
            format!(
                "`{name}` uses up a {resource} its {ordinal} parameter holds and keeps another"
            ),
            "use up every one it holds, or none, where the caller does",
        )
    } else {
        (
            format!(
                "`{name}` uses up the {resource} in its {ordinal} parameter on some ways it goes on and not others"
            ),
            "use it up on every way the function goes on, or on none, where the caller does",
        )
    }
}

/// What is at the place `made` was made.
fn made_label(made: Made, resource: &str) -> String {
    match made.by {
        Maker::Built | Maker::Call(_) => format!("this {resource} is made here"),
    }
}

/// Whether `expr` is a name, or a field read off one.
fn is_local(expr: &d::Expr) -> bool {
    match &expr.kind {
        ExprKind::Local(_) => true,
        ExprKind::Project(receiver, _) => is_local(receiver),
        _ => false,
    }
}

const fn place(expr: &d::Expr) -> Place {
    (expr.module, expr.span)
}

/// Where `expr` answers, as a reader finds it: the last line of a block,
/// and past a leaving line, the lines after it.
fn answering(expr: &d::Expr) -> &d::Expr {
    match &expr.kind {
        ExprKind::Block(body) => answering(&body.result),
        ExprKind::If(_, yes, no) if leaves(no) => answering(yes),
        ExprKind::If(_, yes, no) if leaves(yes) => answering(no),
        _ => expr,
    }
}

/// Whether `expr` never answers where it stands.
fn leaves(expr: &d::Expr) -> bool {
    match &expr.kind {
        ExprKind::Return(_) => true,
        ExprKind::Block(body) => leaves(&body.result),
        _ => false,
    }
}
