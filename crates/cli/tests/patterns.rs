//! Clauses written at random, held to a model of what they mean.
//!
//! Each function takes one or two of `Bool`, `Nat`, `List(Bool)` and a
//! declared `Opt`, in clauses whose patterns are drawn from what each type
//! is taken apart by: numerals and successors, a list's front, end and
//! length, alternatives, and guards on what a clause bound, an `is` test
//! among them. Each clause answers its place. A function is written as
//! clauses, as one `is ( arms )` over its parameters, or, where it ends
//! taking anything, as a chain of `if`s each testing them, `else` the last:
//! each is planned by its own way through pattern compilation. A list's end
//! is matched only by a clause.
//!
//! The model says, for every value of a sample wide enough that each way
//! the patterns part the values holds one, which clause answers it. Where
//! some value is matched by no clause without a guard, checking must refuse
//! the function as not covering every case; where every value is, the
//! function must be accepted and answer each value as the model does. So
//! the coverage check and the decisions pattern compilation makes are each
//! held to the model rather than to each other: planning trusts that a way
//! checking found covered is one no value takes, and a disagreement would
//! be a program that compiles and never answers.

mod support;

use std::collections::HashMap;
use std::fmt::Write as _;

use faun_x86_64_linux::X86_64Linux;
use support::{Package, run_file};

/// How many functions are written, unless `FAUN_PATTERN_CASES` says.
const CASES: usize = 120;

/// How many functions one program holds, to be compiled and run at once.
const BATCH: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ty {
    Bool,
    Nat,
    List,
    Opt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Nat(u32),
    List(Vec<bool>),
    Opt(Option<u32>),
}

#[derive(Clone, Debug)]
enum Pat {
    Wild,
    Bind(String),
    Bool(bool),
    Num(u32),
    Succ(Box<Self>),
    Nil,
    /// `[p, *rest]`, the rest bound where it is named.
    Head(Box<Self>, Option<String>),
    /// `[*_, p]`.
    Last(Box<Self>),
    /// `[p]`.
    One(Box<Self>),
    /// `[p, q]`.
    Two(Box<Self>, Box<Self>),
    /// `[*_, p, q]`.
    LastTwo(Box<Self>, Box<Self>),
    Some(Box<Self>),
    None,
    /// `(p | q)`, the alternatives binding nothing.
    Or(Vec<Self>),
}

#[derive(Clone, Debug)]
enum Guard {
    /// `if x`, of a bound `Bool`.
    Holds(String),
    /// `if n > k`, of a bound `Nat`.
    Above(String, u32),
    /// `if o is Some(m) & m > k`, of a bound `Opt`.
    Holding(String, String, u32),
}

struct Clause {
    patterns: Vec<Pat>,
    guard: Option<Guard>,
}

struct Function {
    name: String,
    parameters: Vec<Ty>,
    clauses: Vec<Clause>,
    form: Form,
}

/// How a function's clauses are written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Form {
    Clauses,
    /// `name(a0, a1) -> (a0, a1) is ( arms )`.
    Arms,
    /// `name(a0, a1) -> if (a0, a1) is (p, q) & guard then 0 else if ... else n`.
    Chain,
}

/// A generator of numbers that says the same each run.
struct Draw(u64);

impl Draw {
    const fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).expect("a small bound"))
            .expect("below a usize")
    }

    /// One of `choices`, each as likely as its weight says.
    fn weighted(&mut self, choices: &[usize]) -> usize {
        let total = choices.iter().sum();
        let mut at = self.below(total);
        for (index, &weight) in choices.iter().enumerate() {
            if at < weight {
                return index;
            }
            at -= weight;
        }
        unreachable!("the draw is below the total")
    }
}

/// What a clause's patterns bind, by name and type, as they are drawn.
struct Binding<'a> {
    draw: &'a mut Draw,
    bound: Vec<(String, Ty)>,
}

impl Binding<'_> {
    fn name(&mut self, ty: Ty) -> String {
        let name = format!("v{}", self.bound.len());
        self.bound.push((name.clone(), ty));
        name
    }

    fn pattern(&mut self, ty: Ty, depth: usize) -> Pat {
        if ty != Ty::List && depth > 0 && self.draw.below(8) == 0 {
            return self.alternatives(ty, depth - 1);
        }
        match ty {
            Ty::Bool => match self.draw.weighted(&[2, 1, 2, 2]) {
                0 => Pat::Wild,
                1 => Pat::Bind(self.name(Ty::Bool)),
                choice => Pat::Bool(choice == 2),
            },
            Ty::Nat => match self.draw.weighted(&[2, 1, 3, usize::from(depth > 0) * 2]) {
                0 => Pat::Wild,
                1 => Pat::Bind(self.name(Ty::Nat)),
                2 => Pat::Num([0, 1, 2, 70][self.draw.below(4)]),
                _ => Pat::Succ(Box::new(self.pattern(Ty::Nat, depth - 1))),
            },
            Ty::List => self.list(),
            Ty::Opt => match self.draw.weighted(&[1, 1, 3, 2]) {
                0 => Pat::Wild,
                1 => Pat::Bind(self.name(Ty::Opt)),
                2 => Pat::Some(Box::new(self.pattern(Ty::Nat, depth))),
                _ => Pat::None,
            },
        }
    }

    fn list(&mut self) -> Pat {
        let element = |binding: &mut Self| Box::new(binding.pattern(Ty::Bool, 0));
        match self.draw.weighted(&[1, 1, 2, 2, 2, 1, 1, 1]) {
            0 => Pat::Wild,
            1 => Pat::Bind(self.name(Ty::List)),
            2 => Pat::Nil,
            3 => {
                let head = element(self);
                let rest = (self.draw.below(2) == 0).then(|| self.name(Ty::List));
                Pat::Head(head, rest)
            }
            4 => Pat::Last(element(self)),
            5 => Pat::One(element(self)),
            6 => Pat::Two(element(self), element(self)),
            _ => Pat::LastTwo(element(self), element(self)),
        }
    }

    /// Two or three patterns of `ty`, each binding nothing, as each
    /// alternative must bind what the others do.
    fn alternatives(&mut self, ty: Ty, depth: usize) -> Pat {
        let bound = std::mem::take(&mut self.bound);
        let count = 2 + self.draw.below(2);
        let each = (0..count)
            .map(|_| unbound(self.pattern(ty, depth)))
            .collect();
        self.bound = bound;
        Pat::Or(each)
    }

    /// A guard on something the clause bound, where it bound something a
    /// guard can ask of.
    fn guard(&mut self) -> Option<Guard> {
        let askable: Vec<(String, Ty)> = self
            .bound
            .iter()
            .filter(|(_, ty)| *ty != Ty::List)
            .cloned()
            .collect();
        if askable.is_empty() {
            return None;
        }
        let (name, ty) = askable[self.draw.below(askable.len())].clone();
        let bound = [0, 1, 3, 70][self.draw.below(4)];
        Some(match ty {
            Ty::Bool => Guard::Holds(name),
            Ty::Nat => Guard::Above(name, bound),
            Ty::Opt => Guard::Holding(name, format!("m{}", self.bound.len()), bound),
            Ty::List => unreachable!("lists are not asked of"),
        })
    }
}

/// `pattern` binding nothing: each name it binds taken anything instead.
fn unbound(pattern: Pat) -> Pat {
    let inner = |inner: Box<Pat>| Box::new(unbound(*inner));
    match pattern {
        Pat::Bind(_) => Pat::Wild,
        Pat::Succ(p) => Pat::Succ(inner(p)),
        Pat::Head(head, _) => Pat::Head(inner(head), None),
        Pat::Last(p) => Pat::Last(inner(p)),
        Pat::One(p) => Pat::One(inner(p)),
        Pat::Two(p, q) => Pat::Two(inner(p), inner(q)),
        Pat::LastTwo(p, q) => Pat::LastTwo(inner(p), inner(q)),
        Pat::Some(p) => Pat::Some(inner(p)),
        Pat::Or(each) => Pat::Or(each.into_iter().map(unbound).collect()),
        other => other,
    }
}

fn function(draw: &mut Draw, name: String) -> Function {
    let parameters: Vec<Ty> = (0..=draw.below(2))
        .map(|_| [Ty::Bool, Ty::Nat, Ty::List, Ty::Opt][draw.below(4)])
        .collect();
    let mut clauses: Vec<Clause> = (0..=draw.below(6))
        .map(|_| clause(draw, &parameters))
        .collect();
    // Half end taking anything, so that half are likely to cover every case.
    let ends_taking_anything = draw.below(2) == 0;
    if ends_taking_anything {
        clauses.push(Clause {
            patterns: vec![Pat::Wild; parameters.len()],
            guard: None,
        });
    }
    let ending = clauses
        .iter()
        .flat_map(|clause| &clause.patterns)
        .any(|pattern| matches!(pattern, Pat::Last(_) | Pat::LastTwo(..)));
    let form = match draw.below(3) {
        _ if ending => Form::Clauses,
        1 => Form::Arms,
        2 if ends_taking_anything => Form::Chain,
        _ => Form::Clauses,
    };
    Function {
        name,
        parameters,
        clauses,
        form,
    }
}

fn clause(draw: &mut Draw, parameters: &[Ty]) -> Clause {
    let mut binding = Binding {
        draw,
        bound: Vec::new(),
    };
    let patterns = parameters
        .iter()
        .map(|&ty| binding.pattern(ty, 2))
        .collect();
    let guard = if binding.draw.below(3) == 0 {
        binding.guard()
    } else {
        None
    };
    Clause { patterns, guard }
}

const fn spelled_type(ty: Ty) -> &'static str {
    match ty {
        Ty::Bool => "Bool",
        Ty::Nat => "Nat",
        Ty::List => "List(Bool)",
        Ty::Opt => "Opt",
    }
}

fn spelled_pattern(pattern: &Pat) -> String {
    let one = |inner: &Pat| spelled_pattern(inner);
    match pattern {
        Pat::Wild => "_".to_owned(),
        Pat::Bind(name) => name.clone(),
        Pat::Bool(value) => if *value { "True" } else { "False" }.to_owned(),
        Pat::Num(number) => number.to_string(),
        Pat::Succ(inner) => format!("Succ({})", one(inner)),
        Pat::Nil => "[]".to_owned(),
        Pat::Head(head, rest) => format!("[{}, *{}]", one(head), rest.as_deref().unwrap_or("_")),
        Pat::Last(last) => format!("[*_, {}]", one(last)),
        Pat::One(only) => format!("[{}]", one(only)),
        Pat::Two(first, second) => format!("[{}, {}]", one(first), one(second)),
        Pat::LastTwo(first, second) => format!("[*_, {}, {}]", one(first), one(second)),
        Pat::Some(inner) => format!("Some({})", one(inner)),
        Pat::None => "None".to_owned(),
        Pat::Or(each) => format!("({})", joined(each.iter().map(spelled_pattern), " | ")),
    }
}

fn joined(parts: impl Iterator<Item = String>, between: &str) -> String {
    parts.collect::<Vec<_>>().join(between)
}

/// Several parts as one: one alone, or a tuple of them.
fn tupled(parts: impl Iterator<Item = String>) -> String {
    let parts: Vec<_> = parts.collect();
    match parts.as_slice() {
        [one] => one.clone(),
        many => format!("({})", many.join(", ")),
    }
}

fn spelled_guard(guard: &Guard) -> String {
    match guard {
        Guard::Holds(name) => name.clone(),
        Guard::Above(name, bound) => format!("{name} > {bound}"),
        Guard::Holding(name, inner, bound) => {
            format!("{name} is Some({inner}) & {inner} > {bound}")
        }
    }
}

/// A clause's guard, written after `lead`, or nothing.
fn guarded(clause: &Clause, lead: &str) -> String {
    clause
        .guard
        .as_ref()
        .map(|guard| format!(" {lead} {}", spelled_guard(guard)))
        .unwrap_or_default()
}

fn spelled_function(function: &Function) -> String {
    let types = function
        .parameters
        .iter()
        .map(|&ty| spelled_type(ty).to_owned());
    let mut written = format!("{} : {} -> Nat\n", function.name, tupled(types));
    let names = || (0..function.parameters.len()).map(|at| format!("a{at}"));
    let head = format!("{}({})", function.name, joined(names(), ", "));
    let subject = tupled(names());
    match function.form {
        Form::Clauses => {
            for (at, clause) in function.clauses.iter().enumerate() {
                let patterns = joined(clause.patterns.iter().map(spelled_pattern), ", ");
                let guard = guarded(clause, "if");
                writeln!(written, "{}({patterns}){guard} -> {at}", function.name)
                    .expect("writing to a string");
            }
        }
        Form::Arms => written.push_str(&arms(function, &head, &subject)),
        Form::Chain => written.push_str(&chain(function, &head, &subject)),
    }
    written
}

/// What a clause tests: its one pattern, or a tuple of them.
fn tested(clause: &Clause) -> String {
    tupled(clause.patterns.iter().map(spelled_pattern))
}

fn arms(function: &Function, head: &str, subject: &str) -> String {
    let mut written = format!("{head} -> {subject} is (\n");
    for (at, clause) in function.clauses.iter().enumerate() {
        let guard = guarded(clause, "if");
        writeln!(written, "  {}{guard} -> {at}", tested(clause)).expect("writing to a string");
    }
    written.push_str(")\n");
    written
}

fn chain(function: &Function, head: &str, subject: &str) -> String {
    let tests = &function.clauses[..function.clauses.len() - 1];
    let mut written = format!("{head} ->");
    for (at, clause) in tests.iter().enumerate() {
        let lead = if at == 0 { "if" } else { "else if" };
        let guard = guarded(clause, "&");
        write!(
            written,
            " {lead} {subject} is {}{guard} then {at}",
            tested(clause)
        )
        .expect("writing to a string");
    }
    let otherwise = if tests.is_empty() { "" } else { " else" };
    writeln!(written, "{otherwise} {}", tests.len()).expect("writing to a string");
    written
}

fn spelled_value(value: &Value) -> String {
    let truth = |value: bool| if value { "True" } else { "False" }.to_owned();
    match value {
        Value::Bool(value) => truth(*value),
        Value::Nat(number) => number.to_string(),
        Value::List(elements) => format!("[{}]", joined(elements.iter().map(|&e| truth(e)), ", ")),
        Value::Opt(None) => "None".to_owned(),
        Value::Opt(Some(number)) => format!("Some({number})"),
    }
}

/// Values of `ty`, one at least in each part the drawn patterns tell apart:
/// the numerals they name and those beside them, two successors deep, and
/// every list as long as a pattern reads into from either end, and one more.
fn sample(ty: Ty) -> Vec<Value> {
    const NATURALS: [u32; 9] = [0, 1, 2, 3, 4, 69, 70, 71, 200];
    match ty {
        Ty::Bool => vec![Value::Bool(false), Value::Bool(true)],
        Ty::Nat => NATURALS.into_iter().map(Value::Nat).collect(),
        Ty::List => (0..=3)
            .flat_map(|length| {
                (0..1_u32 << length).map(move |bits| {
                    Value::List((0..length).map(|at| bits >> at & 1 == 1).collect())
                })
            })
            .collect(),
        Ty::Opt => std::iter::once(Value::Opt(None))
            .chain(NATURALS.into_iter().map(|number| Value::Opt(Some(number))))
            .collect(),
    }
}

fn arguments(parameters: &[Ty]) -> Vec<Vec<Value>> {
    parameters.iter().fold(vec![Vec::new()], |made, &ty| {
        made.iter()
            .flat_map(|before| {
                sample(ty).into_iter().map(move |value| {
                    let mut after = before.clone();
                    after.push(value);
                    after
                })
            })
            .collect()
    })
}

/// Whether `pattern` matches `value`, binding what it names into `bound`.
fn matches(pattern: &Pat, value: &Value, bound: &mut HashMap<String, Value>) -> bool {
    match (pattern, value) {
        (Pat::Wild, _) | (Pat::None, Value::Opt(None)) => true,
        (Pat::Bind(name), _) => {
            bound.insert(name.clone(), value.clone());
            true
        }
        (Pat::Bool(wanted), Value::Bool(found)) => wanted == found,
        (Pat::Num(wanted), Value::Nat(found)) => wanted == found,
        (Pat::Succ(inner), Value::Nat(found)) => {
            *found > 0 && matches(inner, &Value::Nat(found - 1), bound)
        }
        (Pat::Some(inner), Value::Opt(Some(found))) => matches(inner, &Value::Nat(*found), bound),
        (Pat::Or(each), _) => each.iter().any(|pattern| matches(pattern, value, bound)),
        (_, Value::List(elements)) => matches_list(pattern, elements, bound),
        _ => false,
    }
}

fn matches_list(pattern: &Pat, elements: &[bool], bound: &mut HashMap<String, Value>) -> bool {
    let mut element =
        |pattern: &Pat, at: usize| matches(pattern, &Value::Bool(elements[at]), bound);
    let length = elements.len();
    match pattern {
        Pat::Nil => length == 0,
        Pat::Head(head, rest) => {
            if length == 0 {
                return false;
            }
            let matched = element(head, 0);
            if let Some(rest) = rest {
                bound.insert(rest.clone(), Value::List(elements[1..].to_vec()));
            }
            matched
        }
        Pat::Last(last) => length > 0 && element(last, length - 1),
        Pat::One(only) => length == 1 && element(only, 0),
        Pat::Two(first, second) => length == 2 && element(first, 0) && element(second, 1),
        Pat::LastTwo(first, second) => {
            length >= 2 && element(first, length - 2) && element(second, length - 1)
        }
        _ => false,
    }
}

fn holds(guard: &Guard, bound: &HashMap<String, Value>) -> bool {
    match guard {
        Guard::Holds(name) => bound[name] == Value::Bool(true),
        Guard::Above(name, wanted) => matches!(bound[name], Value::Nat(found) if found > *wanted),
        Guard::Holding(name, _, wanted) => {
            matches!(bound[name], Value::Opt(Some(found)) if found > *wanted)
        }
    }
}

/// Whether `pattern` is counted as covering what it matches. A list's end
/// that tests its elements covers nothing whole, as checking reads one:
/// that it is a test is all it says.
fn counted(pattern: &Pat) -> bool {
    let anything = |inner: &Pat| matches!(inner, Pat::Wild | Pat::Bind(_));
    match pattern {
        Pat::Last(last) => anything(last),
        Pat::LastTwo(first, second) => anything(first) && anything(second),
        Pat::Succ(inner) | Pat::Some(inner) | Pat::One(inner) | Pat::Head(inner, _) => {
            counted(inner)
        }
        Pat::Two(first, second) => counted(first) && counted(second),
        Pat::Or(each) => each.iter().all(counted),
        _ => true,
    }
}

/// The clause answering `values`, and whether one with no guard matches
/// them, counted as covering them, which is what covering them is.
fn answer(function: &Function, values: &[Value]) -> (Option<usize>, bool) {
    let mut answered = None;
    let mut covered = false;
    for (at, clause) in function.clauses.iter().enumerate() {
        let mut bound = HashMap::new();
        let matched = clause
            .patterns
            .iter()
            .zip(values)
            .all(|(pattern, value)| matches(pattern, value, &mut bound));
        if !matched {
            continue;
        }
        covered |= clause.guard.is_none() && clause.patterns.iter().all(counted);
        let holding = clause
            .guard
            .as_ref()
            .is_none_or(|guard| holds(guard, &bound));
        if answered.is_none() && holding {
            answered = Some(at);
        }
    }
    (answered, covered)
}

fn program(functions: &[&Function], calls: impl Fn(&Function) -> String) -> String {
    let mut written = "Opt : [Some(Nat), None]\n\n".to_owned();
    for function in functions {
        written.push_str(&spelled_function(function));
        written.push('\n');
    }
    written.push_str("main! : Host -> []\nmain!(host) -> (\n");
    for function in functions {
        let called = calls(function);
        if !called.is_empty() {
            writeln!(written, "  host.println!([{called}].to_str())").expect("writing to a string");
        }
    }
    written.push_str("  host.exit!(0)\n)\n");
    written
}

fn calls(function: &Function) -> String {
    let each = arguments(&function.parameters).into_iter().map(|values| {
        let spelled = joined(values.iter().map(spelled_value), ", ");
        format!("{}({spelled})", function.name)
    });
    joined(each, ", ")
}

/// What checking says of the program at `entry`: a refusal's message, or
/// what the compiler said where it broke rather than refusing.
fn lowered(entry: &std::path::Path) -> Result<(), Lowered> {
    match std::panic::catch_unwind(|| faun::lower_to_barb(entry, &X86_64Linux)) {
        Ok(Ok(_)) => Ok(()),
        Ok(Err(error)) => Err(Lowered::Refused(error.message)),
        Err(panic) => Err(Lowered::Broke(said(&*panic))),
    }
}

enum Lowered {
    Refused(String),
    Broke(String),
}

impl Lowered {
    fn message(&self) -> String {
        match self {
            Self::Refused(message) => message.clone(),
            Self::Broke(message) => format!("the compiler broke: {message}"),
        }
    }
}

fn said(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|said| (*said).to_owned()))
        .unwrap_or_default()
}

/// The numbers a line `[0, 3, 1]` holds.
fn answers(line: &str) -> Vec<usize> {
    line.trim_matches(|c| c == '[' || c == ']')
        .split(", ")
        .filter(|part| !part.is_empty())
        .map(|part| part.parse().expect("a clause's place"))
        .collect()
}

/// Whether `pattern`, or a pattern inside it, is one `wanted` says.
fn holds_one(pattern: &Pat, wanted: &dyn Fn(&Pat) -> bool) -> bool {
    wanted(pattern)
        || match pattern {
            Pat::Succ(p) | Pat::Head(p, _) | Pat::Last(p) | Pat::One(p) | Pat::Some(p) => {
                holds_one(p, wanted)
            }
            Pat::Two(p, q) | Pat::LastTwo(p, q) => holds_one(p, wanted) || holds_one(q, wanted),
            Pat::Or(each) => each.iter().any(|p| holds_one(p, wanted)),
            _ => false,
        }
}

/// Refuse a draw missing any form, alternatives, list ends, the largest
/// numeral or an `is` guard, so a change to the weights cannot quietly stop
/// asking about one.
fn drawn_whole(functions: &[Function]) {
    let clauses = || functions.iter().flat_map(|function| &function.clauses);
    let drawn = |wanted: &dyn Fn(&Pat) -> bool| {
        clauses()
            .flat_map(|clause| &clause.patterns)
            .any(|pattern| holds_one(pattern, wanted))
    };
    for form in [Form::Clauses, Form::Arms, Form::Chain] {
        let found = functions.iter().any(|function| function.form == form);
        assert!(found, "no {form:?} drawn");
    }
    assert!(drawn(&|p| matches!(p, Pat::Or(_))), "no `|` drawn");
    assert!(drawn(&|p| matches!(p, Pat::LastTwo(..))), "no end drawn");
    assert!(drawn(&|p| matches!(p, Pat::Num(70))), "no 70 drawn");
    let asked = clauses().any(|clause| matches!(clause.guard, Some(Guard::Holding(..))));
    assert!(asked, "no `is` guard drawn");
}

/// What is wrong of a function the model says covers not every case: it
/// must be refused as not covering them.
fn refused_as_uncovering(function: &Function, values: &[Value]) -> Option<String> {
    let package = Package::new(
        &format!("patterns-{}", function.name),
        &program(&[function], |_| String::new()),
    );
    let said = match lowered(&package.entry()) {
        Err(Lowered::Refused(message)) if message.contains("does not cover every case") => {
            return None;
        }
        Err(error) => format!("refused as `{}`", error.message()),
        Ok(()) => "accepted".to_owned(),
    };
    Some(format!(
        "{}{said}, where it does not cover {values:?}",
        spelled_function(function)
    ))
}

/// What is wrong of functions the model says each cover every case: each
/// must be accepted and answer every sampled value as the model does.
fn answered_as_modelled(batch: usize, functions: &[&Function]) -> Vec<String> {
    let source = program(functions, calls);
    let package = Package::new(&format!("patterns-batch-{batch}"), &source);
    if let Err(error) = lowered(&package.entry()) {
        // Said of the first refused, each on its own.
        let first = functions.iter().find(|function| {
            let alone = Package::new(
                &format!("patterns-alone-{}", function.name),
                &program(&[function], |_| String::new()),
            );
            lowered(&alone.entry()).is_err()
        });
        let written = first.map_or_else(String::new, |function| spelled_function(function));
        return vec![format!(
            "{written}refused as `{}`, where it covers every case",
            error.message()
        )];
    }
    let Ok((status, written)) = std::panic::catch_unwind(|| run_file(&package.entry(), &[])) else {
        return vec![format!("{source}broke where it ran")];
    };
    assert_eq!(status, 0, "{source}");
    functions
        .iter()
        .zip(written.lines())
        .filter_map(|(function, line)| compared(function, line))
        .collect()
}

/// What is wrong of what `function` answered, as `line` says, for each of
/// its sampled values in turn.
fn compared(function: &Function, line: &str) -> Option<String> {
    let values = arguments(&function.parameters);
    let found = answers(line);
    let meant = values.iter().map(|values| {
        answer(function, values)
            .0
            .expect("a covered value is answered")
    });
    let mismatch = values
        .iter()
        .zip(found.iter().zip(meant))
        .find(|(_, (said, meant))| **said != *meant);
    if let Some((values, (said, meant))) = mismatch {
        return Some(format!(
            "{}answers {values:?} by clause {said}, where clause {meant} matches first",
            spelled_function(function)
        ));
    }
    (found.len() != values.len()).then(|| {
        format!(
            "{}answered {} values of {}",
            spelled_function(function),
            found.len(),
            values.len()
        )
    })
}

#[test]
fn clauses_cover_and_answer_as_their_patterns_say() {
    let cases = std::env::var("FAUN_PATTERN_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(CASES);
    let mut draw = Draw(0x9e37_79b9_7f4a_7c15);
    let functions: Vec<Function> = (0..cases)
        .map(|at| function(&mut draw, format!("f{at}")))
        .collect();
    drawn_whole(&functions);
    let mut wrong = Vec::new();
    let mut covering = Vec::new();
    for function in &functions {
        let uncovered = arguments(&function.parameters)
            .into_iter()
            .find(|values| !answer(function, values).1);
        match uncovered {
            None => covering.push(function),
            Some(values) => wrong.extend(refused_as_uncovering(function, &values)),
        }
    }
    for (batch, functions) in covering.chunks(BATCH).enumerate() {
        wrong.extend(answered_as_modelled(batch, functions));
    }
    assert!(
        wrong.is_empty(),
        "{} of {cases} functions disagree with the model:\n\n{}",
        wrong.len(),
        wrong.iter().take(8).cloned().collect::<Vec<_>>().join("\n")
    );
}
