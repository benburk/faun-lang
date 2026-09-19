//! A small surface for writing barb programs as text.
//!
//! Nothing is blessed: there are inductive types and there are rewrites, and
//! a number is whatever a program builds out of its own constructors. Types
//! are inferred, since every one of them is a name a declaration already
//! gave, so there is nothing to infer but which.
//!
//! A clause matches as many arguments as it likes, with patterns one
//! constructor deep. Clauses are tried in the order they are written, and
//! what they compile to is a match per column any of them tests: rows that
//! could match the constructor go on to the next column, and a row nothing
//! reaches is refused by name.
//!
//! ```text
//! type Nat Zero Succ(Nat)
//!
//! add(Zero b) -> b
//! add(Succ(a) b) -> Succ(add(a b))
//!
//! main() -> add(Succ(Succ(Zero)) Succ(Succ(Zero)))
//! ```

use std::collections::HashMap;
use std::collections::HashSet;

use crate::platform::Routines;

use crate::barb::{Atom, CtorId, FnId, Program, TypeId};

/// What a clause matches in one argument: a name, or a constructor and the
/// names its fields take.
#[derive(Clone, Debug)]
enum Pattern {
    Bind(String),
    Ctor(String, Vec<String>),
}

/// A name applied to arguments, of which there may be none.
#[derive(Clone, Debug)]
struct Term(String, Vec<Self>);

#[derive(Clone, Debug)]
struct Clause {
    patterns: Vec<Pattern>,
    /// What the clause works out on the way, each bound to a name. A result
    /// that is not wanted is bound to one that is not read.
    steps: Vec<(String, Term)>,
    /// What the clause answers.
    body: Term,
}

/// A type as written: its name, then each constructor and its field types.
struct Declared {
    name: String,
    ctors: Vec<(String, Vec<String>)>,
}

#[derive(Default)]
struct Source {
    types: Vec<Declared>,
    /// The functions in the order they were first written.
    order: Vec<String>,
    clauses: HashMap<String, Vec<Clause>>,
}

/// Read a program.
///
/// # Errors
///
/// Names what it could not read, or what it read and cannot represent.
pub fn parse(text: &str, routines: &Routines) -> Result<Program, String> {
    let mut words = Words::new(text);
    let mut source = Source::default();

    while let Some(word) = words.peek() {
        if word == "type" {
            words.take();
            source.types.push(read_type(&mut words)?);
            continue;
        }
        let name = words.word()?;
        let patterns = read_patterns(&mut words)?;
        words.expect("->")?;
        // Everything up to the last term is bound to a name; the last is what
        // the clause answers. A step is what is followed by an equals, which
        // is what tells a body from the clause after it.
        let mut steps = Vec::new();
        while words.at(1) == Some("=") {
            let held = words.word()?;
            words.expect("=")?;
            steps.push((held, read_term(&mut words)?));
        }
        let body = read_term(&mut words)?;
        if !source.clauses.contains_key(&name) {
            source.order.push(name.clone());
        }
        let clause = Clause {
            patterns,
            steps,
            body,
        };
        source.clauses.entry(name).or_default().push(clause);
    }
    build(&source, routines)
}

/// A type and its constructors, which run until the next declaration: there
/// is nothing between them to say where one ends, so what ends them is a
/// `type` or a clause.
fn read_type(words: &mut Words) -> Result<Declared, String> {
    let name = words.word()?;
    let mut ctors = Vec::new();
    while words.peek().is_some_and(|word| word != "type") && !words.starts_clause() {
        let ctor = words.word()?;
        let fields = if words.peek() == Some("(") {
            read_names(words)?
        } else {
            Vec::new()
        };
        ctors.push((ctor, fields));
    }
    Ok(Declared { name, ctors })
}

/// A parenthesised run of bare words.
fn read_names(words: &mut Words) -> Result<Vec<String>, String> {
    words.expect("(")?;
    let mut names = Vec::new();
    while words.peek() != Some(")") {
        names.push(words.word()?);
    }
    words.expect(")")?;
    Ok(names)
}

fn read_patterns(words: &mut Words) -> Result<Vec<Pattern>, String> {
    words.expect("(")?;
    let mut patterns = Vec::new();
    while words.peek() != Some(")") {
        let head = words.word()?;
        patterns.push(if words.peek() == Some("(") {
            Pattern::Ctor(head, read_names(words)?)
        } else {
            Pattern::Bind(head)
        });
    }
    words.expect(")")?;
    Ok(patterns)
}

/// How deep one term may hold another.
///
/// A term is a tree and everything that reads one walks it the way it was
/// written, so a term nested deeper than the machine has stack for would
/// take the compiler down rather than be refused. The count is kept here,
/// where a term is built, since refusing it later means a tree that deep
/// already exists -- and letting go of one is itself a walk.
///
/// Well past anything written by hand. A number is a chain of constructors
/// until there is a shorter way to say one, so this is not as far off as it
/// looks.
const DEEPEST: usize = 1024;

fn read_term(words: &mut Words) -> Result<Term, String> {
    read_term_at(words, 0)
}

fn read_term_at(words: &mut Words, depth: usize) -> Result<Term, String> {
    let head = words.word()?;
    if words.peek() != Some("(") {
        return Ok(Term(head, Vec::new()));
    }
    if depth == DEEPEST {
        return Err(format!(
            "`{head}` is nested more than {DEEPEST} deep, which is deeper than this reads"
        ));
    }
    words.take();
    let mut args = Vec::new();
    while words.peek() != Some(")") {
        args.push(read_term_at(words, depth + 1)?);
    }
    words.expect(")")?;
    Ok(Term(head, args))
}

const PUNCTUATION: [&str; 7] = ["(", ")", ",", "=", "|", ":", "->"];

/// Words and punctuation, in order.
struct Words {
    words: Vec<String>,
    at: usize,
}

impl Words {
    fn new(text: &str) -> Self {
        let mut words = Vec::new();
        let mut held = String::new();
        let mut rest = text.chars().peekable();
        while let Some(character) = rest.next() {
            if character == '#' {
                flush(&mut held, &mut words);
                while rest.peek().is_some_and(|held| *held != '\n') {
                    rest.next();
                }
            } else if character == '-' && rest.peek() == Some(&'>') {
                rest.next();
                flush(&mut held, &mut words);
                words.push("->".to_owned());
            } else if "(),=|:".contains(character) {
                flush(&mut held, &mut words);
                words.push(character.to_string());
            } else if character.is_whitespace() {
                flush(&mut held, &mut words);
            } else {
                held.push(character);
            }
        }
        flush(&mut held, &mut words);
        Self { words, at: 0 }
    }

    fn peek(&self) -> Option<&str> {
        self.at(0)
    }

    /// The word `ahead` past the next one.
    fn at(&self, ahead: usize) -> Option<&str> {
        self.words.get(self.at + ahead).map(String::as_str)
    }

    fn take(&mut self) -> Option<String> {
        let word = self.words.get(self.at).cloned();
        self.at += 1;
        word
    }

    /// A name. Punctuation is never one, so a stray comma is refused rather
    /// than bound as though it were a variable.
    fn word(&mut self) -> Result<String, String> {
        match self.take() {
            Some(word) if !PUNCTUATION.contains(&word.as_str()) => Ok(word),
            Some(word) => Err(format!("expected a name, found `{word}`")),
            None => Err("the program ends early".to_owned()),
        }
    }

    /// Whether what comes next is a clause rather than a constructor: a name,
    /// a parenthesised run, and then an arrow. A constructor's own run is
    /// followed by anything else.
    fn starts_clause(&self) -> bool {
        if self.at(1) != Some("(") {
            return false;
        }
        let mut at = 1;
        let mut depth = 0usize;
        loop {
            match self.at(at) {
                Some("(") => depth += 1,
                Some(")") => {
                    depth -= 1;
                    if depth == 0 {
                        return self.at(at + 1) == Some("->");
                    }
                }
                Some(_) => {}
                None => return false,
            }
            at += 1;
        }
    }

    fn expect(&mut self, want: &str) -> Result<(), String> {
        match self.take() {
            Some(word) if word == want => Ok(()),
            other => Err(format!("expected `{want}`, found {other:?}")),
        }
    }
}

fn flush(held: &mut String, words: &mut Vec<String>) {
    if !held.is_empty() {
        words.push(std::mem::take(held));
    }
}

/// Turn what was read into a program.
fn build(source: &Source, routines: &Routines) -> Result<Program, String> {
    let mut program = Program::default();
    declare_builtin(&mut program, source)?;
    declare_types(&mut program, source)?;
    let ctors = catalogue(&program);
    // A bare name in a pattern is a constructor if one is declared with that
    // name, and a binder otherwise. Nothing in the text says which, so this
    // is the first point that can tell -- and everything after reads the
    // resolved clauses, inference included.
    let clauses: HashMap<&str, Vec<Clause>> = source
        .clauses
        .iter()
        .map(|(name, held)| {
            (
                name.as_str(),
                held.iter().map(|c| resolve(c, &ctors)).collect(),
            )
        })
        .collect();

    let arity = arities(source, &clauses, routines)?;
    validate(source, &clauses, &arity)?;
    let told = infer(source, routines, &clauses, &program, &ctors, &arity)?;
    let mut functions: HashMap<&str, FnId> = HashMap::new();
    for (called, routine) in routines.offered() {
        let Some((params, result)) = told.get(called) else {
            continue;
        };
        // The `!` says a program may observe this one working, which is a
        // rule about the language rather than about the routine, so the
        // declaration goes without it -- and says which routine answers for
        // it rather than leaving the tier below to read the name twice.
        let held = called.strip_suffix('!').unwrap_or(called);
        let id = program.declare(held, params, *result);
        program.answered_by(id, &routine.name);
        if let Some(class) = routine.answers() {
            program.bound(id, host_bound(class));
        }
        functions.insert(called, id);
    }
    for name in &source.order {
        let (params, result) = &told[name];
        functions.insert(name, program.declare(name, params, *result));
    }

    let main = starts(&program, &functions, &told)?;
    program.set_entry(main);
    define(&mut program, source, &clauses, &told, &functions)
}

const fn host_bound(class: crate::ir::Class) -> crate::barb::Bounds {
    let high = match class {
        crate::ir::Class::Fixed { bits } if bits < 64 => Some((1u64 << bits) - 1),
        crate::ir::Class::Word | crate::ir::Class::Fixed { bits: 64 } => Some(u64::MAX),
        _ => None,
    };
    crate::barb::Bounds { low: 0, high }
}

/// Where a program starts, since nothing in the text says so.
///
/// It is effectful because a program that does nothing observable does
/// nothing, and it leaves through an effect rather than answering one.
///
/// A program is what it did, so the status it leaves with is something it
/// says rather than something falling out of how it was called. There is
/// one way a program ends and so one place to look for it. And `Never` is
/// what says nothing comes after the last thing a program does, in the
/// types rather than by agreement.
///
/// Requiring it requires a target to answer for a way to stop, which every
/// machine has: one with no kernel and no loader still ends by running out
/// of program. So this asks for nothing a machine cannot do.
///
/// Nothing below this tier asks for it. Barb keeps an operation because
/// something reads what it answered, whatever type an entry has, so this is
/// a rule about the language and is kept because it is a good one.
fn starts(
    program: &Program,
    functions: &HashMap<&str, FnId>,
    told: &HashMap<String, Inferred>,
) -> Result<FnId, String> {
    let main = functions
        .get("main!")
        .ok_or_else(|| "no `main!` to start at".to_owned())?;
    let (_, answers) = &told["main!"];
    if *answers != NEVER {
        let held = program.name(program.type_(*answers).name);
        return Err(format!(
            "a program leaves through an effect, and `main!` answers `{held}`"
        ));
    }
    Ok(*main)
}

/// Compile every function's clauses into its body.
fn define(
    program: &mut Program,
    source: &Source,
    clauses: &HashMap<&str, Vec<Clause>>,
    told: &HashMap<String, Inferred>,
    functions: &HashMap<&str, FnId>,
) -> Result<Program, String> {
    let ctors = catalogue(program);
    let lowering = Lowering {
        ctors: &ctors,
        functions,
    };
    for name in &source.order {
        let held = &clauses[name.as_str()];
        let (params, _) = &told[name];
        lowering.define(program, functions[name.as_str()], held, params)?;
    }
    Ok(std::mem::take(program))
}

/// The authority a program is handed, what an effect answers when it answers
/// nothing, and what one answers when it does not answer. Nothing can build a
/// `Host`, because its constructor is not among the names a term may use, so
/// the only way to hold one is to have been handed it. Nothing can build a
/// `Never` either, and for a stronger reason: it has no constructors at all.
fn declare_builtin(program: &mut Program, source: &Source) -> Result<(), String> {
    for name in BUILTIN {
        if source.types.iter().any(|held| held.name == name) {
            return Err(format!("`{name}` is the compiler's, not a program's"));
        }
        let id = program.declare_type(name);
        // A type with no constructors has no values, which is what says that
        // the terms answering it never answer.
        let ctors: &[(&str, &[TypeId])] = if id == NEVER { &[] } else { &[(name, &[])] };
        program.define_type(id, ctors);
    }
    Ok(())
}

/// Every type the program declares, then the constructors of each, so that
/// a field may name a type declared later.
fn declare_types(program: &mut Program, source: &Source) -> Result<(), String> {
    let mut types: HashMap<&str, TypeId> = HashMap::new();
    for held in &source.types {
        types.insert(&held.name, program.declare_type(&held.name));
    }
    for Declared { name, ctors } in &source.types {
        let held: Vec<(&str, Vec<TypeId>)> = ctors
            .iter()
            .map(|(ctor, fields)| {
                let fields = fields
                    .iter()
                    .map(|field| look(&types, field, "type"))
                    .collect::<Result<_, _>>()?;
                Ok((ctor.as_str(), fields))
            })
            .collect::<Result<_, String>>()?;
        let held: Vec<(&str, &[TypeId])> = held
            .iter()
            .map(|(ctor, fields)| (*ctor, fields.as_slice()))
            .collect();
        program.define_type(types[name.as_str()], &held);
    }
    Ok(())
}

/// How many arguments each name takes, which every clause of one has to
/// agree on. An effect takes the authority and what it was blessed with.
fn arities<'a>(
    source: &'a Source,
    clauses: &HashMap<&str, Vec<Clause>>,
    routines: &'a Routines,
) -> Result<HashMap<&'a str, usize>, String> {
    let mut arity = HashMap::new();
    for name in &source.order {
        let held = &clauses[name.as_str()];
        let width = held[0].patterns.len();
        if held.iter().any(|clause| clause.patterns.len() != width) {
            return Err(format!("`{name}` takes a different number each clause"));
        }
        arity.insert(name.as_str(), width);
    }
    for (called, routine) in routines.offered() {
        arity.insert(called, routine.takes.len() + 1);
    }
    Ok(arity)
}

/// What the tiers below are entitled to assume of a program. Everything
/// else here answers what a program says; this answers whether it says
/// anything at all, and it runs before anything reads it as though it did.
fn validate(
    source: &Source,
    clauses: &HashMap<&str, Vec<Clause>>,
    arity: &HashMap<&str, usize>,
) -> Result<(), String> {
    colour(source)?;
    standing(source)?;
    one_name_per_thing(source)?;
    calls_are_saturated(source, clauses, arity)?;
    // The entry is handed the authority and nothing else: there is nobody
    // to hand it anything more.
    if arity.get("main!").is_some_and(|takes| *takes != 1) {
        return Err("`main!` is handed the authority and nothing else".to_owned());
    }
    Ok(())
}

/// A constructor is named once, and nothing else takes its name. A term
/// reads a name as a constructor before it reads it as anything, so a
/// second one is not a second meaning but the loss of the first.
fn one_name_per_thing(source: &Source) -> Result<(), String> {
    let mut held: HashSet<&str> = BUILTIN.into_iter().collect();
    for declared in &source.types {
        for (ctor, _) in &declared.ctors {
            if !held.insert(ctor.as_str()) {
                return Err(format!("`{ctor}` is declared twice"));
            }
        }
    }
    for name in &source.order {
        if held.contains(name.as_str()) {
            return Err(format!(
                "`{name}` is a constructor and a name; one or the other"
            ));
        }
    }
    Ok(())
}

/// Every call gives a name what it takes. Nothing downstream checks this:
/// the slots a call unifies with are the name's own, so an argument too
/// many lands on the name's result and the call answers whatever was
/// allocated after it.
fn calls_are_saturated(
    source: &Source,
    clauses: &HashMap<&str, Vec<Clause>>,
    arity: &HashMap<&str, usize>,
) -> Result<(), String> {
    fn within(
        term: &Term,
        bound: &HashSet<&str>,
        arity: &HashMap<&str, usize>,
    ) -> Result<(), String> {
        let Term(name, args) = term;
        // A name a clause binds is a value, and shadows the one declared.
        if !bound.contains(name.as_str())
            && let Some(&takes) = arity.get(name.as_str())
            && args.len() != takes
        {
            let each = if takes == 1 { "argument" } else { "arguments" };
            return Err(format!("`{name}` takes {takes} {each}, not {}", args.len()));
        }
        args.iter()
            .try_for_each(|argument| within(argument, bound, arity))
    }

    for name in &source.order {
        for clause in &clauses[name.as_str()] {
            let mut bound: HashSet<&str> = HashSet::new();
            for pattern in &clause.patterns {
                match pattern {
                    Pattern::Bind(held) => {
                        bound.insert(held.as_str());
                    }
                    Pattern::Ctor(_, fields) => {
                        bound.extend(fields.iter().map(String::as_str));
                    }
                }
            }
            for (held, step) in &clause.steps {
                within(step, &bound, arity)?;
                bound.insert(held.as_str());
            }
            within(&clause.body, &bound, arity)?;
        }
    }
    Ok(())
}

/// A name ending in `!` may perform observable work, and a name that does
/// not may not call one that does. One colour, stated where it is written.
fn colour(source: &Source) -> Result<(), String> {
    fn calls(term: &Term, each: &mut impl FnMut(&str)) {
        each(&term.0);
        for arg in &term.1 {
            calls(arg, each);
        }
    }
    for name in &source.order {
        if name.ends_with('!') {
            continue;
        }
        for clause in &source.clauses[name] {
            let mut found = None;
            for term in clause
                .steps
                .iter()
                .map(|(_, term)| term)
                .chain([&clause.body])
            {
                calls(term, &mut |called| {
                    if called.ends_with('!') {
                        found.get_or_insert_with(|| called.to_owned());
                    }
                });
            }
            if let Some(called) = found {
                return Err(format!("`{name}` is pure and calls `{called}`"));
            }
        }
    }
    Ok(())
}

/// An effect stands on its own: as the whole of a step, or as what a clause
/// answers, and never as an argument to something else.
///
/// What a term hands over is worked out before the term is, and where two
/// of them are observable, which goes first is a question the writing does
/// not answer. Binding each to a name answers it, in the order the names
/// are written. Nothing below the language knows this rule, and nothing
/// below it has to: what reaches the tier below is already in an order.
fn standing(source: &Source) -> Result<(), String> {
    fn within(term: &Term, name: &str) -> Result<(), String> {
        for held in &term.1 {
            if held.0.ends_with('!') {
                return Err(format!(
                    "`{name}` hands over `{}`, and an effect stands on its own",
                    held.0
                ));
            }
            within(held, name)?;
        }
        Ok(())
    }
    for name in &source.order {
        for clause in &source.clauses[name] {
            for term in clause
                .steps
                .iter()
                .map(|(_, term)| term)
                .chain([&clause.body])
            {
                within(term, name)?;
            }
        }
    }
    Ok(())
}

/// Whether anything in the program calls a name.
fn calls(source: &Source, name: &str) -> bool {
    fn within(term: &Term, name: &str) -> bool {
        term.0 == name || term.1.iter().any(|held| within(held, name))
    }
    source.clauses.values().flatten().any(|clause| {
        clause
            .steps
            .iter()
            .map(|(_, term)| term)
            .chain([&clause.body])
            .any(|term| within(term, name))
    })
}

/// A pattern naming a declared constructor is that constructor, not a name
/// the clause binds.
fn resolve(clause: &Clause, ctors: &HashMap<String, CtorId>) -> Clause {
    let patterns = clause
        .patterns
        .iter()
        .map(|pattern| match pattern {
            Pattern::Bind(name) if ctors.contains_key(name) => {
                Pattern::Ctor(name.clone(), Vec::new())
            }
            held => held.clone(),
        })
        .collect();
    Clause {
        patterns,
        steps: clause.steps.clone(),
        body: clause.body.clone(),
    }
}

/// The types the compiler declares, in the order they are declared in: the
/// authority a program is handed, what an effect answers when it answers
/// nothing, and what a term answers when it does not come back. None of them
/// carries anything, so all are erased, and `Host`'s constructor is left out
/// of the names a term may use so that no program can make one for itself.
const BUILTIN: [&str; 3] = ["Host", "Unit", "Never"];

/// Two of them are named here as well as declared above, since the rules
/// below are written in terms of them. The order `BUILTIN` is declared in is
/// what makes these the indices they are.
const HOST: TypeId = TypeId(0);
const UNIT: TypeId = TypeId(1);
const NEVER: TypeId = TypeId(2);

/// Every constructor a term may name.
fn catalogue(program: &Program) -> HashMap<String, CtorId> {
    let mut ctors = HashMap::new();
    // From past the authority, which is the one a program may not build.
    for at in 1..program.types().len() {
        let id = TypeId::at(at);
        for tag in 0..u32::try_from(program.type_(id).ctors.len()).expect("a sane count") {
            let ctor = program.ctor_at(id, tag);
            ctors.insert(program.name(program.ctor(ctor).name).to_owned(), ctor);
        }
    }
    ctors
}

fn look<T: Copy>(table: &HashMap<&str, T>, name: &str, what: &str) -> Result<T, String> {
    table
        .get(name)
        .copied()
        .ok_or_else(|| format!("no {what} named `{name}`"))
}

struct Lowering<'a> {
    ctors: &'a HashMap<String, CtorId>,
    functions: &'a HashMap<&'a str, FnId>,
}

/// The names a clause has bound, and what each stands for.
type Scope = Vec<(String, Atom)>;

/// One clause on its way through the matrix: what it still matches on, and
/// what it has bound so far. Two clauses may name one constructor's fields
/// differently, so the bindings belong to the row rather than to the match
/// that made them.
#[derive(Clone)]
struct Row<'a> {
    clause: &'a Clause,
    at: usize,
    /// Its patterns, with a column that has been matched on left out: every
    /// row in a run of them has the same columns settled, since they were
    /// settled by the same match.
    patterns: Vec<Option<Pattern>>,
    scope: Scope,
}

/// The leftmost column any row still matches on, and nothing where every
/// row takes what is left as a name.
fn column(rows: &[Row]) -> Option<usize> {
    let width = rows.first()?.patterns.len();
    (0..width).find(|at| {
        rows.iter()
            .any(|row| matches!(row.patterns[*at], Some(Pattern::Ctor(..))))
    })
}

/// What the constructors chosen to reach here were, as a program reads it.
fn along(chosen: &[String]) -> String {
    match chosen {
        [] => String::new(),
        [held] => format!("`{held}`"),
        [rest @ .., last] => format!("{} and `{last}`", along(rest)),
    }
}

impl Lowering<'_> {
    /// Compile one function's clauses into its body. A builder answers an
    /// atom rather than a result, so a refusal is carried out around it.
    fn define(
        &self,
        program: &mut Program,
        id: FnId,
        clauses: &[Clause],
        types: &[TypeId],
    ) -> Result<(), String> {
        let mut failed = None;
        let mut reached = vec![false; clauses.len()];
        program.define(id, |b, args| {
            let rows: Vec<Row> = clauses
                .iter()
                .enumerate()
                .map(|(at, clause)| Row {
                    clause,
                    at,
                    patterns: clause.patterns.iter().cloned().map(Some).collect(),
                    scope: Scope::new(),
                })
                .collect();
            match self.rows(b, &rows, args, types, &[], &mut reached) {
                Ok(atom) => atom,
                Err(error) => {
                    failed = Some(error);
                    args.first().copied().unwrap_or(Atom(crate::barb::Local(0)))
                }
            }
        });
        if let Some(error) = failed {
            return Err(error);
        }
        if reached.iter().any(|reached| !reached) {
            let name = program.name(program.function(id).name).to_owned();
            return Err(format!("`{name}` has a clause nothing reaches"));
        }
        Ok(())
    }

    /// The clauses still in play, as a match on a column one of them tests.
    /// Each arm keeps the rows that could match that constructor -- the ones
    /// naming it, and the ones taking the argument as a name -- and asks the
    /// same question of what is left.
    ///
    /// Where no row tests anything, the first of them is what matches: they
    /// are tried in the order they were written, so an earlier row that
    /// reaches here answers here.
    fn rows(
        &self,
        b: &mut crate::barb::Builder,
        rows: &[Row],
        args: &[Atom],
        types: &[TypeId],
        chosen: &[String],
        reached: &mut [bool],
    ) -> Result<Atom, String> {
        let Some(at) = column(rows) else {
            let row = rows.first().expect("a row, since an empty run is refused");
            reached[row.at] = true;
            let mut scope = row.scope.clone();
            for (pattern, arg) in row.patterns.iter().zip(args) {
                if let Some(Pattern::Bind(name)) = pattern {
                    scope.push((name.clone(), *arg));
                }
            }
            return self.body(b, row.clause, scope);
        };
        let scrutinee = *args
            .get(at)
            .ok_or_else(|| format!("no argument {at} to match on"))?;
        let owner = types[at];

        let mut failed = None;
        let answer = b.match_(scrutinee, owner, |b, ctor, fields| {
            let held = self
                .narrow(rows, (at, scrutinee), (ctor, fields), chosen)
                .and_then(|(rows, chosen)| self.rows(b, &rows, args, types, &chosen, reached));
            match held {
                Ok(atom) => atom,
                Err(error) => {
                    failed.get_or_insert(error);
                    scrutinee
                }
            }
        });
        failed.map_or(Ok(answer), Err)
    }

    /// The rows that could match `ctor` in column `at`, each with what that
    /// constructor revealed bound to the names that row gave it.
    fn narrow<'a>(
        &self,
        rows: &[Row<'a>],
        (at, scrutinee): (usize, Atom),
        (ctor, fields): (CtorId, &[Atom]),
        chosen: &[String],
    ) -> Result<(Vec<Row<'a>>, Vec<String>), String> {
        let wanted = self
            .ctors
            .iter()
            .find(|(_, held)| **held == ctor)
            .map(|(name, _)| name.clone())
            .expect("a constructor of the program");

        let mut held = Vec::new();
        for row in rows {
            let mut row = row.clone();
            match row.patterns[at].take() {
                Some(Pattern::Bind(name)) => row.scope.push((name, scrutinee)),
                Some(Pattern::Ctor(name, names)) if name == wanted => {
                    if names.len() != fields.len() {
                        return Err(format!("`{wanted}` takes {} fields", fields.len()));
                    }
                    for (name, field) in names.into_iter().zip(fields) {
                        row.scope.push((name, *field));
                    }
                }
                // Another constructor, so this row is not this arm's.
                Some(Pattern::Ctor(..)) => continue,
                None => {}
            }
            held.push(row);
        }

        let mut chosen = chosen.to_vec();
        chosen.push(wanted);
        if held.is_empty() {
            return Err(format!("no clause covers {}", along(&chosen)));
        }
        Ok((held, chosen))
    }

    /// A clause's steps in order, each bound where it named it, then what it
    /// answers. Order is the order they were written: the tier below keeps a
    /// body's bindings in the order they arrive, so an effect that must
    /// happen first is written first.
    fn body(
        &self,
        b: &mut crate::barb::Builder,
        clause: &Clause,
        scope: Scope,
    ) -> Result<Atom, String> {
        let mut scope = scope;
        for (held, step) in &clause.steps {
            let atom = self.term(b, step, &scope)?;
            scope.push((held.clone(), atom));
        }
        self.term(b, &clause.body, &scope)
    }

    fn term(
        &self,
        b: &mut crate::barb::Builder,
        term: &Term,
        scope: &Scope,
    ) -> Result<Atom, String> {
        let Term(name, args) = term;
        if args.is_empty()
            && let Some((_, atom)) = scope.iter().rev().find(|(held, _)| held == name)
        {
            return Ok(*atom);
        }
        let args: Vec<Atom> = args
            .iter()
            .map(|arg| self.term(b, arg, scope))
            .collect::<Result<_, _>>()?;
        if let Some(ctor) = self.ctors.get(name) {
            return Ok(b.con(*ctor, &args));
        }
        let id = look(self.functions, name, "function")?;
        Ok(b.call(id, &args))
    }
}

/// What a function takes and answers, worked out rather than declared.
type Inferred = (Vec<TypeId>, TypeId);

/// Slots that must hold the same type, and the type they hold once anything
/// pins it. Every type here is a name some declaration already gave, so
/// there is nothing to infer but which one.
struct Unify {
    parent: Vec<usize>,
    known: Vec<Option<TypeId>>,
}

impl Unify {
    fn fresh(&mut self) -> usize {
        self.parent.push(self.parent.len());
        self.known.push(None);
        self.parent.len() - 1
    }

    fn find(&mut self, slot: usize) -> usize {
        let mut at = slot;
        while self.parent[at] != at {
            self.parent[at] = self.parent[self.parent[at]];
            at = self.parent[at];
        }
        at
    }

    fn union(&mut self, left: usize, right: usize) -> Result<(), String> {
        let (left, right) = (self.find(left), self.find(right));
        if left == right {
            return Ok(());
        }
        let held = match (self.known[left], self.known[right]) {
            (Some(one), Some(other)) => Some(agree(one, other)?),
            (held, other) => held.or(other),
        };
        self.parent[right] = left;
        self.known[left] = held;
        Ok(())
    }

    fn pin(&mut self, slot: usize, id: TypeId) -> Result<(), String> {
        let slot = self.find(slot);
        self.known[slot] = Some(match self.known[slot] {
            Some(held) => agree(held, id)?,
            None => id,
        });
        Ok(())
    }

    fn get(&mut self, slot: usize) -> Option<TypeId> {
        let slot = self.find(slot);
        self.known[slot]
    }
}

/// The type two slots hold once they are the same slot. `Never` has no
/// values, so a term answering it answers nothing that could disagree with
/// anything: it takes the type of whatever it was used beside. That is the
/// one place two types meet and both are kept.
fn agree(one: TypeId, other: TypeId) -> Result<TypeId, String> {
    match (one, other) {
        _ if one == other => Ok(one),
        (NEVER, held) | (held, NEVER) => Ok(held),
        _ => Err("a value is used at two types".to_owned()),
    }
}

/// Work out what every function takes and answers.
fn infer(
    source: &Source,
    routines: &Routines,
    clauses: &HashMap<&str, Vec<Clause>>,
    program: &Program,
    ctors: &HashMap<String, CtorId>,
    arity: &HashMap<&str, usize>,
) -> Result<HashMap<String, Inferred>, String> {
    let mut unify = Unify {
        parent: Vec::new(),
        known: Vec::new(),
    };
    // Each function takes a run of slots: one per argument, then its result.
    let base = slots(source, routines, arity, &mut unify)?;
    let leaving = diverging(source, clauses, routines);

    let reading = Reading {
        program,
        ctors,
        base: &base,
        arity,
        leaving: &leaving,
    };
    for name in &source.order {
        for clause in &clauses[name.as_str()] {
            let mut scope = reading.bound(clause, base[name.as_str()], &mut unify)?;
            for (held, step) in &clause.steps {
                let slot = reading.term(step, &scope, &mut unify)?;
                scope.insert(held.as_str(), slot);
            }
            let answer = reading.term(&clause.body, &scope, &mut unify)?;
            let result = base[name.as_str()] + arity[name.as_str()];
            unify.union(answer, result)?;
        }
    }

    let mut told = HashMap::new();
    for name in source.order.iter().map(String::as_str) {
        told.insert(name.to_owned(), reading.settled(&mut unify, name)?);
    }
    // An effect no program calls settles nothing, and needs to: there is
    // nothing to declare and nothing to answer for.
    for (called, _) in routines.offered() {
        match reading.settled(&mut unify, called) {
            Ok(held) => {
                told.insert(called.to_owned(), held);
            }
            // One nothing calls settles nothing, and needs to: there is
            // nothing to declare and nothing to answer for. One something
            // calls and that still settles nothing is a program that never
            // said which type it was working over.
            Err(held) if calls(source, called) => return Err(held),
            Err(_) => {}
        }
    }
    Ok(told)
}

/// A run of slots per function: one per argument, then its result. A
/// platform states what it takes, so its slots start out settled.
fn slots<'a>(
    source: &'a Source,
    routines: &'a Routines,
    arity: &HashMap<&str, usize>,
    unify: &mut Unify,
) -> Result<HashMap<&'a str, usize>, String> {
    let mut base = HashMap::new();
    for name in &source.order {
        let at = unify.parent.len();
        for _ in 0..=arity[name.as_str()] {
            unify.fresh();
        }
        base.insert(name.as_str(), at);
    }
    // An effect is handed the authority; what either takes after that is
    // whatever it is given, which the argument settles, and what it answers
    // is either nothing ever or one of those arguments.
    for (called, routine) in routines.offered() {
        let at = unify.parent.len();
        // Every one of them is handed the authority, since every one of them
        // is something a program may be watched doing.
        let held = unify.fresh();
        unify.pin(held, HOST)?;
        for _ in 0..routine.takes.len() {
            unify.fresh();
        }
        let answer = unify.fresh();
        if !routine.comes_back() {
            unify.pin(answer, NEVER)?;
        } else if routine.answers().is_none() {
            // One that comes back and works nothing out says nothing by
            // answering, which is what `Unit` is for.
            unify.pin(answer, UNIT)?;
        }
        // And one that answers a value says nothing here about which type
        // holds it, there being no type below this tier. What it answers
        // is whatever it stands beside, the same as anything else.
        base.insert(called, at);
    }
    Ok(base)
}

/// The names a call to which does not come back: the effects, and every
/// name whose clauses all leave through one. Inference needs this before it
/// decides anything, since a use of such a name is free to stand at whatever
/// type its neighbours do -- and freedom per use is not something the slots
/// can work out for themselves, because they are shared between uses.
///
/// A clause leaves if any of its steps does or if its body does, and a term
/// leaves if the name at its head does or if one of its arguments does.
/// Nothing here recognises a loop that never ends; only leaving.
fn diverging<'a>(
    source: &'a Source,
    clauses: &HashMap<&str, Vec<Clause>>,
    routines: &'a Routines,
) -> HashSet<&'a str> {
    fn leaves(term: &Term, held: &HashSet<&str>) -> bool {
        held.contains(term.0.as_str()) || term.1.iter().any(|argument| leaves(argument, held))
    }
    let mut held: HashSet<&str> = routines
        .offered()
        .filter(|(_, routine)| !routine.comes_back())
        .map(|(called, _)| called)
        .collect();
    let mut growing = true;
    while growing {
        growing = false;
        for name in &source.order {
            if held.contains(name.as_str()) {
                continue;
            }
            let every = clauses[name.as_str()].iter().all(|clause| {
                clause.steps.iter().any(|(_, step)| leaves(step, &held))
                    || leaves(&clause.body, &held)
            });
            if every {
                held.insert(name.as_str());
                growing = true;
            }
        }
    }
    held
}

fn tell(unify: &mut Unify, slot: usize, name: &str) -> Result<TypeId, String> {
    unify
        .get(slot)
        .ok_or_else(|| format!("nothing says what type `{name}` works over"))
}

/// What a term is read against: the types a program declared, the slots
/// every name takes, and which names do not come back.
///
/// None of it changes while a program is read, and all of it is wanted
/// wherever a term is, so it is carried rather than handed over one piece
/// at a time.
struct Reading<'a> {
    program: &'a Program,
    ctors: &'a HashMap<String, CtorId>,
    base: &'a HashMap<&'a str, usize>,
    arity: &'a HashMap<&'a str, usize>,
    leaving: &'a HashSet<&'a str>,
}

impl Reading<'_> {
    /// What a name takes and answers, once everything it is used at agrees.
    fn settled(&self, unify: &mut Unify, name: &str) -> Result<Inferred, String> {
        let at = self.base[name];
        let params = (0..self.arity[name])
            .map(|argument| tell(unify, at + argument, name))
            .collect::<Result<_, _>>()?;
        let result = tell(unify, at + self.arity[name], name)?;
        Ok((params, result))
    }

    /// The slot a clause's patterns bind, and the scope they bind into.
    ///
    /// A pattern one constructor deep says the type of what it matched and
    /// of every name it binds, so a clause settles its own arguments.
    fn bound<'b>(
        &self,
        clause: &'b Clause,
        base: usize,
        unify: &mut Unify,
    ) -> Result<HashMap<&'b str, usize>, String> {
        let mut scope = HashMap::new();
        for (at, pattern) in clause.patterns.iter().enumerate() {
            match pattern {
                Pattern::Bind(held) => {
                    scope.insert(held.as_str(), base + at);
                }
                Pattern::Ctor(ctor, fields) => {
                    let id = *self
                        .ctors
                        .get(ctor)
                        .ok_or_else(|| format!("no constructor named `{ctor}`"))?;
                    unify.pin(base + at, self.program.ctor(id).owner)?;
                    for (field, held) in self.program.fields(id).to_vec().iter().zip(fields) {
                        let slot = unify.fresh();
                        unify.pin(slot, *field)?;
                        scope.insert(held.as_str(), slot);
                    }
                }
            }
        }
        Ok(scope)
    }

    /// The slot a term's type lives in, constraining what it is built from.
    fn term(
        &self,
        held: &Term,
        scope: &HashMap<&str, usize>,
        unify: &mut Unify,
    ) -> Result<usize, String> {
        let Term(name, args) = held;
        if let Some(slot) = scope.get(name.as_str()) {
            if args.is_empty() {
                return Ok(*slot);
            }
            return Err(format!("`{name}` is a value, not something to apply"));
        }
        if let Some(ctor) = self.ctors.get(name) {
            let fields = self.program.fields(*ctor).to_vec();
            if fields.len() != args.len() {
                return Err(format!("`{name}` takes {} fields", fields.len()));
            }
            for (argument, field) in args.iter().zip(fields) {
                let slot = self.term(argument, scope, unify)?;
                unify.pin(slot, field)?;
            }
            let answer = unify.fresh();
            unify.pin(answer, self.program.ctor(*ctor).owner)?;
            return Ok(answer);
        }
        let at = *self.base.get(name.as_str()).ok_or_else(|| {
            if name == BUILTIN[0] {
                format!("`{name}` cannot be built; it is what `main!` is handed")
            } else if name == BUILTIN[NEVER.index()] {
                format!("`{name}` cannot be built; it is what a term that leaves answers")
            } else {
                format!("nothing named `{name}` is in scope")
            }
        })?;
        for (argument, index) in args.iter().zip(0..) {
            let slot = self.term(argument, scope, unify)?;
            unify.union(slot, at + index)?;
        }
        if !self.leaving.contains(name.as_str()) {
            return Ok(at + args.len());
        }
        // A call that does not come back answers `Never`, and a use of it takes
        // a slot of its own rather than the name's result: what stands beside
        // this use settles this use, and every other use stays free.
        let answer = unify.fresh();
        unify.pin(answer, NEVER)?;
        Ok(answer)
    }
}
