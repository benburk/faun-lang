//! Lowering barb into the machine tier.
//!
//! This is where a value stops being a term and becomes storage, which is
//! this tier's job rather than barb's or a target's. Two rules so far:
//!
//! - a spine-shaped type whose elements carry nothing is a number, and a
//!   number is a machine word. `Zero` is nought, `Succ(n)` is `n + 1`, and
//!   matching one asks whether it is nought.
//! - a type with no constructors has no values, so a term answering one
//!   does not answer: what it does is laid out, and nothing after it is.
//!
//! The first is sound only while the number fits a word. A bound says when,
//! and nothing derives bounds yet, so that one is a placeholder for the rule
//! rather than the rule.

use crate::barb;

use super::model::{Binary, Class, FunctionId, PlatformId, Program, Relation, Terminator, ValueId};
use super::platform::{reads, routine};
use super::validate::validate;

/// Lower a whole program, or say what it holds that this tier cannot yet
/// represent.
///
/// # Errors
///
/// Names the first type whose representation is not decided.
///
/// # Panics
///
/// If `program` has no entry.
pub fn lower(program: &barb::Program, facts: &barb::Facts) -> Result<Program, String> {
    let entry = program.entry().expect("a program to lower has an entry");
    let classes: Vec<Option<Class>> = (0..program.types().len())
        .map(|at| represent(program, barb::TypeId::at(at)))
        .collect::<Result<_, _>>()?;

    let (mut machine, main) = Program::new(program.name(program.function(entry).name));
    let (functions, platforms) = declare(program, facts, &classes, &mut machine, (entry, main))?;

    let lowering = Lowering {
        barb: program,
        facts,
        classes,
        functions,
        platforms,
    };
    for at in 0..program.functions().len() {
        let id = barb::FnId::at(at);
        if facts.operation(id).is_none() && program.function(id).body.is_some() {
            lowering.function(&mut machine, id);
        }
    }
    validate(&machine)?;
    Ok(machine)
}

/// Every definition, as what it becomes: a function, an instruction, or a
/// routine something outside provides.
#[expect(
    clippy::type_complexity,
    reason = "what each definition became, by definition"
)]
fn declare(
    program: &barb::Program,
    facts: &barb::Facts,
    classes: &[Option<Class>],
    machine: &mut Program,
    (entry, main): (barb::FnId, FunctionId),
) -> Result<(Vec<Option<FunctionId>>, Vec<(barb::FnId, PlatformId)>), String> {
    // `None` where a definition became an instruction and has no function.
    let mut functions: Vec<Option<FunctionId>> = Vec::with_capacity(program.functions().len());
    let mut platforms: Vec<(barb::FnId, PlatformId)> = Vec::new();
    for at in 0..program.functions().len() {
        let id = barb::FnId::at(at);
        if id == entry {
            functions.push(Some(main));
            continue;
        }
        // A definition the tier below has an instruction for is never
        // emitted: its callers write the instruction instead.
        if facts.operation(id).is_some() {
            functions.push(None);
            continue;
        }
        let function = program.function(id);
        // A parameter or a result that carries nothing takes no slot.
        let params: Vec<Class> = program
            .params(id)
            .iter()
            .filter_map(|type_| classes[type_.index()])
            .collect();
        let returns: Vec<Class> = classes[function.result.index()].into_iter().collect();
        let name = program.name(function.name);
        // One something else answers for is a platform routine rather than a
        // function: the program declares it and a target provides it.
        functions.push(Some(if function.body.is_some() {
            machine.declare(name, &params, &returns)
        } else {
            let held = provided(name, &params, &returns)?;
            platforms.push((id, machine.platform(held)));
            main
        }));
    }
    Ok((functions, platforms))
}

/// The routine answering for a name nothing defines, checked against what
/// that name means.
///
/// What a routine reads is what it is handed, and a value of a type that
/// carries nothing is not handed over at all. So a status that carries
/// nothing is no status, and saying so here beats three targets reading
/// past the end of their arguments.
fn provided(name: &str, params: &[Class], returns: &[Class]) -> Result<&'static str, String> {
    // The `!` says the program may observe this one working; the routine a
    // target provides is named without it.
    let held = name.strip_suffix('!').unwrap_or(name);
    let Some(wanted) = routine(held) else {
        return Err(format!("nothing answers for `{name}`"));
    };
    if params != wanted.takes {
        return Err(format!(
            "`{name}` hands over {}, but `{held}` reads {}",
            reads(params),
            reads(wanted.takes),
        ));
    }
    if returns != wanted.answers {
        return Err(format!(
            "`{name}` takes back {}, but `{held}` answers {}",
            reads(returns),
            reads(wanted.answers),
        ));
    }
    Ok(wanted.name)
}

/// The class a type's values take. Only numbers are decided so far.
fn represent(program: &barb::Program, id: barb::TypeId) -> Result<Option<Class>, String> {
    let name = program.name(program.type_(id).name);
    if uninhabited(program, id) || erased(program, id) {
        return Ok(None);
    }
    let barb::Shape::Spine { cons, .. } = barb::shape(program, id) else {
        return Err(format!("`{name}` has no representation in this tier yet"));
    };
    if program.fields(cons).len() == 1 {
        return Ok(Some(Class::Word));
    }
    Err(format!(
        "`{name}` carries something per element, which has no representation in this tier yet"
    ))
}

/// A type with one constructor and no fields says nothing by being one value
/// rather than another, so it needs no bits and no argument. The authority a
/// program is handed is such a type, and so is what an effect answers when it
/// answers nothing.
fn erased(program: &barb::Program, id: barb::TypeId) -> bool {
    let ctors = program.ctors(id);
    ctors.len() == 1 && program.types_of(ctors[0].fields).is_empty()
}

/// A type with no constructors has no values, so nothing holds one and
/// nothing is passed. What is said to answer one does not answer.
fn uninhabited(program: &barb::Program, id: barb::TypeId) -> bool {
    program.ctors(id).is_empty()
}

/// What a term answers: a value, nothing because its type carries nothing,
/// or nothing ever because the term does not come back.
#[derive(Clone, Copy, Debug)]
enum Answer<T> {
    Value(T),
    Nothing,
    Never,
}

impl<T> From<Option<T>> for Answer<T> {
    /// What something that may hold a value answers. A type carrying nothing
    /// holds none, and that is `Nothing`: it is the term that says `Never`,
    /// not the storage.
    fn from(held: Option<T>) -> Self {
        held.map_or(Self::Nothing, Self::Value)
    }
}

impl<T> Answer<T> {
    /// The value, where there is one. `Nothing` and `Never` both hold none:
    /// what tells them apart is what a region does after them, not what it
    /// carries out.
    fn held(self) -> Option<T> {
        match self {
            Self::Value(value) => Some(value),
            Self::Nothing | Self::Never => None,
        }
    }

    /// Where two paths join. A path that does not come back says nothing
    /// about what the join carries, so the other one says it.
    fn or(self, other: Self) -> Self {
        match self {
            Self::Never => other,
            held => held,
        }
    }

    fn map<U>(self, held: impl FnOnce(T) -> U) -> Answer<U> {
        match self {
            Self::Value(value) => Answer::Value(held(value)),
            Self::Nothing => Answer::Nothing,
            Self::Never => Answer::Never,
        }
    }
}

/// Leave an arm with what its body answered. An arm that does not come back
/// never reaches the join, so it carries nothing there.
fn yielded(b: &mut super::Builder, answer: Answer<ValueId>) -> Terminator {
    match answer {
        Answer::Value(value) => b.yield_(&[value]),
        Answer::Nothing => b.yield_(&[]),
        Answer::Never => Terminator::UNREACHABLE,
    }
}

struct Lowering<'a> {
    barb: &'a barb::Program,
    facts: &'a barb::Facts,
    /// The class each barb type takes, by type, and nothing where it is
    /// erased.
    classes: Vec<Option<Class>>,
    /// The machine function each barb function became, by function, and
    /// `None` for one that became an instruction.
    functions: Vec<Option<FunctionId>>,
    /// The platform routine each declared-elsewhere function became.
    platforms: Vec<(barb::FnId, PlatformId)>,
}

impl Lowering<'_> {
    /// The class a type takes, where it takes one.
    fn class(&self, id: barb::TypeId) -> Class {
        self.classes[id.index()].expect("a type that carries something")
    }

    fn function(&self, machine: &mut Program, id: barb::FnId) {
        let body = self.barb.function(id).body.expect("a function with a body");
        let into = self.functions[id.index()].expect("a function that is not an instruction");
        let entry = self.barb.entry() == Some(id);
        // An erased parameter takes no slot, so the machine's run of them is
        // shorter than barb's and they are matched up in order.
        let erased: Vec<bool> = self
            .barb
            .params(id)
            .iter()
            .map(|type_| self.classes[type_.index()].is_none())
            .collect();
        machine.define(into, |b, params| {
            let mut taken = params.iter().copied();
            let mut locals: Vec<Option<ValueId>> = erased
                .iter()
                .map(|erased| (!erased).then(|| taken.next().expect("a parameter")))
                .collect();
            match self.body(b, body, &mut locals) {
                Answer::Value(answer) => b.ret(&[answer]),
                // The entry answers a status whatever the program says, and
                // reaches here only where nothing has already left.
                Answer::Nothing if entry => {
                    let status = b.constant(Class::Word, 0);
                    b.ret(&[status])
                }
                Answer::Nothing => b.ret(&[]),
                // Nothing comes back from here, so there is nothing to
                // return and nowhere to return to.
                Answer::Never => Terminator::UNREACHABLE,
            }
        });
    }

    /// Each binding takes the next local, then the tail answers.
    fn body(
        &self,
        b: &mut super::Builder,
        body: barb::Body,
        locals: &mut Vec<Option<ValueId>>,
    ) -> Answer<ValueId> {
        for binding in self.barb.bindings(body.bindings).to_vec() {
            match self.expr(b, binding, locals) {
                Answer::Value(value) => locals.push(Some(value)),
                Answer::Nothing => locals.push(None),
                // A body leaves where its bindings do: nothing after this
                // one is reached, so nothing after it is lowered.
                Answer::Never => return Answer::Never,
            }
        }
        self.expr(b, body.tail, locals)
    }

    fn expr(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        match self.barb.expr(expr) {
            barb::Expr::Atom(atom) => locals[atom.0.index()].into(),
            barb::Expr::Static(id, value) => {
                let bytes = self.barb.known_bytes(value);
                let number = barb::as_number(self.barb, id, bytes).expect("a number");
                Answer::Value(b.constant(self.class(id), number))
            }
            barb::Expr::Con(ctor, args) => self.construct(b, ctor, args, locals).into(),
            barb::Expr::Call(function, args) => self.call(b, function, args, locals),
            barb::Expr::Match(scrutinee, arms) => {
                let scrutinee = locals[scrutinee.0.index()].expect("a scrutinee to match");
                self.branch(b, scrutinee, arms, locals)
            }
        }
    }

    /// An instruction where the tier below has one, a platform routine where
    /// something outside answers, and a call otherwise. An argument that
    /// carries nothing is not passed.
    fn call(
        &self,
        b: &mut super::Builder,
        function: barb::FnId,
        args: barb::Range,
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let args: Vec<ValueId> = self
            .barb
            .atoms(args)
            .iter()
            .filter_map(|atom| locals[atom.0.index()])
            .collect();
        if self.facts.operation(function) == Some(barb::Operation::Add) {
            return Answer::Value(b.binary(Binary::Add, args[0], args[1]));
        }
        let results =
            if let Some((_, platform)) = self.platforms.iter().find(|(id, _)| *id == function) {
                b.platform_call(*platform, &args)
            } else {
                let callee = self.functions[function.index()]
                    .expect("a call to something that stayed a function");
                b.call(callee, &args)
            };
        // A call answers what its result type does, which is nothing ever
        // where that type has no values.
        self.answer(self.barb.function(function).result)
            .map(|_| *results.first().expect("a result where a type carries one"))
    }

    /// A number's empty constructor is nought, and its other one counts up.
    /// One that carries nothing builds nothing.
    fn construct(
        &self,
        b: &mut super::Builder,
        ctor: barb::CtorId,
        args: barb::Range,
        locals: &[Option<ValueId>],
    ) -> Option<ValueId> {
        let owner = self.barb.ctor(ctor).owner;
        let class = self.classes[owner.index()]?;
        let Some(&atom) = self.barb.atoms(args).first() else {
            return Some(b.constant(class, 0));
        };
        let one = b.constant(class, 1);
        let held = locals[atom.0.index()].expect("a field that carries something");
        Some(b.binary(Binary::Add, held, one))
    }

    /// Matching a number asks whether it is nought; the other arm counts the
    /// scrutinee back down to what it wraps.
    fn branch(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        arms: barb::Range,
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let arms = self.barb.arms(arms).to_vec();
        let owner = self.barb.ctor(arms[0].ctor).owner;
        let class = self.class(owner);
        let barb::Shape::Spine { nil, .. } = barb::shape(self.barb, owner) else {
            unreachable!("only numbers are represented");
        };
        let empty = arms
            .iter()
            .find(|arm| arm.ctor == nil)
            .expect("an empty arm");
        let counted = arms
            .iter()
            .find(|arm| arm.ctor != nil)
            .expect("a counting arm");

        // Both arms answer alike, so whichever of them comes back says what
        // the match holds. An arm that leaves says nothing about it.
        let answer = self.answers(empty.body).or(self.answers(counted.body));
        let held: Vec<Class> = answer.held().into_iter().collect();
        let nought = b.constant(class, 0);
        let is_nought = b.compare(Relation::Equal, scrutinee, nought);
        let results = b.if_(
            is_nought,
            &held,
            |b| {
                let mut inner = locals.to_vec();
                let answer = self.body(b, empty.body, &mut inner);
                yielded(b, answer)
            },
            |b| {
                let mut inner = locals.to_vec();
                let one = b.constant(class, 1);
                inner.push(Some(b.binary(Binary::Sub, scrutinee, one)));
                let answer = self.body(b, counted.body, &mut inner);
                yielded(b, answer)
            },
        );
        answer.map(|_| *results.first().expect("a result where the arms carry one"))
    }

    /// What a body answers, read off its shape: an `if` has to be told what
    /// its arms leave with before either of them is lowered.
    fn answers(&self, body: barb::Body) -> Answer<Class> {
        match self.barb.expr(body.tail) {
            barb::Expr::Static(id, _) => self.answer(id),
            barb::Expr::Con(ctor, _) => self.answer(self.barb.ctor(ctor).owner),
            barb::Expr::Call(function, _) => self.answer(self.barb.function(function).result),
            barb::Expr::Match(_, arms) => self
                .barb
                .arms(arms)
                .iter()
                .map(|arm| self.answers(arm.body))
                .fold(Answer::Never, Answer::or),
            barb::Expr::Atom(_) => Answer::Value(Class::Word),
        }
    }

    /// What a type answers with: its class, nothing where it carries
    /// nothing, and nothing ever where it has no values at all.
    fn answer(&self, id: barb::TypeId) -> Answer<Class> {
        if uninhabited(self.barb, id) {
            return Answer::Never;
        }
        self.classes[id.index()].into()
    }
}
