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
use super::validate::validate;
use crate::platform::{Routine, Routines, reads};

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
pub fn lower(
    program: &barb::Program,
    facts: &barb::Facts,
    routines: &Routines,
) -> Result<Program, String> {
    barb::validate(program)?;
    let entry = program.entry().expect("a program to lower has an entry");
    // Whether a value of each type takes a place at all. What place is a
    // question per value, which is why this answers nothing about width.
    let carries: Vec<Option<()>> = (0..program.types().len())
        .map(|at| represent(program, barb::TypeId::at(at)))
        .collect::<Result<_, _>>()?;

    let reached = reached(program, entry);
    let (mut machine, main) =
        Program::with(program.name(program.function(entry).name), routines.clone());
    let (functions, platforms) = declare(
        program,
        facts,
        routines,
        &carries,
        &mut machine,
        (entry, main),
        &reached,
    )?;

    let lowering = Lowering {
        barb: program,
        facts,
        carries,
        functions,
        platforms,
    };
    for (at, reached) in reached.iter().enumerate() {
        let id = barb::FnId::at(at);
        if *reached && facts.operation(id).is_none() && program.function(id).body.is_some() {
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
fn declare<'a>(
    program: &barb::Program,
    facts: &barb::Facts,
    routines: &'a Routines,
    carries: &[Option<()>],
    machine: &mut Program,
    (entry, main): (barb::FnId, FunctionId),
    reached: &[bool],
) -> Result<
    (
        Vec<Option<FunctionId>>,
        Vec<(barb::FnId, PlatformId, &'a Routine)>,
    ),
    String,
> {
    // `None` where a definition became an instruction and has no function.
    let mut functions: Vec<Option<FunctionId>> = Vec::with_capacity(program.functions().len());
    let mut platforms: Vec<(barb::FnId, PlatformId, &Routine)> = Vec::new();
    for (at, reached) in reached.iter().enumerate() {
        let id = barb::FnId::at(at);
        if id == entry {
            functions.push(Some(main));
            continue;
        }
        // A definition the tier below has an instruction for is never
        // emitted: its callers write the instruction instead. Neither is one
        // nothing reaches, which has no callers to write anything.
        if facts.operation(id).is_some() || !reached {
            functions.push(None);
            continue;
        }
        let function = program.function(id);
        // A parameter or a result that carries nothing takes no slot.
        let params: Vec<Class> = program
            .params(id)
            .iter()
            .zip(facts.takes(id))
            .filter(|(type_, _)| carries[type_.index()].is_some())
            .map(|(_, held)| width(*held))
            .collect();
        let returns: Vec<Class> = carries[function.result.index()]
            .map(|()| width(facts.answers(id)))
            .into_iter()
            .collect();
        let name = program.name(function.name);
        // One something else answers for is a platform routine rather than a
        // function: the program declares it and a target provides it.
        functions.push(Some(if function.body.is_some() {
            machine.declare(name, &params, &returns)
        } else {
            // What a program calls it and what answers for it need not be
            // the same name, so that one routine may serve a program at
            // more than one type.
            let outside = function.outside.map_or(name, |held| program.name(held));
            let (held, wanted) = provided(routines, name, outside, &params, &returns)?;
            platforms.push((id, machine.platform(held), wanted));
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
fn provided<'a>(
    routines: &'a Routines,
    name: &str,
    outside: &str,
    params: &[Class],
    returns: &[Class],
) -> Result<(&'a str, &'a Routine), String> {
    let Some(wanted) = routines.get(outside) else {
        return Err(format!("nothing answers for `{name}`"));
    };
    let held = wanted.name.as_str();
    // What is handed over is converted to what the routine reads, so what
    // has to agree is how many of them: a value of a type carrying nothing
    // is not handed over at all, and then there is no value where one is
    // read.
    if params.len() != wanted.takes.len() {
        return Err(format!(
            "`{held}` reads {}, and is handed {}",
            reads(&wanted.takes),
            reads(params),
        ));
    }
    if returns.len() != wanted.answers.len() {
        return Err(format!(
            "`{held}` answers {}, and what is taken back is {}",
            reads(&wanted.answers),
            reads(returns),
        ));
    }
    Ok((held, wanted))
}

/// Which definitions the entry can reach, by definition. A program is what
/// runs from its entry, and a name nothing calls is not part of it -- so it
/// is not emitted, and nothing below this tier hears of it.
fn reached(program: &barb::Program, entry: barb::FnId) -> Vec<bool> {
    fn within(program: &barb::Program, body: barb::Body, held: &mut Vec<barb::FnId>) {
        for expr in program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
            .copied()
        {
            match program.expr(expr) {
                barb::Expr::Call(id, _) => held.push(id),
                barb::Expr::Match(_, arms) => {
                    for arm in program.arms(arms).to_vec() {
                        within(program, arm.body, held);
                    }
                }
                barb::Expr::Atom(_) | barb::Expr::Con(..) | barb::Expr::Static(..) => {}
            }
        }
    }

    let mut reached = vec![false; program.functions().len()];
    let mut waiting = vec![entry];
    while let Some(id) = waiting.pop() {
        if std::mem::replace(&mut reached[id.index()], true) {
            continue;
        }
        if let Some(body) = program.function(id).body {
            within(program, body, &mut waiting);
        }
    }
    reached
}

/// The class a type's values take. Numbers and tags are decided so far.
fn represent(program: &barb::Program, id: barb::TypeId) -> Result<Option<()>, String> {
    let name = program.name(program.type_(id).name);
    if uninhabited(program, id) || erased(program, id) {
        return Ok(None);
    }
    if tagged(program, id) {
        return Ok(Some(()));
    }
    let barb::Shape::Spine { cons, .. } = barb::shape(program, id) else {
        return Err(format!("`{name}` has no representation in this tier yet"));
    };
    if program.fields(cons).len() == 1 {
        // A number takes a place. How wide is not a question about the type
        // -- every `Nat` is the same type and they are not all the same
        // size -- so it is asked of each value, where the tier above
        // answered it.
        return Ok(Some(()));
    }
    Err(format!(
        "`{name}` carries something per element, which has no representation in this tier yet"
    ))
}

/// A type with one constructor and no fields says nothing by being one value
/// rather than another, so it needs no bits and no argument. The authority a
/// program is handed is such a type, and so is what a routine answers when it
/// answers nothing.
fn erased(program: &barb::Program, id: barb::TypeId) -> bool {
    let ctors = program.ctors(id);
    ctors.len() == 1 && program.types_of(ctors[0].fields).is_empty()
}

/// The narrowest class holding every value a term answers. A width is what
/// a value needs and not what it wraps at, so this narrows nothing: what a
/// target holds it in is whatever it has that is at least this wide.
///
/// Where nothing bounds the values there is nothing to say but a machine
/// word, which is the placeholder rule -- sound while the number fits one,
/// and this is where it stops saying so of numbers it can see the size of.
fn width(held: barb::Bounds) -> Class {
    held.width().map_or(Class::Word, |bits| Class::Fixed {
        // A value that can only be nought still takes a place to be nought
        // in, until something makes it worth not taking one.
        bits: u16::try_from(bits.max(1)).expect("a width a machine has"),
    })
}

/// A type with no constructors has no values, so nothing holds one and
/// nothing is passed. What is said to answer one does not answer.
fn uninhabited(program: &barb::Program, id: barb::TypeId) -> bool {
    program.ctors(id).is_empty()
}

/// A type whose constructors all carry nothing says which one it is and
/// says nothing else, so a value of one is which: the tag, in a word.
/// `Bool` is such a type, and so is an ordering, and so is anything a
/// program writes as a run of bare names.
///
/// One such constructor is [`erased`] rather than tagged: a value that
/// could not have been anything else says nothing by being itself.
fn tagged(program: &barb::Program, id: barb::TypeId) -> bool {
    let ctors = program.ctors(id);
    ctors.len() > 1
        && ctors
            .iter()
            .all(|ctor| program.types_of(ctor.fields).is_empty())
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

/// Every value at the width that reads it, where what reads it was worked
/// out from the same bounds the value was.
///
/// A class is what a term could need rather than what it does: a field
/// stepped down from a scrutinee is held at the scrutinee's width, while the
/// tier above may have proved it smaller. So narrowing here takes nothing
/// off, and what it narrows to is a width that tier chose.
///
/// Nothing like that holds where a width came from outside. A routine reads
/// what it reads whatever a program worked out, so a value not fitting one
/// is a program refused rather than a value quietly made to fit -- which is
/// what [`super::model::Op::Convert`] is for, a program asking.
fn met(b: &mut super::Builder, args: &[ValueId], takes: &[Class]) -> Vec<ValueId> {
    args.iter()
        .zip(takes)
        .map(|(&arg, &wanted)| {
            if b.class(arg).fits(wanted) {
                arg
            } else {
                b.convert(wanted, arg)
            }
        })
        .collect()
}

/// Where two arms meet: what they leave with is one place, so it is as wide
/// as either of them needs.
fn widest(held: Answer<Class>, other: Answer<Class>) -> Answer<Class> {
    match (held.held(), other.held()) {
        (Some(held), Some(other)) if other.fits(held) => Answer::Value(held),
        (Some(_), Some(other)) => Answer::Value(other),
        _ => held.or(other),
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
    /// Whether a value of each barb type takes a place, by type.
    carries: Vec<Option<()>>,
    /// The machine function each barb function became, by function, and
    /// `None` for one that became an instruction.
    functions: Vec<Option<FunctionId>>,
    /// The platform routine each declared-elsewhere function became.
    platforms: Vec<(barb::FnId, PlatformId, &'a Routine)>,
}

impl Lowering<'_> {
    /// The class a term answers at, which is how wide what it answers can
    /// be. Two values of one type may be held differently, since what makes
    /// them wide is what was done with them and not what they are.
    fn width(&self, id: barb::ExprId) -> Class {
        width(self.facts.held(id))
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
            .map(|type_| self.carries[type_.index()].is_none())
            .collect();
        // What it leaves with: a word from the entry, whatever the program
        // worked in, and otherwise the width it was declared at.
        let returns = if entry {
            Class::Word
        } else {
            width(self.facts.answers(id))
        };
        machine.define(into, |b, params| {
            let mut taken = params.iter().copied();
            let mut locals: Vec<Option<ValueId>> = erased
                .iter()
                .map(|erased| (!erased).then(|| taken.next().expect("a parameter")))
                .collect();
            match self.body(b, body, &mut locals) {
                // The entry leaves with a word, whatever width it worked
                // in, since that is what the machine takes; and every
                // definition leaves at the width it was worked out at.
                Answer::Value(answer) => {
                    let answer = met(b, &[answer], &[returns])[0];
                    b.ret(&[answer])
                }
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
            // A value the tier above worked out, as the word it lowers to:
            // which constructor for a tag, and what it counts to for a
            // number. One that carries nothing is nothing to carry.
            barb::Expr::Static(id, value) => {
                let Some(()) = self.carries[id.index()] else {
                    return Answer::Nothing;
                };
                let class = self.width(expr);
                let bytes = self.barb.known_bytes(value);
                let held = if tagged(self.barb, id) {
                    u64::from(self.barb.tag(barb::decode(self.barb, id, bytes).0.0))
                } else {
                    barb::as_number(self.barb, id, bytes).expect("a number")
                };
                Answer::Value(b.constant(class, held))
            }
            barb::Expr::Con(ctor, args) => self.construct(b, expr, ctor, args, locals).into(),
            barb::Expr::Call(function, args) => self.call(b, expr, function, args, locals),
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
        expr: barb::ExprId,
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
            let class = self.width(expr);
            return Answer::Value(b.binary_at(class, Binary::Add, args[0], args[1]));
        }
        let held = self.platforms.iter().find(|(id, ..)| *id == function);
        let (results, answers) = if let Some((_, platform, wanted)) = held {
            (b.platform_call(*platform, &args), wanted.answers.first())
        } else {
            let callee = self.functions[function.index()]
                .expect("a call to something that stayed a function");
            let takes = b.takes(callee);
            let args = met(b, &args, &takes);
            (b.call(callee, &args), None)
        };
        // A call answers what its result type does, which is nothing ever
        // where that type has no values -- and it answers at the width the
        // name it calls was declared at, which the caller may hold wider.
        self.answer(self.barb.function(function).result).map(|_| {
            let class = self.width(expr);
            let held = *results.first().expect("a result where a type carries one");
            if answers.is_some_and(|answers| !answers.fits(class)) {
                b.convert(class, held)
            } else {
                held
            }
        })
    }

    /// A tag is which constructor it is. A number's empty constructor is
    /// nought and its other one counts up -- which is not the same as its
    /// tag, since a program may write `Succ` before `Zero`. One that
    /// carries nothing builds nothing.
    fn construct(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        ctor: barb::CtorId,
        args: barb::Range,
        locals: &[Option<ValueId>],
    ) -> Option<ValueId> {
        let owner = self.barb.ctor(ctor).owner;
        self.carries[owner.index()]?;
        let class = self.width(expr);
        if tagged(self.barb, owner) {
            return Some(b.constant(class, u64::from(self.barb.tag(ctor))));
        }
        let Some(&atom) = self.barb.atoms(args).first() else {
            return Some(b.constant(class, 0));
        };
        let one = b.constant(class, 1);
        let held = locals[atom.0.index()].expect("a field that carries something");
        Some(b.binary_at(class, Binary::Add, held, one))
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
        // Read at the width what it is taking apart is held at, since that
        // is what the comparison and the step down are against.
        let class = b.class(scrutinee);
        let barb::Shape::Spine { nil, .. } = barb::shape(self.barb, owner) else {
            return self.tags(b, scrutinee, class, &arms, locals);
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
        // The counting arm binds what the scrutinee wraps, which holds what
        // the scrutinee holds.
        let mut inner = locals.to_vec();
        inner.push(Some(scrutinee));
        let answer = self
            .answers(b, empty.body, locals)
            .or(self.answers(b, counted.body, &inner));
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

    /// Matching a tag asks which one it is, arm by arm. The last needs no
    /// asking: nothing else is left for the value to be.
    ///
    /// A run of tests is what a target has instructions for. Anything
    /// cleverer -- a jump table, a search -- wants more constructors than
    /// anything here has, and would be this tier deciding what a target is
    /// better placed to.
    fn tags(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        class: Class,
        arms: &[barb::Arm],
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let (arm, rest) = arms.split_first().expect("an arm to match");
        if rest.is_empty() {
            let mut inner = locals.to_vec();
            return self.body(b, arm.body, &mut inner);
        }

        let answer = arms
            .iter()
            .map(|arm| self.answers(b, arm.body, locals))
            .fold(Answer::Never, widest);
        let held: Vec<Class> = answer.held().into_iter().collect();
        let tag = b.constant(class, u64::from(self.barb.tag(arm.ctor)));
        let is_this_one = b.compare(Relation::Equal, scrutinee, tag);
        let results = b.if_(
            is_this_one,
            &held,
            |b| {
                let mut inner = locals.to_vec();
                let answer = self.body(b, arm.body, &mut inner);
                yielded(b, answer)
            },
            |b| {
                let answer = self.tags(b, scrutinee, class, rest, locals);
                yielded(b, answer)
            },
        );
        answer.map(|_| *results.first().expect("a result where the arms carry one"))
    }

    /// What a body answers, read off its shape: an `if` has to be told what
    /// its arms leave with before either of them is lowered.
    ///
    /// A body that answers a name it was given answers whatever that name
    /// is, which is why this needs the locals: nothing about the term says
    /// how wide the value it names is.
    fn answers(
        &self,
        b: &super::Builder,
        body: barb::Body,
        locals: &[Option<ValueId>],
    ) -> Answer<Class> {
        match self.barb.expr(body.tail) {
            barb::Expr::Static(id, _) => self.answer(id),
            barb::Expr::Con(ctor, _) => self.answer(self.barb.ctor(ctor).owner),
            barb::Expr::Call(function, _) => self.answer(self.barb.function(function).result),
            barb::Expr::Match(scrutinee, arms) => {
                // A constructor's fields are the next locals, and what they
                // hold is what the value they came out of holds.
                let mut inner = locals.to_vec();
                let held = locals[scrutinee.0.index()];
                self.barb
                    .arms(arms)
                    .iter()
                    .map(|arm| {
                        inner.resize(locals.len(), None);
                        inner.resize(locals.len() + self.barb.fields(arm.ctor).len(), held);
                        self.answers(b, arm.body, &inner)
                    })
                    .fold(Answer::Never, Answer::or)
            }
            barb::Expr::Atom(atom) => locals[atom.0.index()]
                .map_or(Answer::Nothing, |value| Answer::Value(b.class(value))),
        }
    }

    /// What a type answers with: its class, nothing where it carries
    /// nothing, and nothing ever where it has no values at all.
    fn answer(&self, id: barb::TypeId) -> Answer<Class> {
        if uninhabited(self.barb, id) {
            return Answer::Never;
        }
        self.carries[id.index()].map(|()| Class::Word).into()
    }
}
