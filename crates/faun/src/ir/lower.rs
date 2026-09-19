//! Lowering barb into the machine tier.
//!
//! This is where a value stops being a term and becomes storage, which is
//! this tier's job rather than barb's or a target's. Two rules so far:
//!
//! - a spine-shaped type whose elements carry nothing is an unbounded
//!   natural. Proven bounds can select a fixed width; unknown bounds cannot.
//!   `Zero` is nought, `Succ(n)` is `n + 1`, and a match tests for nought.
//! - a type with no constructors has no values, so a term answering one
//!   does not answer: what it does is laid out, and nothing after it is.
//!
//! Targets without arbitrary-precision support reject that class explicitly.

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
    // Only values actually lowered need a representation. Merely declaring
    // a library type (or retaining an old expression in the arena) does not.
    let demand = Demand::discover(program, facts, entry)?;
    let (mut machine, main) =
        Program::with(program.name(program.function(entry).name), routines.clone());
    let (functions, platforms) = declare(
        program,
        facts,
        routines,
        &demand.carries,
        &mut machine,
        (entry, main),
        &demand.reached,
    )?;

    let lowering = Lowering {
        barb: program,
        facts,
        carries: demand.carries,
        functions,
        platforms,
    };
    for (at, reached) in demand.reached.iter().enumerate() {
        let id = barb::FnId::at(at);
        if *reached && facts.operation(id).is_none() && program.function(id).body.is_some() {
            lowering.function(&mut machine, id)?;
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
    // Unlike internal range-proven narrowing, a host signature is not a
    // proof that its argument fits. In particular runtime Natural support
    // must never turn an implicit effect argument into modulo-word Convert.
    for (&actual, &expected) in params.iter().zip(&wanted.takes) {
        if !actual.fits(expected) {
            return Err(format!(
                "`{held}` requires {expected:?}, but its argument needs {actual:?}; host arguments must be proven to fit"
            ));
        }
    }
    if returns.len() != wanted.answers.iter().len() {
        return Err(format!(
            "`{held}` answers {}, and what is taken back is {}",
            reads(wanted.answers.as_slice()),
            reads(returns),
        ));
    }
    Ok((held, wanted))
}

/// Function and representation demand follow the same paths as emission:
/// recognized definitions become instructions, impossible arms disappear,
/// and a body stops at its first binding that cannot return.
struct Demand<'a> {
    program: &'a barb::Program,
    facts: &'a barb::Facts,
    reached: Vec<bool>,
    waiting: Vec<barb::FnId>,
    // An undemanded type has no slot. Every introduction of a lowered value
    // (signature, constructor, constant, or match field) checks it first;
    // unsupported representations are never mistaken for erased values.
    carries: Vec<Option<()>>,
}

impl<'a> Demand<'a> {
    fn discover(
        program: &'a barb::Program,
        facts: &'a barb::Facts,
        entry: barb::FnId,
    ) -> Result<Self, String> {
        let mut demand = Self {
            program,
            facts,
            reached: vec![false; program.functions().len()],
            waiting: vec![entry],
            carries: vec![None; program.types().len()],
        };
        while let Some(id) = demand.waiting.pop() {
            if std::mem::replace(&mut demand.reached[id.index()], true) {
                continue;
            }
            let function = program.function(id);
            for &ty in program.params(id).iter().chain([&function.result]) {
                demand.type_(ty)?;
            }
            if facts.operation(id).is_none()
                && let Some(body) = function.body
            {
                demand.body(body)?;
            }
        }
        Ok(demand)
    }

    fn type_(&mut self, ty: barb::TypeId) -> Result<(), String> {
        self.carries[ty.index()] = represent(self.program, ty)?;
        Ok(())
    }

    /// Whether this body can return, matching `Lowering::body`.
    fn body(&mut self, body: barb::Body) -> Result<bool, String> {
        for &expr in self
            .program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
        {
            if !self.expr(expr)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn expr(&mut self, expr: barb::ExprId) -> Result<bool, String> {
        match self.program.expr(expr) {
            barb::Expr::Atom(_) => {}
            barb::Expr::Static(ty, _) => self.type_(ty)?,
            barb::Expr::Con(ctor, _) => self.type_(self.program.ctor(ctor).owner)?,
            barb::Expr::Call(id, _) => {
                self.waiting.push(id);
                return Ok(!uninhabited(self.program, self.program.function(id).result));
            }
            barb::Expr::Match(_, arms) => {
                let mut returns = false;
                for arm in reachable(self.program, arms, self.facts.matched(expr)) {
                    for &ty in self.program.fields(arm.ctor) {
                        self.type_(ty)?;
                    }
                    // Visit every reachable arm, even after one can return.
                    returns |= self.body(arm.body)?;
                }
                return Ok(returns);
            }
        }
        Ok(true)
    }
}

/// Shared by demand discovery, answer analysis, and emission: types in an
/// impossible arm do not need storage any more than its calls need code.
fn reachable(program: &barb::Program, arms: barb::Range, bounds: barb::Bounds) -> Vec<barb::Arm> {
    program
        .arms(arms)
        .iter()
        .copied()
        .filter(
            |arm| match barb::shape(program, program.ctor(arm.ctor).owner) {
                barb::Shape::Spine { nil, .. } if arm.ctor == nil => bounds.low == 0,
                barb::Shape::Spine { .. } => bounds.high != Some(0),
                barb::Shape::Tagged => {
                    let tag = u64::from(program.tag(arm.ctor));
                    tag >= bounds.low && bounds.high.is_none_or(|high| tag <= high)
                }
            },
        )
        .collect()
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
/// Where nothing bounds the values, only an arbitrary-precision natural
/// preserves the semantics. A target may reject it, but may not wrap it.
fn width(held: barb::Bounds) -> Class {
    held.width().map_or(Class::Natural, |bits| Class::Fixed {
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
        (Some(held), Some(other)) => Answer::Value(super::arithmetic::widest(held, other)),
        _ => held.or(other),
    }
}

/// Leave an arm with what its body answered. An arm that does not come back
/// never reaches the join, so it carries nothing there.
fn yielded(b: &mut super::Builder, answer: Answer<ValueId>, classes: &[Class]) -> Terminator {
    match answer {
        Answer::Value(value) => {
            let values = met(b, &[value], classes);
            b.yield_(&values)
        }
        Answer::Nothing => b.yield_(&[]),
        Answer::Never => Terminator::UNREACHABLE,
    }
}

/// The entry's implicit status is a host word, not a request for modulo.
fn returned(
    b: &mut super::Builder,
    answer: Answer<ValueId>,
    entry: bool,
    returns: Class,
) -> Result<Terminator, String> {
    Ok(match answer {
        Answer::Value(answer) => {
            if entry && b.class(answer) == Class::Natural {
                return Err(
                    "the entry's result is unbounded, but its exit status must fit a word"
                        .to_owned(),
                );
            }
            let answer = met(b, &[answer], &[returns])[0];
            b.ret(&[answer])
        }
        Answer::Nothing if entry => {
            let status = b.constant(Class::Word, 0);
            b.ret(&[status])
        }
        Answer::Nothing => b.ret(&[]),
        Answer::Never => Terminator::UNREACHABLE,
    })
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

    fn function(&self, machine: &mut Program, id: barb::FnId) -> Result<(), String> {
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
        let mut failure = None;
        machine.define(into, |b, params| {
            let mut taken = params.iter().copied();
            let mut locals: Vec<Option<ValueId>> = erased
                .iter()
                .map(|erased| (!erased).then(|| taken.next().expect("a parameter")))
                .collect();
            let answer = self.body(b, body, &mut locals);
            returned(b, answer, entry, returns).unwrap_or_else(|error| {
                failure = Some(error);
                Terminator::UNREACHABLE
            })
        });
        failure.map_or(Ok(()), Err)
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
                if tagged(self.barb, id) {
                    let tag = u64::from(self.barb.tag(barb::decode(self.barb, id, bytes).0.0));
                    return Answer::Value(b.constant(class, tag));
                }
                if let Some(held) = barb::as_number(self.barb, id, bytes) {
                    Answer::Value(b.constant(class, held))
                } else {
                    Answer::Value(
                        b.natural(&barb::as_natural(self.barb, id, bytes).expect("a natural")),
                    )
                }
            }
            barb::Expr::Con(ctor, args) => self.construct(b, expr, ctor, args, locals).into(),
            barb::Expr::Call(function, args) => self.call(b, expr, function, args, locals),
            barb::Expr::Match(scrutinee, arms) => {
                let scrutinee = locals[scrutinee.0.index()].expect("a scrutinee to match");
                self.branch(b, scrutinee, arms, locals, self.facts.matched(expr))
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
        if let Some(operation) = self.facts.operation(function) {
            return Answer::Value(self.operation(b, operation, self.width(expr), &args));
        }
        let held = self.platforms.iter().find(|(id, ..)| *id == function);
        let (results, answers) = if let Some((_, platform, wanted)) = held {
            (b.platform_call(*platform, &args), wanted.answers.as_ref())
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
            if answers == Some(&Class::Word) {
                held
            } else if answers.is_some_and(|answers| !answers.fits(class)) {
                b.convert(class, held)
            } else {
                held
            }
        })
    }

    fn operation(
        &self,
        b: &mut super::Builder,
        operation: barb::Operation,
        class: Class,
        args: &[ValueId],
    ) -> ValueId {
        match operation {
            barb::Operation::Equals { yes, no } | barb::Operation::LessThan { yes, no } => {
                let relation = if matches!(operation, barb::Operation::Equals { .. }) {
                    Relation::Equal
                } else {
                    Relation::Less
                };
                let test = super::arithmetic::compare(b, relation, args[0], args[1]);
                b.if_(
                    test,
                    &[class],
                    |b| {
                        let value = b.constant(class, u64::from(self.barb.tag(yes)));
                        b.yield_(&[value])
                    },
                    |b| {
                        let value = b.constant(class, u64::from(self.barb.tag(no)));
                        b.yield_(&[value])
                    },
                )[0]
            }
            operation => super::arithmetic::lower(b, operation, class, args[0], args[1]),
        }
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
        Some(super::arithmetic::lower(
            b,
            barb::Operation::Add,
            class,
            held,
            one,
        ))
    }

    /// Matching a number asks whether it is nought; the other arm counts the
    /// scrutinee back down to what it wraps.
    fn branch(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        arms: barb::Range,
        locals: &[Option<ValueId>],
        bounds: barb::Bounds,
    ) -> Answer<ValueId> {
        let arms = self.reachable(arms, bounds);
        let Some(first) = arms.first() else {
            return Answer::Never;
        };
        let owner = self.barb.ctor(first.ctor).owner;
        if arms.len() == 1 {
            return self.only_arm(b, scrutinee, first, locals);
        }
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

        self.natural_branch(b, scrutinee, empty, counted, locals)
    }

    fn natural_branch(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        empty: &barb::Arm,
        counted: &barb::Arm,
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let class = b.class(scrutinee);
        // Both arms answer alike, so whichever of them comes back says what
        // the match holds. An arm that leaves says nothing about it.
        // The counting arm binds what the scrutinee wraps, which holds what
        // the scrutinee holds.
        let mut inner = locals.to_vec();
        inner.push(Some(scrutinee));
        let answer = self.answers(empty.body, locals);
        let answer = widest(answer, self.answers(counted.body, &inner));
        let held: Vec<Class> = answer.held().into_iter().collect();
        let nought = b.constant(class, 0);
        let is_nought = b.compare(Relation::Equal, scrutinee, nought);
        let results = b.if_(
            is_nought,
            &held,
            |b| {
                let mut inner = locals.to_vec();
                let answer = self.body(b, empty.body, &mut inner);
                yielded(b, answer, &held)
            },
            |b| {
                let mut inner = locals.to_vec();
                let one = b.constant(class, 1);
                inner.push(Some(b.binary(Binary::Sub, scrutinee, one)));
                let answer = self.body(b, counted.body, &mut inner);
                yielded(b, answer, &held)
            },
        );
        answer.map(|_| *results.first().expect("a result where the arms carry one"))
    }

    fn reachable(&self, arms: barb::Range, bounds: barb::Bounds) -> Vec<barb::Arm> {
        reachable(self.barb, arms, bounds)
    }

    fn only_arm(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        arm: &barb::Arm,
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let mut inner = locals.to_vec();
        if let barb::Shape::Spine { cons, .. } =
            barb::shape(self.barb, self.barb.ctor(arm.ctor).owner)
            && arm.ctor == cons
        {
            let one = b.constant(b.class(scrutinee), 1);
            inner.push(Some(b.binary(Binary::Sub, scrutinee, one)));
        }
        self.body(b, arm.body, &mut inner)
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
            .map(|arm| self.answers(arm.body, locals))
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
                yielded(b, answer, &held)
            },
            |b| {
                let answer = self.tags(b, scrutinee, class, rest, locals);
                yielded(b, answer, &held)
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
    fn answers(&self, body: barb::Body, locals: &[Option<ValueId>]) -> Answer<Class> {
        self.body_answer(body, locals.iter().map(Option::is_some).collect())
    }

    fn body_answer(&self, body: barb::Body, mut carried: Vec<bool>) -> Answer<Class> {
        for &binding in self.barb.bindings(body.bindings) {
            let answer = self.expr_answer(binding, &carried);
            if matches!(answer, Answer::Never) {
                return Answer::Never;
            }
            carried.push(answer.held().is_some());
        }
        self.expr_answer(body.tail, &carried)
    }

    fn expr_answer(&self, expr: barb::ExprId, carried: &[bool]) -> Answer<Class> {
        match self.barb.expr(expr) {
            barb::Expr::Static(id, _) => self.answer(id).map(|_| self.width(expr)),
            barb::Expr::Con(ctor, _) => self
                .answer(self.barb.ctor(ctor).owner)
                .map(|_| self.width(expr)),
            barb::Expr::Call(function, _) => self
                .answer(self.barb.function(function).result)
                .map(|_| self.width(expr)),
            barb::Expr::Match(_, arms) => self
                .reachable(arms, self.facts.matched(expr))
                .iter()
                .map(|arm| {
                    let mut inner = carried.to_vec();
                    inner.extend(
                        self.barb
                            .fields(arm.ctor)
                            .iter()
                            .map(|ty| self.carries[ty.index()].is_some()),
                    );
                    self.body_answer(arm.body, inner)
                })
                .fold(Answer::Never, widest),
            barb::Expr::Atom(atom) => {
                if carried[atom.0.index()] {
                    Answer::Value(self.width(expr))
                } else {
                    Answer::Nothing
                }
            }
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
