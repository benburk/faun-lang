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

use super::model::{Binary, Class, FunctionId, Relation, ValueId};
use super::program::Program;
use super::validate::validate;
use crate::platform::{Routine, Routines, reads};

#[cfg(test)]
mod tests;

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
    let (mut machine, main) = Program::new(program.name(program.function(entry).name));
    let callees = declare(&demand, routines, &mut machine, (entry, main))?;

    let lowering = Lowering {
        barb: program,
        facts,
        carries: demand.carries,
        callees,
    };
    for (at, callee) in lowering.callees.iter().enumerate() {
        let id = barb::FnId::at(at);
        if matches!(callee, Callee::Function(_)) && program.function(id).body().is_some() {
            lowering.function(&mut machine, id)?;
        }
    }
    validate(&machine)?;
    Ok(machine)
}

/// One entry per source function; no fabricated IDs for non-functions.
#[derive(Clone, Copy)]
enum Callee<'a> {
    Unreachable,
    Instruction(barb::Operation),
    Function(FunctionId),
    External {
        id: FunctionId,
        routine: &'a Routine,
    },
}

#[expect(
    clippy::too_many_lines,
    reason = "one dispatch over demanded declarations and their contracts"
)]
fn declare<'a>(
    demand: &Demand<'_>,
    routines: &'a Routines,
    machine: &mut Program,
    (entry, main): (barb::FnId, FunctionId),
) -> Result<Vec<Callee<'a>>, String> {
    let (program, facts) = (demand.program, demand.facts);
    let mut callees = Vec::with_capacity(program.functions().len());
    for (at, reached) in demand.reached.iter().enumerate() {
        let id = barb::FnId::at(at);
        if id == entry {
            callees.push(Callee::Function(main));
            continue;
        }
        // A definition the tier below has an instruction for is never
        // emitted: its callers write the instruction instead. Neither is one
        // nothing reaches, which has no callers to write anything.
        if !reached {
            callees.push(Callee::Unreachable);
            continue;
        }
        if let Some(operation) = facts.operation(id) {
            callees.push(Callee::Instruction(operation));
            continue;
        }
        let function = program.function(id);
        let (params, returns) = demand.signature(id);
        let name = program.name(function.name);
        // External functions carry the provider's machine contract. They
        // share function IDs and calls with bodies, not the narrowing policy.
        callees.push(match function.definition {
            barb::Definition::Body(_) => {
                Callee::Function(if uninhabited(program, function.result) {
                    machine.declare_never(name, &params)
                } else {
                    machine.declare(name, &params, &returns)
                })
            }
            barb::Definition::External { symbol, .. } => {
                // A provider may answer for several source declarations.
                let outside = program.name(symbol);
                let wanted = provided(routines, name, outside, &params, &returns)?;
                if wanted.comes_back() == uninhabited(program, function.result) {
                    return Err(format!(
                        "`{outside}` disagrees with `{name}` about returning"
                    ));
                }
                Callee::External {
                    id: wanted.declare(machine),
                    routine: wanted,
                }
            }
        });
    }
    Ok(callees)
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
) -> Result<&'a Routine, String> {
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
    if returns.len() != wanted.answers().iter().len() {
        return Err(format!(
            "`{held}` answers {}, and what is taken back is {}",
            reads(wanted.answers().as_slice()),
            reads(returns),
        ));
    }
    Ok(wanted)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Storage {
    Undemanded,
    Erased,
    Carried,
}

impl Storage {
    fn carried(self) -> bool {
        match self {
            Self::Carried => true,
            Self::Erased => false,
            Self::Undemanded => panic!("a lowered type must have been demanded"),
        }
    }
}

/// Function and representation demand follow the same paths as emission:
/// recognized definitions become instructions, impossible arms disappear,
/// and a body stops at its first binding that cannot return.
struct Demand<'a> {
    program: &'a barb::Program,
    facts: &'a barb::Facts,
    reached: Vec<bool>,
    waiting: Vec<barb::FnId>,
    // Every lowered introduction must demand its type first. Undemanded is
    // distinct from erased, so a missed visit cannot silently discard a value.
    carries: Vec<Storage>,
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
            carries: vec![Storage::Undemanded; program.types().len()],
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
                && let Some(body) = function.body()
            {
                demand.body(body)?;
            }
        }
        Ok(demand)
    }

    /// Erased parameters and results take no machine slot.
    fn signature(&self, id: barb::FnId) -> (Vec<Class>, Vec<Class>) {
        let params = self
            .program
            .params(id)
            .iter()
            .zip(self.facts.takes(id))
            .filter(|(ty, _)| self.carries[ty.index()].carried())
            .map(|(_, held)| width(*held))
            .collect();
        let result = self.program.function(id).result;
        let returns = self.carries[result.index()]
            .carried()
            .then(|| width(self.facts.answers(id)))
            .into_iter()
            .collect();
        (params, returns)
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
            barb::Expr::Static(value) => self.type_(self.program.constant(value).owner())?,
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
fn reachable(
    program: &barb::Program,
    arms: barb::Range,
    bounds: barb::Bounds,
) -> impl Iterator<Item = barb::Arm> + '_ {
    program.arms(arms).iter().copied().filter(move |arm| {
        match barb::shape(program, program.ctor(arm.ctor).owner) {
            barb::Shape::Spine { nil, .. } if arm.ctor == nil => bounds.low == 0,
            barb::Shape::Spine { .. } => bounds.high != Some(0),
            barb::Shape::Tagged => {
                let tag = u64::from(program.tag(arm.ctor));
                tag >= bounds.low && bounds.high.is_none_or(|high| tag <= high)
            }
        }
    })
}

/// The class a type's values take. Numbers and tags are decided so far.
fn represent(program: &barb::Program, id: barb::TypeId) -> Result<Storage, String> {
    let name = program.name(program.type_(id).name);
    if uninhabited(program, id) || erased(program, id) {
        return Ok(Storage::Erased);
    }
    if tagged(program, id) {
        return Ok(Storage::Carried);
    }
    let barb::Shape::Spine { cons, .. } = barb::shape(program, id) else {
        return Err(format!("`{name}` has no representation in this tier yet"));
    };
    if program.fields(cons).len() == 1 {
        // A number takes a place. How wide is not a question about the type
        // -- every `Nat` is the same type and they are not all the same
        // size -- so it is asked of each value, where the tier above
        // answered it.
        return Ok(Storage::Carried);
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
    // Everything worked out above is carried, not just how wide it makes
    // the value: what a value can be is what says whether reading it at
    // another width takes anything off it. The singleton zero needs no
    // value bits and is still a scalar; physical storage and
    // calling-convention slots are target decisions.
    if held.width().is_some() {
        Class::Held(held)
    } else {
        Class::Natural
    }
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

/// A value at the width that reads it, where what reads it was worked
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
fn met(b: &mut super::Builder, arg: ValueId, wanted: Class) -> ValueId {
    if b.class(arg).fits(wanted) {
        arg
    } else {
        b.convert(wanted, arg)
    }
}

/// Where two arms meet: what they leave with is one place, so it is as wide
/// as either of them needs.
fn widest(held: Answer<Class>, other: Answer<Class>) -> Answer<Class> {
    match (held.held(), other.held()) {
        (Some(held), Some(other)) => Answer::Value(super::arithmetic::widest(held, other)),
        _ => held.or(other),
    }
}

/// A tagged arm and the join of this arm with all following arms.
struct TagArm {
    arm: barb::Arm,
    suffix: Answer<Class>,
}

// Analyze each body once, then accumulate joins backward. Returning arms of a
// well-typed match agree on whether they carry a value, so widest is associative
// here. Keep the narrower suffix joins, not just the width of the whole match.
fn tag_plan(
    arms: impl Iterator<Item = barb::Arm>,
    mut answer: impl FnMut(barb::Body) -> Answer<Class>,
) -> Vec<TagArm> {
    let mut planned: Vec<_> = arms
        .map(|arm| TagArm {
            suffix: answer(arm.body),
            arm,
        })
        .collect();
    let mut suffix = Answer::Never;
    for arm in planned.iter_mut().rev() {
        suffix = widest(arm.suffix, suffix);
        arm.suffix = suffix;
    }
    planned
}

/// Leave an arm with what its body answered. An arm that does not come back
/// never reaches the join, so it carries nothing there.
fn yielded(b: &mut super::Builder, answer: Answer<ValueId>, classes: &[Class]) {
    match answer {
        Answer::Value(value) => {
            let value = met(b, value, classes[0]);
            b.yield_(&[value]);
        }
        Answer::Nothing => b.yield_(&[]),
        Answer::Never => (),
    }
}

#[derive(Clone, Copy)]
enum ReturnTo {
    Entry,
    Function(Class),
}

/// The entry's implicit status is a host word, not a request for modulo.
fn returned(
    b: &mut super::Builder,
    answer: Answer<ValueId>,
    destination: ReturnTo,
) -> Result<(), String> {
    let returns = match destination {
        ReturnTo::Entry => Class::Word,
        ReturnTo::Function(class) => class,
    };
    match answer {
        Answer::Value(answer) => {
            if matches!(destination, ReturnTo::Entry) && b.class(answer) == Class::Natural {
                return Err(
                    "the entry's result is unbounded, but its exit status must fit a word"
                        .to_owned(),
                );
            }
            let answer = met(b, answer, returns);
            b.ret(&[answer]);
        }
        Answer::Nothing if matches!(destination, ReturnTo::Entry) => {
            let status = b.constant(Class::Word, 0);
            b.ret(&[status]);
        }
        Answer::Nothing => b.ret(&[]),
        Answer::Never => (),
    }
    Ok(())
}

struct Lowering<'a> {
    barb: &'a barb::Program,
    facts: &'a barb::Facts,
    /// Whether a value of each barb type takes a place, by type.
    carries: Vec<Storage>,
    callees: Vec<Callee<'a>>,
}

impl Lowering<'_> {
    /// The class a term answers at, which is how wide what it answers can
    /// be. Two values of one type may be held differently, since what makes
    /// them wide is what was done with them and not what they are.
    fn width(&self, id: barb::ExprId) -> Class {
        width(self.facts.held(id))
    }

    fn function(&self, machine: &mut Program, id: barb::FnId) -> Result<(), String> {
        let body = self
            .barb
            .function(id)
            .body()
            .expect("a function with a body");
        let Callee::Function(into) = self.callees[id.index()] else {
            unreachable!("only machine functions have bodies to lower");
        };
        let entry = self.barb.entry() == Some(id);
        // What it leaves with: a word from the entry, whatever the program
        // worked in, and otherwise the width it was declared at.
        let destination = if entry {
            ReturnTo::Entry
        } else {
            ReturnTo::Function(width(self.facts.answers(id)))
        };
        machine.try_define(into, |b, params| {
            let mut taken = params.iter().copied();
            // Erased parameters take no machine slot; match the rest in order.
            let mut locals: Vec<Option<ValueId>> = self
                .barb
                .params(id)
                .iter()
                .map(|ty| {
                    self.carries[ty.index()]
                        .carried()
                        .then(|| taken.next().expect("a parameter"))
                })
                .collect();
            let answer = self.body(b, body, &mut locals);
            returned(b, answer, destination)
        })
    }

    /// Each binding takes the next local, then the tail answers.
    fn body(
        &self,
        b: &mut super::Builder,
        body: barb::Body,
        locals: &mut Vec<Option<ValueId>>,
    ) -> Answer<ValueId> {
        for &binding in self.barb.bindings(body.bindings) {
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
            barb::Expr::Static(value) => {
                let value = self.barb.constant(value);
                let id = value.owner();
                if !self.carries[id.index()].carried() {
                    return Answer::Nothing;
                }
                let class = self.width(expr);
                match value.view() {
                    barb::ConstantView::Constructor(ctor) => {
                        let tag = u64::from(self.barb.tag(ctor.constructor()));
                        Answer::Value(b.constant(class, tag))
                    }
                    barb::ConstantView::Natural(number) => match number.try_u64() {
                        Ok(held) => Answer::Value(b.constant(class, held)),
                        Err(barb::TooWide) => Answer::Value(b.natural(&number.to_biguint())),
                    },
                    barb::ConstantView::Spine(_) => {
                        unreachable!("unsupported constants were rejected by demand")
                    }
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
        let mut args: Vec<ValueId> = self
            .barb
            .atoms(args)
            .iter()
            .filter_map(|atom| locals[atom.0.index()])
            .collect();
        let (results, answers) = match self.callees[function.index()] {
            Callee::Instruction(operation) => {
                if matches!(operation, barb::Operation::Add | barb::Operation::Mul)
                    && let Some(affine) = self.facts.affine(expr)
                {
                    return Answer::Value(self.affine(b, expr, affine, locals));
                }
                return Answer::Value(self.operation(b, operation, self.width(expr), &args));
            }
            Callee::External { id, routine } => (b.call(id, &args), routine.answers()),
            Callee::Function(callee) => {
                for (at, arg) in args.iter_mut().enumerate() {
                    let wanted = b.takes(callee)[at];
                    *arg = met(b, *arg, wanted);
                }
                (b.call(callee, &args), None)
            }
            Callee::Unreachable => unreachable!("a lowered call must have been demanded"),
        };
        // A call answers what its result type does, which is nothing ever
        // where that type has no values -- and it answers at the width the
        // name it calls was declared at, which the caller may hold wider.
        self.answer(self.barb.function(function).result).map(|_| {
            let class = self.width(expr);
            let held = *results.first().expect("a result where a type carries one");
            if answers == Some(Class::Word) {
                held
            } else if answers.is_some_and(|answers| !answers.fits(class)) {
                b.convert(class, held)
            } else {
                held
            }
        })
    }

    /// Materialize a target-independent affine summary as machine arithmetic.
    /// Earlier bindings may still have emitted their source operations; the
    /// machine optimizer removes those when this expression bypasses them.
    fn affine(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        affine: &barb::Affine,
        locals: &[Option<ValueId>],
    ) -> ValueId {
        let class = self.width(expr);
        let mut answer = None;
        for &(atom, coefficient) in &affine.terms {
            let value = locals[atom.0.index()].expect("an affine term to carry a value");
            let term = match coefficient {
                1 => value,
                // Preserve the primitive operation already present in x+x.
                // Machine simplification can make fixed-width doubling a
                // shift, while runtime naturals retain their cheaper add.
                2 => super::arithmetic::lower(b, barb::Operation::Add, class, value, value),
                _ => {
                    let coefficient = b.constant(width(barb::Bounds::at(coefficient)), coefficient);
                    super::arithmetic::lower(b, barb::Operation::Mul, class, value, coefficient)
                }
            };
            answer = Some(answer.map_or(term, |held| {
                super::arithmetic::lower(b, barb::Operation::Add, class, held, term)
            }));
        }
        if affine.constant != 0 || answer.is_none() {
            let constant = b.constant(width(barb::Bounds::at(affine.constant)), affine.constant);
            answer = Some(answer.map_or(constant, |held| {
                super::arithmetic::lower(b, barb::Operation::Add, class, held, constant)
            }));
        }
        met(
            b,
            answer.expect("an affine form has a term or constant"),
            class,
        )
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
                let yes = u64::from(self.barb.tag(yes));
                let no = u64::from(self.barb.tag(no));
                let yes_class = width(barb::Bounds::at(yes));
                let no_class = width(barb::Bounds::at(no));
                // Both emitted arms must fit the join, even if range analysis
                // proves only the zero tag reachable. Narrow after the join
                // in that case, rather than truncating the other arm's tag.
                let join = super::arithmetic::widest(
                    class,
                    super::arithmetic::widest(yes_class, no_class),
                );
                let test = super::arithmetic::compare(b, relation, args[0], args[1]);
                let answer = b.if_(
                    test,
                    &[join],
                    |b| {
                        let value = b.constant(yes_class, yes);
                        b.yield_(&[value]);
                    },
                    |b| {
                        let value = b.constant(no_class, no);
                        b.yield_(&[value]);
                    },
                )[0];
                met(b, answer, class)
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
        if !self.carries[owner.index()].carried() {
            return None;
        }
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
        let mut arms = reachable(self.barb, arms, bounds);
        let Some(first) = arms.next() else {
            return Answer::Never;
        };
        let Some(second) = arms.next() else {
            return self.only_arm(b, scrutinee, &first, locals);
        };
        match barb::shape(self.barb, self.barb.ctor(first.ctor).owner) {
            barb::Shape::Spine { nil, .. } => {
                // A spine has exactly these two arms, regardless of their tags.
                let (empty, counted) = if first.ctor == nil {
                    (first, second)
                } else {
                    (second, first)
                };
                self.natural_branch(b, scrutinee, &empty, &counted, locals)
            }
            barb::Shape::Tagged => {
                let arms = {
                    let mut carried = locals.iter().map(Option::is_some).collect();
                    tag_plan([first, second].into_iter().chain(arms), |body| {
                        self.body_answer(body, &mut carried)
                    })
                };
                let class = b.class(scrutinee);
                self.tags(b, scrutinee, class, &arms, locals)
            }
        }
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
        let answer = {
            let mut carried = locals.iter().map(Option::is_some).collect();
            let answer = self.body_answer(empty.body, &mut carried);
            carried.push(true);
            widest(answer, self.body_answer(counted.body, &mut carried))
        };
        let held = answer.held();
        let nought = b.constant(class, 0);
        let is_nought = b.compare(Relation::Equal, scrutinee, nought);
        let results = b.if_(
            is_nought,
            held.as_slice(),
            |b| {
                let mut inner = locals.to_vec();
                let answer = self.body(b, empty.body, &mut inner);
                yielded(b, answer, held.as_slice());
            },
            |b| {
                let mut inner = locals.to_vec();
                let one = b.constant(class, 1);
                inner.push(Some(b.binary(Binary::Sub, scrutinee, one)));
                let answer = self.body(b, counted.body, &mut inner);
                yielded(b, answer, held.as_slice());
            },
        );
        answer.map(|_| *results.first().expect("a result where the arms carry one"))
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
        arms: &[TagArm],
        locals: &[Option<ValueId>],
    ) -> Answer<ValueId> {
        let (
            TagArm {
                arm,
                suffix: answer,
            },
            rest,
        ) = arms.split_first().expect("an arm to match");
        if rest.is_empty() {
            let mut inner = locals.to_vec();
            return self.body(b, arm.body, &mut inner);
        }
        let held = answer.held();
        let tag = b.constant(class, u64::from(self.barb.tag(arm.ctor)));
        let is_this_one = b.compare(Relation::Equal, scrutinee, tag);
        let results = b.if_(
            is_this_one,
            held.as_slice(),
            |b| {
                let mut inner = locals.to_vec();
                let answer = self.body(b, arm.body, &mut inner);
                yielded(b, answer, held.as_slice());
            },
            |b| {
                let answer = self.tags(b, scrutinee, class, rest, locals);
                yielded(b, answer, held.as_slice());
            },
        );
        answer.map(|_| *results.first().expect("a result where the arms carry one"))
    }

    /// What a body answers, read off its shape: an `if` has to be told what
    /// its arms leave with before either of them is lowered.
    ///
    /// Local presence is occurrence-specific, not an `ExprId` cache. Reuse the
    /// scratch stack across siblings, restoring it even when a binding exits.
    fn body_answer(&self, body: barb::Body, carried: &mut Vec<bool>) -> Answer<Class> {
        let base = carried.len();
        let answer = 'body: {
            for &binding in self.barb.bindings(body.bindings) {
                let answer = self.expr_answer(binding, carried);
                if matches!(answer, Answer::Never) {
                    break 'body answer;
                }
                carried.push(answer.held().is_some());
            }
            self.expr_answer(body.tail, carried)
        };
        carried.truncate(base);
        answer
    }

    fn expr_answer(&self, expr: barb::ExprId, carried: &mut Vec<bool>) -> Answer<Class> {
        match self.barb.expr(expr) {
            barb::Expr::Static(value) => self
                .answer(self.barb.constant(value).owner())
                .map(|_| self.width(expr)),
            barb::Expr::Con(ctor, _) => self
                .answer(self.barb.ctor(ctor).owner)
                .map(|_| self.width(expr)),
            barb::Expr::Call(function, _) => self
                .answer(self.barb.function(function).result)
                .map(|_| self.width(expr)),
            barb::Expr::Match(_, arms) => {
                let base = carried.len();
                let mut answer = Answer::Never;
                for arm in reachable(self.barb, arms, self.facts.matched(expr)) {
                    carried.extend(
                        self.barb
                            .fields(arm.ctor)
                            .iter()
                            .map(|ty| self.carries[ty.index()].carried()),
                    );
                    answer = widest(answer, self.body_answer(arm.body, carried));
                    carried.truncate(base);
                }
                answer
            }
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
        self.carries[id.index()]
            .carried()
            .then_some(Class::Word)
            .into()
    }
}
