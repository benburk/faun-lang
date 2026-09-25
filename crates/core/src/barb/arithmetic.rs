//! Structural arithmetic recognition, and the count of a sequence. Names are
//! never consulted.
//!
//! Each check is an induction equation: evaluate the nonrecursive part of
//! a definition on zero/successor cases, leaving recursive calls opaque,
//! then compare with the equation for the operation. A near miss does not
//! become an instruction. Let aliases and nonrecursive helpers disappear
//! in this bounded normalization; an opaque/bodyless call makes it fail.

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::constant::{ConstantView, Shape};
use super::shape;
use super::{
    Body, CtorId, Expr, FnId, Operation, Program, SequenceOperation, TypeId, TypeShape, type_shape,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Variable(u8),
    Number(BigUint),
    Succ(Box<Self>),
    Constructor(CtorId, Vec<Self>),
    Recursive(Vec<Self>),
    Known(Operation, Vec<Self>),
    Match(Box<Self>, Vec<(CtorId, Self)>),
}

fn zero() -> Term {
    Term::Number(BigUint::zero())
}
fn succ(value: Term) -> Term {
    match value {
        Term::Number(n) => Term::Number(n + BigUint::one()),
        value => Term::Succ(Box::new(value)),
    }
}
fn recur(a: Term, b: Term) -> Term {
    Term::Recursive(vec![a, b])
}
fn known(op: Operation, a: Term, b: Term) -> Term {
    Term::Known(op, vec![a, b])
}
const fn tag(ctor: CtorId) -> Term {
    Term::Constructor(ctor, vec![])
}

pub(super) fn natural(program: &Program, ty: TypeId) -> Option<(CtorId, CtorId)> {
    let Shape::Spine { nil, cons, .. } = shape(program, ty) else {
        return None;
    };
    (program.fields(cons).len() == 1).then_some((nil, cons))
}

pub(super) fn recognise(program: &Program) -> Vec<Option<Operation>> {
    let mut found = vec![None; program.functions().len()];
    // Dependencies (mul on add, div on mod and equality) can be declared in
    // any order. Every successful round adds at least one fact.
    loop {
        let mut changed = false;
        for at in 0..found.len() {
            if found[at].is_none() {
                let op = recognise_one(program, FnId::at(at), &found)
                    .or_else(|| recognise_columns(program, FnId::at(at), &found));
                changed |= op.is_some();
                found[at] = op;
            }
        }
        if !changed {
            return found;
        }
    }
}

fn recognise_one(program: &Program, id: FnId, facts: &[Option<Operation>]) -> Option<Operation> {
    let [a, b] = program.params(id) else {
        return None;
    };
    if a != b {
        return None;
    }
    let normal = Normal::new(program, id, facts, *a)?;
    let result = program.function(id).result;
    if result != *a {
        return comparison(&normal, result);
    }
    let (a, b) = (Term::Variable(0), Term::Variable(1));
    for counted in [0, 1] {
        let args = |step| {
            if counted == 0 {
                vec![step, b.clone()]
            } else {
                vec![b.clone(), step]
            }
        };
        let (Some(base), Some(step)) =
            (normal.run(args(zero())), normal.run(args(succ(a.clone()))))
        else {
            continue;
        };
        if base == b && step == succ(Term::Recursive(args(a.clone()))) {
            return Some(Operation::Add);
        }
        let rest = Term::Recursive(args(a.clone()));
        if base == zero()
            && [
                known(Operation::Add, b.clone(), rest.clone()),
                known(Operation::Add, rest, b.clone()),
            ]
            .contains(&step)
        {
            return Some(Operation::Mul);
        }
    }
    None
}

/// Which definitions answer a question about a sequence, given which are
/// already recognised arithmetic.
pub(super) fn recognise_sequences(
    program: &Program,
    facts: &[Option<Operation>],
) -> Vec<Option<SequenceOperation>> {
    (0..program.functions().len())
        .map(|at| length(program, FnId::at(at), facts).then_some(SequenceOperation::Length))
        .collect()
}

/// A count of a sequence: nought for the empty one, and one more than the
/// count of the rest for a step. The element is a variable the answer must
/// not mention, so a definition reading it counts something else.
fn length(program: &Program, id: FnId, facts: &[Option<Operation>]) -> bool {
    let [sequence] = program.params(id) else {
        return false;
    };
    let TypeShape::Sequence {
        empty,
        push,
        recursive,
        ..
    } = type_shape(program, *sequence)
    else {
        return false;
    };
    let Some(normal) = Normal::new(program, id, facts, program.function(id).result) else {
        return false;
    };
    let (element, rest) = (Term::Variable(1), Term::Variable(0));
    let mut fields = vec![element.clone(), element];
    fields[recursive] = rest.clone();
    let counted = Term::Recursive(vec![rest]);
    let one = Term::Number(BigUint::one());
    let counts = [
        succ(counted.clone()),
        known(Operation::Add, one.clone(), counted.clone()),
        known(Operation::Add, counted, one),
    ];
    normal.run(vec![Term::Constructor(empty, vec![])]) == Some(zero())
        && normal
            .run(vec![Term::Constructor(push, fields)])
            .is_some_and(|step| counts.contains(&step))
}

// The checks needing two constructor columns are separate: failing to
// normalize a single-column equation is not evidence against these.
pub(super) fn recognise_columns(
    program: &Program,
    id: FnId,
    facts: &[Option<Operation>],
) -> Option<Operation> {
    let [a, b] = program.params(id) else {
        return None;
    };
    if a != b || program.function(id).result != *a {
        return None;
    }
    let normal = Normal::new(program, id, facts, *a)?;
    let (a, b) = (Term::Variable(0), Term::Variable(1));
    let at = |x, y| normal.run(vec![x, y]);
    if at(zero(), b.clone()) == Some(zero())
        && at(succ(a.clone()), zero()) == Some(succ(a.clone()))
        && at(succ(a.clone()), succ(b.clone())) == Some(recur(a, b))
    {
        return Some(Operation::Monus);
    }
    division(&normal)
}

fn division(normal: &Normal<'_>) -> Option<Operation> {
    let (a, b) = (Term::Variable(0), Term::Variable(1));
    let at = |x, y| normal.run(vec![x, y]);
    if at(zero(), zero()) != Some(zero()) || at(zero(), succ(b.clone())) != Some(zero()) {
        return None;
    }
    let base = at(succ(a.clone()), zero())?;
    let step = at(succ(a.clone()), succ(b.clone()))?;
    for equality in normal.facts.iter().flatten().copied() {
        let Operation::Equals { yes, no } = equality else {
            continue;
        };
        let rest = recur(a.clone(), succ(b.clone()));
        let select = |test, yes_value, no_value| {
            let mut arms = vec![(yes, yes_value), (no, no_value)];
            arms.sort_by_key(|(ctor, _)| ctor.index());
            Term::Match(Box::new(test), arms)
        };
        let test = known(equality, rest.clone(), b.clone());
        if base == succ(a.clone()) && step == select(test, zero(), succ(rest.clone())) {
            return Some(Operation::Mod);
        }
        let remainder = known(Operation::Mod, a.clone(), succ(b.clone()));
        let test = known(equality, remainder, b.clone());
        if base == zero() && step == select(test, succ(rest.clone()), rest) {
            return Some(Operation::Div);
        }
    }
    None
}

fn comparison(normal: &Normal<'_>, result: TypeId) -> Option<Operation> {
    let ctors = normal.program.ctors(result);
    if ctors.len() != 2
        || ctors
            .iter()
            .any(|c| !normal.program.types_of(c.fields).is_empty())
    {
        return None;
    }
    let (a, b) = (Term::Variable(0), Term::Variable(1));
    let zz = normal.run(vec![zero(), zero()])?;
    let zs = normal.run(vec![zero(), succ(b.clone())])?;
    let sz = normal.run(vec![succ(a.clone()), zero()])?;
    let ss = normal.run(vec![succ(a.clone()), succ(b.clone())])?;
    if ss != recur(a, b) {
        return None;
    }
    for yes_tag in 0..2 {
        let yes = normal.program.ctor_at(result, yes_tag);
        let no = normal.program.ctor_at(result, 1 - yes_tag);
        if zz == tag(yes) && zs == tag(no) && sz == tag(no) {
            return Some(Operation::Equals { yes, no });
        }
        if zz == tag(no) && zs == tag(yes) && sz == tag(no) {
            return Some(Operation::LessThan { yes, no });
        }
    }
    None
}

struct Normal<'a> {
    program: &'a Program,
    id: FnId,
    facts: &'a [Option<Operation>],
    nil: CtorId,
    cons: CtorId,
}
impl<'a> Normal<'a> {
    fn new(
        program: &'a Program,
        id: FnId,
        facts: &'a [Option<Operation>],
        ty: TypeId,
    ) -> Option<Self> {
        let (nil, cons) = natural(program, ty)?;
        Some(Self {
            program,
            id,
            facts,
            nil,
            cons,
        })
    }

    fn run(&self, args: Vec<Term>) -> Option<Term> {
        self.body(self.program.function(self.id).body()?, args, &mut 256)
    }
    fn body(&self, body: Body, mut locals: Vec<Term>, fuel: &mut u32) -> Option<Term> {
        for &binding in self.program.bindings(body.bindings) {
            locals.push(self.expr(binding, &locals, fuel)?);
        }
        self.expr(body.tail, &locals, fuel)
    }
    fn expr(&self, id: super::ExprId, locals: &[Term], fuel: &mut u32) -> Option<Term> {
        *fuel = fuel.checked_sub(1)?;
        let args = |range| {
            self.program
                .atoms(range)
                .iter()
                .map(|a| locals[a.0.index()].clone())
                .collect::<Vec<_>>()
        };
        match self.program.expr(id) {
            Expr::Atom(a) => Some(locals[a.0.index()].clone()),
            Expr::Static(value) => self.constant(value),
            Expr::Con(ctor, fields) => {
                let mut fields = args(fields);
                Some(if ctor == self.nil {
                    zero()
                } else if ctor == self.cons {
                    succ(fields.remove(0))
                } else {
                    Term::Constructor(ctor, fields)
                })
            }
            Expr::Call(called, fields) => {
                let fields = args(fields);
                if called == self.id {
                    return Some(Term::Recursive(fields));
                }
                if let Some(op) = self.facts[called.index()] {
                    return Some(Term::Known(op, fields));
                }
                self.body(self.program.function(called).body()?, fields, fuel)
            }
            Expr::Match(value, arms) => self.branch(&locals[value.0.index()], arms, locals, fuel),
        }
    }

    fn constant(&self, value: super::ConstId) -> Option<Term> {
        let value = self.program.constant(value);
        match value.view() {
            ConstantView::Natural(n) => Some(Term::Number(n.to_biguint())),
            ConstantView::Constructor(ctor)
                if self
                    .program
                    .ctors(value.owner())
                    .iter()
                    .all(|ctor| self.program.types_of(ctor.fields).is_empty()) =>
            {
                Some(tag(ctor.constructor()))
            }
            ConstantView::Constructor(_) | ConstantView::Spine(_) => None,
        }
    }

    fn branch(
        &self,
        value: &Term,
        arms: super::Range,
        locals: &[Term],
        fuel: &mut u32,
    ) -> Option<Term> {
        let parts = match value {
            Term::Number(n) if n.is_zero() => Some((self.nil, vec![])),
            Term::Number(n) => Some((self.cons, vec![Term::Number(n - BigUint::one())])),
            Term::Succ(n) => Some((self.cons, vec![*n.clone()])),
            Term::Constructor(ctor, fields) => Some((*ctor, fields.clone())),
            _ => None,
        };
        if let Some((ctor, fields)) = parts {
            let arm = self
                .program
                .arms(arms)
                .iter()
                .find(|arm| arm.ctor == ctor)?;
            let mut inner = locals.to_vec();
            inner.extend(fields);
            return self.body(arm.body, inner, fuel);
        }
        // Only an enum can be normalized without knowing its value;
        // fields of an unknown inductive value have no substitution.
        let mut choices = Vec::new();
        for arm in self.program.arms(arms) {
            if !self.program.fields(arm.ctor).is_empty() {
                return None;
            }
            choices.push((arm.ctor, self.body(arm.body, locals.to_vec(), fuel)?));
        }
        Some(Term::Match(Box::new(value.clone()), choices))
    }
}
