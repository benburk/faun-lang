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
    /// A call of a definition recognised as a bitwise walk: see
    /// [`accumulator`].
    Walk(Operation, Vec<Self>),
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
    // Bitwise walks, which take four arguments and are no operation of
    // their own: only a call of one handed a place of one and nothing
    // built is.
    let mut walks = vec![None; found.len()];
    // Dependencies (mul on add, div on mod and equality) can be declared in
    // any order. Every successful round adds at least one fact.
    loop {
        let mut changed = false;
        for at in 0..found.len() {
            let id = FnId::at(at);
            if walks[at].is_none() {
                walks[at] = accumulator(program, id, &found)
                    .or_else(|| exponentiation(program, id, &found));
                changed |= walks[at].is_some();
            }
            if found[at].is_none() {
                let op = recognise_one(program, id, &found)
                    .or_else(|| started(program, id, &found, &walks))
                    .or_else(|| recognise_columns(program, id, &found));
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

/// A walk started from its identity: a place of one and nothing built for
/// a bitwise one, and one built for a power.
fn started(
    program: &Program,
    id: FnId,
    facts: &[Option<Operation>],
    walks: &[Option<Operation>],
) -> Option<Operation> {
    let normal = walk(program, id, facts, 2)?.walking(walks);
    let (a, b) = (Term::Variable(0), Term::Variable(1));
    let Term::Walk(op, args) = normal.run(vec![a.clone(), b.clone()])? else {
        return None;
    };
    let one = Term::Number(BigUint::one());
    let start = if op == Operation::Pow {
        vec![one]
    } else {
        vec![one, zero()]
    };
    (args[..2] == [a, b] && args[2..] == start).then_some(op)
}

/// How a walk of `arity` numbers, answering one, is normalized.
fn walk<'a>(
    program: &'a Program,
    id: FnId,
    facts: &'a [Option<Operation>],
    arity: usize,
) -> Option<Normal<'a>> {
    let params = program.params(id);
    let [ty, ..] = params else {
        return None;
    };
    if params.len() != arity
        || params.iter().any(|param| param != ty)
        || program.function(id).result != *ty
    {
        return None;
    }
    Normal::new(program, id, facts, *ty)
}

/// A bitwise walk: `f(a, b, place, built)` is `built + place * (a op b)`
/// for `op` an and, an or or an exclusive or, taking a bit of each at a
/// time from the bottom:
///
/// ```text
/// f(0, b, place, built)     = built + place * (0 op b)
/// f(a, 0, place, built)     = built + place * (a op 0)
/// f(a, b, place, built)     = f(a / 2, b / 2, place * 2, built + place * bit)
/// ```
///
/// where `bit` reads only `a % 2` and `b % 2`, and is their `op` for each
/// of the four ways they can be. Halving `a` each step is what makes the
/// last line an induction, so these equations are the operation: nothing
/// here is sampled.
fn accumulator(program: &Program, id: FnId, facts: &[Option<Operation>]) -> Option<Operation> {
    let normal = walk(program, id, facts, 4)?;
    let [a, b, place, built] = [0, 1, 2, 3].map(Term::Variable);
    let from_nought =
        canonical(normal.run(vec![zero(), b.clone(), place.clone(), built.clone()])?);
    let to_nought =
        canonical(normal.run(vec![succ(a.clone()), zero(), place.clone(), built.clone()])?);
    let bit = halving(&normal)?;
    let two = Term::Number(BigUint::from(2u8));
    let low = |x: &Term| canonical(known(Operation::Mod, succ(x.clone()), two.clone()));
    let (low_a, low_b) = (low(&a), low(&b));
    let table = BITS.map(|(x, y)| simplify(replace(&bit, &[(&low_a, x), (&low_b, y)])));
    let product = |x: &Term| canonical(known(Operation::Mul, x.clone(), place.clone()));
    let sum_with = |x: Term| canonical(known(Operation::Add, built.clone(), x));
    [Operation::And, Operation::Or, Operation::Xor]
        .into_iter()
        .find(|&op| {
            let (from, to) = if op == Operation::And {
                (built.clone(), built.clone())
            } else {
                (sum_with(product(&b)), sum_with(product(&succ(a.clone()))))
            };
            let answers = BITS.map(|(x, y)| {
                let set = op.calculate(&BigUint::from(x), &BigUint::from(y));
                if set.is_some_and(|n| !n.is_zero()) {
                    place.clone()
                } else {
                    zero()
                }
            });
            from_nought == from && to_nought == to && table == answers
        })
}

/// The four ways two bits can be.
const BITS: [(u8, u8); 4] = [(0, 0), (0, 1), (1, 0), (1, 1)];

/// What a bitwise walk adds for a step of two numbers above nought, which
/// must halve both, double the place, and add to what was built, with each
/// remainder taken apart over sums and products so it reads bits.
fn halving(normal: &Normal<'_>) -> Option<Term> {
    let [a, b, place, built] = [0, 1, 2, 3].map(Term::Variable);
    let two = Term::Number(BigUint::from(2u8));
    let Term::Recursive(step) = normal.run(vec![
        succ(a.clone()),
        succ(b.clone()),
        place.clone(),
        built.clone(),
    ])?
    else {
        return None;
    };
    let [halved_a, halved_b, doubled, sum] = <[Term; 4]>::try_from(step).ok()?.map(canonical);
    let halves = |x: &Term| canonical(known(Operation::Div, succ(x.clone()), two.clone()));
    let twice = [
        canonical(known(Operation::Mul, place.clone(), two.clone())),
        canonical(known(Operation::Add, place.clone(), place)),
    ];
    if halved_a != halves(&a) || halved_b != halves(&b) || !twice.contains(&doubled) {
        return None;
    }
    let Term::Known(Operation::Add, sum) = sum else {
        return None;
    };
    match sum.as_slice() {
        [x, bit] | [bit, x] if *x == built => Some(distribute(bit.clone())),
        _ => None,
    }
}

/// A power by squaring: `f(base, exponent, built)` is
/// `built * base ^ exponent`, a bit of the exponent at a time:
///
/// ```text
/// f(base, 0, built) = built
/// f(base, 1, built) = built * base
/// f(base, e, built) = f(base * base, e / 2, e % 2 == 1 ? built * base : built)
/// ```
///
/// where the last may also answer for one. As for [`accumulator`], halving
/// the exponent makes these an induction on it, and the choice reads only
/// `e % 2`, so it is checked for both of the two ways it can be.
fn exponentiation(program: &Program, id: FnId, facts: &[Option<Operation>]) -> Option<Operation> {
    let normal = walk(program, id, facts, 3)?;
    let [base, exponent, built] = [0, 1, 2].map(Term::Variable);
    let two = Term::Number(BigUint::from(2u8));
    let one = Term::Number(BigUint::one());
    let times = |x: &Term| canonical(known(Operation::Mul, x.clone(), base.clone()));
    if canonical(normal.run(vec![base.clone(), zero(), built.clone()])?) != built {
        return None;
    }
    let squared = times(&base);
    // A step of the exponent `e`, with `e % 2` as each of its two ways.
    let stepped = |e: Term, odd: &[u8]| {
        let Some(Term::Recursive(step)) = normal.run(vec![base.clone(), e.clone(), built.clone()])
        else {
            return false;
        };
        let Ok([next_base, next_exponent, kept]) = <[Term; 3]>::try_from(step) else {
            return false;
        };
        let low = canonical(known(Operation::Mod, e.clone(), two.clone()));
        canonical(next_base) == squared
            && canonical(next_exponent) == canonical(known(Operation::Div, e, two.clone()))
            && odd.iter().all(|&bit| {
                let chosen = simplify(replace(&distribute(kept.clone()), &[(&low, bit)]));
                canonical(chosen)
                    == if bit == 1 {
                        times(&built)
                    } else {
                        built.clone()
                    }
            })
    };
    let at_one = canonical(normal.run(vec![base.clone(), one.clone(), built.clone()])?);
    if at_one != times(&built) && !stepped(one, &[1]) {
        return None;
    }
    stepped(succ(succ(exponent)), &[0, 1]).then_some(Operation::Pow)
}

/// A term with the operands of each commutative operation in one order,
/// so two spellings of one sum compare equal.
fn canonical(term: Term) -> Term {
    match term {
        Term::Known(op, args) => {
            let mut args: Vec<_> = args.into_iter().map(canonical).collect();
            if matches!(
                op,
                Operation::Add | Operation::Mul | Operation::And | Operation::Or | Operation::Xor
            ) {
                args.sort_by_cached_key(|arg| format!("{arg:?}"));
            }
            Term::Known(op, args)
        }
        Term::Succ(n) => succ(canonical(*n)),
        Term::Constructor(ctor, fields) => {
            Term::Constructor(ctor, fields.into_iter().map(canonical).collect())
        }
        Term::Recursive(args) => Term::Recursive(args.into_iter().map(canonical).collect()),
        Term::Walk(op, args) => Term::Walk(op, args.into_iter().map(canonical).collect()),
        Term::Match(value, arms) => Term::Match(
            Box::new(canonical(*value)),
            arms.into_iter()
                .map(|(ctor, arm)| (ctor, canonical(arm)))
                .collect(),
        ),
        term @ (Term::Variable(_) | Term::Number(_)) => term,
    }
}

/// `term` with each remainder of a sum or product by a number known
/// outright taken of the operands too, which is the same number:
/// `(u + v) % m` is `(u % m + v % m) % m`. So a bit read off a sum reads
/// the bits it is a sum of.
fn distribute(term: Term) -> Term {
    let each = |args: Vec<Term>| args.into_iter().map(distribute).collect::<Vec<_>>();
    match term {
        Term::Known(Operation::Mod, args) => {
            let args = each(args);
            if let [
                Term::Known(inner @ (Operation::Add | Operation::Mul), operands),
                m @ Term::Number(_),
            ] = args.as_slice()
            {
                let operands = operands
                    .iter()
                    .map(|operand| known(Operation::Mod, operand.clone(), m.clone()))
                    .collect();
                return known(Operation::Mod, Term::Known(*inner, operands), m.clone());
            }
            Term::Known(Operation::Mod, args)
        }
        Term::Known(op, args) => Term::Known(op, each(args)),
        Term::Succ(n) => succ(distribute(*n)),
        Term::Constructor(ctor, fields) => Term::Constructor(ctor, each(fields)),
        Term::Recursive(args) => Term::Recursive(each(args)),
        Term::Walk(op, args) => Term::Walk(op, each(args)),
        Term::Match(value, arms) => Term::Match(
            Box::new(distribute(*value)),
            arms.into_iter()
                .map(|(ctor, arm)| (ctor, distribute(arm)))
                .collect(),
        ),
        term @ (Term::Variable(_) | Term::Number(_)) => term,
    }
}

/// `term` with each of `by`'s terms, compared canonically, a number.
fn replace(term: &Term, by: &[(&Term, u8)]) -> Term {
    let canon = canonical(term.clone());
    if let Some((_, n)) = by.iter().find(|(from, _)| **from == canon) {
        return Term::Number(BigUint::from(*n));
    }
    let each = |args: &[Term]| args.iter().map(|arg| replace(arg, by)).collect();
    match term {
        Term::Known(op, args) => Term::Known(*op, each(args)),
        Term::Succ(n) => succ(replace(n, by)),
        Term::Constructor(ctor, fields) => Term::Constructor(*ctor, each(fields)),
        Term::Recursive(args) => Term::Recursive(each(args)),
        Term::Walk(op, args) => Term::Walk(*op, each(args)),
        Term::Match(value, arms) => Term::Match(
            Box::new(replace(value, by)),
            arms.iter()
                .map(|(ctor, arm)| (*ctor, replace(arm, by)))
                .collect(),
        ),
        Term::Variable(_) | Term::Number(_) => term.clone(),
    }
}

/// Work out what numbers known outright say: each operation of two of
/// them, a product by nought or one, a sum with nought, and the arm of a
/// match a known tag selects.
fn simplify(term: Term) -> Term {
    match term {
        Term::Known(op, args) => simplify_known(op, args.into_iter().map(simplify).collect()),
        Term::Succ(n) => succ(simplify(*n)),
        Term::Match(value, arms) => {
            let value = simplify(*value);
            if let Term::Constructor(ctor, fields) = &value
                && fields.is_empty()
                && let Some((_, arm)) = arms.iter().find(|(arm, _)| arm == ctor)
            {
                return simplify(arm.clone());
            }
            Term::Match(
                Box::new(value),
                arms.into_iter()
                    .map(|(ctor, arm)| (ctor, simplify(arm)))
                    .collect(),
            )
        }
        term => term,
    }
}

/// An operation on operands already simplified.
fn simplify_known(op: Operation, args: Vec<Term>) -> Term {
    let number = |term: &Term| match term {
        Term::Number(n) => Some(n.clone()),
        _ => None,
    };
    if let [x, y] = args.as_slice() {
        if let (Some(x), Some(y)) = (number(x), number(y)) {
            if let Some(n) = op.calculate(&x, &y) {
                return Term::Number(n);
            }
            if let Some(ctor) = op.compare(&x, &y) {
                return tag(ctor);
            }
        }
        let is = |term: &Term, n: u8| number(term) == Some(BigUint::from(n));
        match op {
            Operation::Mul if is(x, 0) || is(y, 0) => return zero(),
            Operation::Mul if is(x, 1) => return y.clone(),
            Operation::Add if is(x, 0) => return y.clone(),
            Operation::Mul if is(y, 1) => return x.clone(),
            Operation::Add if is(y, 0) => return x.clone(),
            _ => {}
        }
    }
    Term::Known(op, args)
}

/// Which definitions answer a question about a sequence, given which are
/// already recognised arithmetic.
pub(super) fn recognise_sequences(
    program: &Program,
    facts: &[Option<Operation>],
) -> Vec<Option<SequenceOperation>> {
    let counts: Vec<_> = (0..program.functions().len())
        .map(|at| length(program, FnId::at(at), facts))
        .collect();
    super::sequence::recognise(program, &counts)
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
    /// Which definitions are bitwise walks, whose calls are left as terms.
    walks: &'a [Option<Operation>],
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
            walks: &[],
            nil,
            cons,
        })
    }

    const fn walking(self, walks: &'a [Option<Operation>]) -> Self {
        Self { walks, ..self }
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
                if let Some(Some(op)) = self.walks.get(called.index()) {
                    return Some(Term::Walk(*op, fields));
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
