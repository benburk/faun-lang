//! Definitions answering a question about a sequence, or building one from
//! others, recognized by the equations they are written as. Names are never
//! consulted.
//!
//! A sequence is held as a buffer, and some of what a definition over one
//! computes is something a buffer does in one step: how many elements it
//! holds, or another's elements put before its own. A definition recognized
//! as one keeps its body, as recognized arithmetic does, and a call to it is
//! answered from the representation rather than walked.

use super::{Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, Range, TypeShape};
use super::{SequenceOperation, type_shape};

/// Which definitions are one of the operations recognized here, given which
/// counts of a sequence `length` already found.
pub(super) fn recognise(program: &Program, length: &[bool]) -> Vec<Option<SequenceOperation>> {
    let count = program.functions().len();
    let reversals: Vec<_> = (0..count)
        .map(|at| reverses(program, FnId::at(at)))
        .collect();
    (0..count)
        .map(|at| {
            let id = FnId::at(at);
            if length[at] {
                Some(SequenceOperation::Length)
            } else if reversals[at] {
                Some(SequenceOperation::ReverseOnto)
            } else if prepends(program, id, &reversals) {
                Some(SequenceOperation::Prepend)
            } else if drops(program, id) {
                Some(SequenceOperation::Drop)
            } else if takes(program, id, &reversals) {
                Some(SequenceOperation::Take)
            } else if replaces(program, id) {
                Some(SequenceOperation::Replace)
            } else {
                None
            }
        })
        .collect()
}

/// The empty constructor of a sequence type, its step, and which of the
/// step's two fields is the rest.
fn sequence(program: &Program, ty: super::TypeId) -> Option<(CtorId, CtorId, usize)> {
    match type_shape(program, ty) {
        TypeShape::Sequence {
            empty,
            push,
            recursive,
            ..
        } => Some((empty, push, recursive)),
        _ => None,
    }
}

/// Whether `id` puts its first sequence's elements before its second's,
/// last first:
///
/// ```text
/// r(list, onto) = match list
///   empty => onto
///   push(x, rest) => r(rest, push(x, onto))
/// ```
pub(super) fn reverses(program: &Program, id: FnId) -> bool {
    let params = program.params(id);
    let (Some(body), &[list, onto]) = (program.function(id).body(), params) else {
        return false;
    };
    let Some((empty, push, recursive)) = sequence(program, list) else {
        return false;
    };
    if onto != list || program.function(id).result != list {
        return false;
    }
    let Some((0, arms)) = top_match(program, body) else {
        return false;
    };
    let Some([nil_arm, push_arm]) = split_arms(program, arms, empty, push) else {
        return false;
    };
    if !nil_arm.body.bindings.is_empty()
        || program.expr(nil_arm.body.tail) != Expr::Atom(Atom(Local::at(1)))
    {
        return false;
    }
    let (element, rest) = (2 + (1 - recursive), 2 + recursive);
    let Expr::Call(again, args) = program.expr(push_arm.body.tail) else {
        return false;
    };
    let &[Atom(first), Atom(second)] = program.atoms(args) else {
        return false;
    };
    if again != id || first.index() != rest {
        return false;
    }
    let Some(pushed) = bound(program, push_arm.body, 4, second.index()) else {
        return false;
    };
    let Expr::Con(ctor, fields) = program.expr(pushed) else {
        return false;
    };
    let fields = program.atoms(fields);
    ctor == push && fields[recursive].0.index() == 1 && fields[1 - recursive].0.index() == element
}

/// Whether `id` puts its first sequence's elements before its second's, in
/// order: its first reversed onto nothing, reversed again onto its second.
///
/// ```text
/// p(list, onto) = r(r(list, empty), onto)
/// ```
fn prepends(program: &Program, id: FnId, reversals: &[bool]) -> bool {
    let params = program.params(id);
    let (Some(body), &[list, onto]) = (program.function(id).body(), params) else {
        return false;
    };
    let Some((empty, _, _)) = sequence(program, list) else {
        return false;
    };
    if onto != list || program.function(id).result != list {
        return false;
    }
    let Expr::Call(outer, args) = program.expr(body.tail) else {
        return false;
    };
    let &[Atom(reversed), Atom(second)] = program.atoms(args) else {
        return false;
    };
    let Some(inner) = bound(program, body, 2, reversed.index()) else {
        return false;
    };
    let Expr::Call(inner_callee, inner_args) = program.expr(inner) else {
        return false;
    };
    let &[Atom(first), Atom(nothing)] = program.atoms(inner_args) else {
        return false;
    };
    let is_empty =
        bound(program, body, 2, nothing.index()).is_some_and(|expr| match program.expr(expr) {
            Expr::Con(ctor, _) => ctor == empty,
            Expr::Static(value) => program.constant(value).constructor() == empty,
            Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => false,
        });
    // Nothing but the empty sequence and the first reversal is bound.
    reversals[outer.index()]
        && reversals[inner_callee.index()]
        && first.index() == 0
        && second.index() == 1
        && is_empty
        && program.bindings(body.bindings).len() == 2
}

/// Whether `id` takes a count of elements off the front of a sequence,
/// matching the count first or the sequence first:
///
/// ```text
/// d(list, n) = match n                d(list, n) = match list
///   zero => list                        empty => empty or list
///   step(m) => match list               push(x, rest) => match n
///     empty => empty                      zero => list
///     push(x, rest) => d(rest, m)         step(m) => d(rest, m)
/// ```
#[expect(
    clippy::too_many_lines,
    reason = "each condition of the two drop shapes is one early return, read in order"
)]
fn drops(program: &Program, id: FnId) -> bool {
    let params = program.params(id);
    let (Some(body), &[list, count]) = (program.function(id).body(), params) else {
        return false;
    };
    let Some((empty, push, recursive)) = sequence(program, list) else {
        return false;
    };
    let TypeShape::Natural {
        empty: zero,
        push: succ,
        ..
    } = type_shape(program, count)
    else {
        return false;
    };
    if program.function(id).result != list {
        return false;
    }
    let Some((on, arms)) = top_match(program, body) else {
        return false;
    };
    let is = |body: Body, local: usize| {
        body.bindings.is_empty() && program.expr(body.tail) == Expr::Atom(Atom(Local::at(local)))
    };
    let is_empty = |body: Body| {
        body.bindings.is_empty()
            && match program.expr(body.tail) {
                Expr::Con(ctor, _) => ctor == empty,
                Expr::Static(value) => program.constant(value).constructor() == empty,
                Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => false,
            }
    };
    // The call going round, on the rest at `rest` and the count less one at
    // `fewer`.
    let again = |body: Body, rest: usize, fewer: usize| {
        let Expr::Call(callee, args) = program.expr(body.tail) else {
            return false;
        };
        body.bindings.is_empty()
            && callee == id
            && program.atoms(args) == [Atom(Local::at(rest)), Atom(Local::at(fewer))]
    };
    let inner = |arm: Arm, on: usize| {
        if !arm.body.bindings.is_empty() {
            return None;
        }
        let Expr::Match(Atom(matched), arms) = program.expr(arm.body.tail) else {
            return None;
        };
        (matched.index() == on).then_some(arms)
    };
    match on {
        1 => {
            let Some([done, step]) = split_arms(program, arms, zero, succ) else {
                return false;
            };
            // The step binds the count less one at 2, and a push its fields
            // at 3 and 4.
            let Some(arms) = inner(step, 0) else {
                return false;
            };
            let Some([nil, cons]) = split_arms(program, arms, empty, push) else {
                return false;
            };
            is(done.body, 0) && is_empty(nil.body) && again(cons.body, 3 + recursive, 2)
        }
        0 => {
            let Some([nil, cons]) = split_arms(program, arms, empty, push) else {
                return false;
            };
            let Some(arms) = inner(cons, 1) else {
                return false;
            };
            let Some([done, step]) = split_arms(program, arms, zero, succ) else {
                return false;
            };
            (is(nil.body, 0) || is_empty(nil.body))
                && is(done.body, 0)
                && again(step.body, 2 + recursive, 4)
        }
        _ => false,
    }
}

/// Whether `id` walks a count of a sequence's first elements onto nothing,
/// which is those elements: see [`taken_onto`].
///
/// ```text
/// t(list, n) = w(list, n, empty)
/// ```
fn takes(program: &Program, id: FnId, reversals: &[bool]) -> bool {
    let (Some(body), &[list, count]) = (program.function(id).body(), program.params(id)) else {
        return false;
    };
    let Some((empty, _, _)) = sequence(program, list) else {
        return false;
    };
    let Expr::Call(walk, args) = program.expr(body.tail) else {
        return false;
    };
    program.function(id).result == list
        && matches!(program.atoms(args), &[Atom(a), Atom(b), Atom(c)]
            if a.index() == 0 && b.index() == 1 && c.index() == 2)
        && program.bindings(body.bindings).len() == 1
        && bound(program, body, 2, 2).is_some_and(|expr| is_empty(program, expr, empty))
        && program.params(walk) == [list, count, list]
        && taken_onto(program, walk, reversals)
}

/// Whether `id` pushes a sequence's first elements onto another while a
/// count lasts, and answers that one reversed onto nothing when either runs
/// out: the elements it took, last first, after those it was handed.
///
/// ```text
/// w(list, n, built) = match list
///   empty => r(built, empty)
///   push(x, rest) => match n
///     zero => r(built, empty)
///     step(m) => w(rest, m, push(x, built))
/// ```
#[expect(
    clippy::too_many_lines,
    reason = "each condition of the walk's shape is one early return, read in order"
)]
fn taken_onto(program: &Program, id: FnId, reversals: &[bool]) -> bool {
    let Some(body) = program.function(id).body() else {
        return false;
    };
    let (list, count) = (program.params(id)[0], program.params(id)[1]);
    let (
        Some((empty, push, recursive)),
        TypeShape::Natural {
            empty: zero,
            push: succ,
            ..
        },
    ) = (sequence(program, list), type_shape(program, count))
    else {
        return false;
    };
    let Some((0, arms)) = top_match(program, body) else {
        return false;
    };
    let Some([nil, cons]) = split_arms(program, arms, empty, push) else {
        return false;
    };
    // The answer reversed onto nothing, where the body's first binding
    // takes level `base`.
    let finished = |body: Body, base: usize| {
        let Expr::Call(reversal, args) = program.expr(body.tail) else {
            return false;
        };
        reversals[reversal.index()]
            && program.bindings(body.bindings).len() == 1
            && bound(program, body, base, base).is_some_and(|expr| is_empty(program, expr, empty))
            && program.atoms(args) == [Atom(Local::at(2)), Atom(Local::at(base))]
    };
    // The push binds its fields at 3 and 4, and the step the count less
    // one at 5.
    let (head, rest) = (3 + (1 - recursive), 3 + recursive);
    let Expr::Match(Atom(matched), arms) = program.expr(cons.body.tail) else {
        return false;
    };
    let Some([done, step]) = split_arms(program, arms, zero, succ) else {
        return false;
    };
    // The step's one binding, at 6, is the element pushed onto what was
    // taken so far.
    let pushed = match program.bindings(step.body.bindings) {
        &[pushed] => match program.expr(pushed) {
            Expr::Con(ctor, fields) => {
                let mut expected = [Atom(Local::at(head)), Atom(Local::at(2))];
                if recursive == 0 {
                    expected.reverse();
                }
                ctor == push && program.atoms(fields) == expected
            }
            _ => false,
        },
        _ => false,
    };
    let again = matches!(program.expr(step.body.tail), Expr::Call(callee, args)
        if callee == id
            && program.atoms(args)
                == [Atom(Local::at(rest)), Atom(Local::at(5)), Atom(Local::at(6))]);
    cons.body.bindings.is_empty()
        && matched.index() == 1
        && finished(nil.body, 3)
        && finished(done.body, 5)
        && pushed
        && again
}

/// Whether `expr` is the empty sequence, built or known.
fn is_empty(program: &Program, expr: ExprId, empty: CtorId) -> bool {
    match program.expr(expr) {
        Expr::Con(ctor, _) => ctor == empty,
        Expr::Static(value) => program.constant(value).constructor() == empty,
        Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => false,
    }
}

/// Whether `id` replaces the element a count reaches with a value, matching
/// the sequence first:
///
/// ```text
/// s(list, n, x) = match list
///   empty => empty or list
///   push(y, rest) => match n
///     zero => push(x, rest)
///     step(m) => push(y, s(rest, m, x))
/// ```
#[expect(
    clippy::too_many_lines,
    reason = "each condition of the replacement shape is one early return, read in order"
)]
fn replaces(program: &Program, id: FnId) -> bool {
    let params = program.params(id);
    let (Some(body), &[list, count, value]) = (program.function(id).body(), params) else {
        return false;
    };
    let Some((empty, push, recursive)) = sequence(program, list) else {
        return false;
    };
    let TypeShape::Natural {
        empty: zero,
        push: succ,
        ..
    } = type_shape(program, count)
    else {
        return false;
    };
    // The element's type is the one the push's other field holds.
    let element = program.fields(push)[1 - recursive];
    if program.function(id).result != list || value != element {
        return false;
    }
    let Some((0, arms)) = top_match(program, body) else {
        return false;
    };
    let Some([nil, cons]) = split_arms(program, arms, empty, push) else {
        return false;
    };
    let nil_answers = nil.body.bindings.is_empty()
        && match program.expr(nil.body.tail) {
            Expr::Atom(Atom(local)) => local.index() == 0,
            Expr::Con(ctor, _) => ctor == empty,
            Expr::Static(value) => program.constant(value).constructor() == empty,
            Expr::Call(..) | Expr::Match(..) => false,
        };
    // The push binds its fields at 3 and 4, and the step the count less
    // one at 5.
    let (head, rest) = (3 + (1 - recursive), 3 + recursive);
    if !nil_answers || !cons.body.bindings.is_empty() {
        return false;
    }
    let Expr::Match(Atom(matched), arms) = program.expr(cons.body.tail) else {
        return false;
    };
    let Some([done, step]) = split_arms(program, arms, zero, succ) else {
        return false;
    };
    // A push of `first` before `second`, in the push's own field order.
    let pushes = |expr: ExprId, first: usize, second: usize| {
        let Expr::Con(ctor, fields) = program.expr(expr) else {
            return false;
        };
        let mut expected = [Atom(Local::at(first)), Atom(Local::at(second))];
        if recursive == 0 {
            expected.reverse();
        }
        ctor == push && program.atoms(fields) == expected
    };
    let written = done.body.bindings.is_empty() && pushes(done.body.tail, 2, rest);
    // The step's one binding, at 6, is the call going round.
    let again = match program.bindings(step.body.bindings) {
        &[call] => match program.expr(call) {
            Expr::Call(callee, args) => {
                callee == id
                    && program.atoms(args)
                        == [
                            Atom(Local::at(rest)),
                            Atom(Local::at(5)),
                            Atom(Local::at(2)),
                        ]
            }
            _ => false,
        },
        _ => false,
    };
    matched.index() == 1 && written && again && pushes(step.body.tail, head, 6)
}

/// A body that is nothing but a match on a parameter: which one, and its
/// arms.
fn top_match(program: &Program, body: Body) -> Option<(usize, Range)> {
    if !body.bindings.is_empty() {
        return None;
    }
    let Expr::Match(Atom(on), arms) = program.expr(body.tail) else {
        return None;
    };
    Some((on.index(), arms))
}

/// Two arms, the one for `empty` first.
fn split_arms(program: &Program, arms: Range, empty: CtorId, push: CtorId) -> Option<[Arm; 2]> {
    let &[first, second] = program.arms(arms) else {
        return None;
    };
    match (first.ctor, second.ctor) {
        (a, b) if a == empty && b == push => Some([first, second]),
        (a, b) if a == push && b == empty => Some([second, first]),
        _ => None,
    }
}

/// What wrote local `level`, where it is a binding of `body`, whose first
/// binding takes level `base`.
fn bound(program: &Program, body: Body, base: usize, level: usize) -> Option<ExprId> {
    let at = level.checked_sub(base)?;
    program.bindings(body.bindings).get(at).copied()
}
