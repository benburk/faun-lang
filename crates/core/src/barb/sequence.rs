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

/// A sequence's two arms, the empty one first.
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
