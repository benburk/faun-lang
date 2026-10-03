//! Reading terms without a scope: every expression a body holds, however
//! deeply its matches nest, and the shapes equations are recognized by.
//!
//! A pass that asks only what is called or which local is read, not what a
//! local holds where it is read, needs no map of locals, and reads a body
//! through these rather than walking its arms by hand.

use super::{Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Program, Range};

/// Every expression in `roots` and in the arms of each match among them,
/// however deep: each before what its arms hold, and in the order written.
pub(super) fn nested(
    program: &Program,
    roots: impl IntoIterator<Item = ExprId>,
) -> impl Iterator<Item = ExprId> {
    let mut waiting: Vec<_> = roots.into_iter().collect();
    waiting.reverse();
    std::iter::from_fn(move || {
        let id = waiting.pop()?;
        if let Expr::Match(_, arms) = program.expr(id) {
            for arm in program.arms(arms).iter().rev() {
                waiting.push(arm.body.tail);
                waiting.extend(program.bindings(arm.body.bindings).iter().rev());
            }
        }
        Some(id)
    })
}

/// Every expression in `body`: see [`nested`].
pub(super) fn within(program: &Program, body: Body) -> impl Iterator<Item = ExprId> {
    let roots = program.bindings(body.bindings).iter().copied();
    nested(program, roots.chain([body.tail]))
}

/// Whether `body` calls `id` anywhere in it.
pub(super) fn calls(program: &Program, body: Body, id: FnId) -> bool {
    within(program, body)
        .any(|expr| matches!(program.expr(expr), Expr::Call(callee, _) if callee == id))
}

/// The locals `id` reads itself, not counting what its arms read.
pub(super) fn operands(program: &Program, id: ExprId) -> impl Iterator<Item = Atom> + '_ {
    let (one, many) = match program.expr(id) {
        Expr::Atom(atom) | Expr::Match(atom, _) => (Some(atom), &[][..]),
        Expr::Static(_) => (None, &[][..]),
        Expr::Con(_, args) | Expr::Call(_, args) => (None, program.atoms(args)),
    };
    one.into_iter().chain(many.iter().copied())
}

/// How many times `exprs` read local `level`. A local bound before every
/// one of them is read as itself in any arm, since arms bind only levels
/// past it.
pub(super) fn reads(program: &Program, exprs: impl Iterator<Item = ExprId>, level: usize) -> usize {
    exprs
        .map(|id| {
            operands(program, id)
                .filter(|atom| atom.0.index() == level)
                .count()
        })
        .sum()
}

/// A body that is nothing but a match: which local it takes apart, which
/// with no bindings before it is a parameter, and its arms.
pub(super) fn top_match(program: &Program, body: Body) -> Option<(usize, Range)> {
    if !body.bindings.is_empty() {
        return None;
    }
    let Expr::Match(Atom(on), arms) = program.expr(body.tail) else {
        return None;
    };
    Some((on.index(), arms))
}

/// A match's two arms, `first`'s before `second`'s, whichever order the
/// declaration gave them.
pub(super) fn split_arms(
    program: &Program,
    arms: Range,
    first: CtorId,
    second: CtorId,
) -> Option<[Arm; 2]> {
    let &[a, b] = program.arms(arms) else {
        return None;
    };
    match (a.ctor, b.ctor) {
        (x, y) if x == first && y == second => Some([a, b]),
        (x, y) if x == second && y == first => Some([b, a]),
        _ => None,
    }
}

/// What wrote local `level`, where it is a binding of `body`, whose first
/// binding takes level `base`.
pub(super) fn bound(program: &Program, body: Body, base: usize, level: usize) -> Option<ExprId> {
    let at = level.checked_sub(base)?;
    program.bindings(body.bindings).get(at).copied()
}
