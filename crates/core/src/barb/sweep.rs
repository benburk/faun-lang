//! Dropping definitions the entry cannot reach.
//!
//! Inlining copies a helper into its callers and fusion writes a walk in
//! place of two, and each leaves the definition it read behind. Nothing
//! calls it any more, but every definition is a root to the passes before
//! this one, so it stays until this: a program with an entry keeps what the
//! entry reaches and nothing else. One without an entry is only checked,
//! and every definition in it is what it is for, so it keeps them all.
//!
//! Function IDs are renumbered, keeping their order, so an ID held from
//! before this names nothing or something else. Types, constructors and
//! constants are neither dropped nor renumbered.

use super::{Expr, ExprId, FnId, Program};
use crate::index::Pool;

/// Keep only the definitions the entry reaches, where there is one.
pub(crate) fn sweep(program: &mut Program) {
    let Some(entry) = program.entry else {
        return;
    };
    let (reached, calls) = reached(program, entry);
    if reached.iter().all(|&kept| kept) {
        return;
    }
    let mut renamed = vec![None; reached.len()];
    let mut kept = Pool::default();
    for (at, function) in program.functions.iter().enumerate() {
        if reached[at] {
            renamed[at] = Some(kept.push(function.clone()));
        }
    }
    let renamed = |id: FnId| renamed[id.index()].expect("a reached definition");
    for expr in calls {
        let Expr::Call(callee, args) = program.expr(expr) else {
            unreachable!("a call found reaching");
        };
        program.write(expr, Expr::Call(renamed(callee), args));
    }
    program.entry = Some(renamed(entry));
    program.functions = kept;
    program.redefined();
}

/// Which definitions `entry` reaches, by function, and every call in them,
/// each once however many bodies share it.
pub(super) fn reached(program: &Program, entry: FnId) -> (Vec<bool>, Vec<ExprId>) {
    let mut reached = vec![false; program.functions.len()];
    let mut seen = vec![false; program.terms.exprs_count()];
    let mut calls = Vec::new();
    let mut waiting = vec![entry];
    while let Some(id) = waiting.pop() {
        if std::mem::replace(&mut reached[id.index()], true) {
            continue;
        }
        let Some(body) = program.functions[id].body() else {
            continue;
        };
        let mut exprs: Vec<_> = program.bindings(body.bindings).to_vec();
        exprs.push(body.tail);
        while let Some(expr) = exprs.pop() {
            if std::mem::replace(&mut seen[expr.index()], true) {
                continue;
            }
            match program.expr(expr) {
                Expr::Call(callee, _) => {
                    waiting.push(callee);
                    calls.push(expr);
                }
                Expr::Match(_, arms) => {
                    for arm in program.arms(arms) {
                        exprs.extend_from_slice(program.bindings(arm.body.bindings));
                        exprs.push(arm.body.tail);
                    }
                }
                Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => {}
            }
        }
    }
    (reached, calls)
}
