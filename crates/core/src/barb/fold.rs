//! Constant folding shares the recognizer's arithmetic semantics. Unknown
//! calls remain opaque; exhausting the shared budget leaves a term alone.

use super::budget::{Budget, FoldLimits};
use super::evaluate::{CannotFold, Evaluation, Evaluator};
use super::{Body, Expr, ExprId, FnId, Operation, Program};

pub(crate) fn fold(program: &mut Program) {
    fold_with_limits(program, FoldLimits::default());
}

pub(crate) fn fold_with_limits(program: &mut Program, limits: FoldLimits) {
    let order = super::calls::callees_first(program);
    fold_in(program, order, limits);
}

/// Fold again only `changed`, which a later stage handed something new to
/// read, with a budget of its own. A single definition needs no call-graph
/// ordering; several are folded after their callees.
pub(crate) fn refold(program: &mut Program, changed: &[FnId]) {
    let limits = FoldLimits::default();
    match changed {
        [] => {}
        &[id] => fold_in(program, [id], limits),
        _ => {
            let order = super::calls::callees_first(program);
            fold_in(
                program,
                order.into_iter().filter(|id| changed.contains(id)),
                limits,
            );
        }
    }
}

fn fold_in(program: &mut Program, order: impl IntoIterator<Item = FnId>, limits: FoldLimits) {
    let recognised = program.recognised().clone();
    let operations = recognised.operations.as_slice();
    let mut remaining = limits.work;
    // A definition is folded after what it calls, so a call of one whose
    // answer is known outright is a constant by the time a caller asks.
    for id in order {
        // Keep the induction equations intact for subsequent recognition.
        if recognised.answered(id) {
            continue;
        }
        if remaining == 0 {
            break;
        }
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let allowance = remaining.min(limits.work_per_function);
        let mut budget = Budget::new(FoldLimits {
            work: allowance,
            ..limits
        });
        let mut known = vec![Err(CannotFold::DynamicInput); program.params(id).len()];
        in_body(
            program,
            operations,
            body,
            &mut known,
            &mut budget,
            limits.max_depth,
        );
        remaining -= allowance - budget.remaining;
    }
}

fn in_body(
    program: &mut Program,
    operations: &[Option<Operation>],
    body: Body,
    known: &mut Vec<Evaluation>,
    budget: &mut Budget,
    depth: usize,
) {
    if depth == 0 || budget.remaining == 0 {
        return;
    }
    for at in body.bindings.range() {
        let binding = program.terms.binding(at);
        let held = in_expr(program, operations, binding, known, budget, depth);
        known.push(held);
        if budget.remaining == 0 {
            return;
        }
    }
    let _ = in_expr(program, operations, body.tail, known, budget, depth);
}

fn in_expr(
    program: &mut Program,
    operations: &[Option<Operation>],
    id: ExprId,
    known: &mut Vec<Evaluation>,
    budget: &mut Budget,
    depth: usize,
) -> Evaluation {
    let evaluator = Evaluator {
        program,
        operations,
    };
    let refusal = match evaluator.expr(id, known, budget) {
        Ok(value) => {
            if !matches!(program.expr(id), Expr::Static(..)) {
                let held = program.intern_held(&value);
                program.write(id, Expr::Static(held));
            }
            return Ok(value);
        }
        Err(refusal) => refusal,
    };
    if let Expr::Match(_, arms) = program.expr(id) {
        for at in arms.range() {
            let arm = program.terms.arm(at);
            let level = known.len();
            known.resize(
                level + program.fields(arm.ctor).len(),
                Err(CannotFold::DynamicInput),
            );
            in_body(program, operations, arm.body, known, budget, depth - 1);
            known.truncate(level);
            if budget.remaining == 0 {
                break;
            }
        }
    }
    Err(refusal)
}
