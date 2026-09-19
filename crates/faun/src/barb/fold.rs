//! Constant folding shares the recognizer's arithmetic semantics. Unknown
//! calls remain opaque; exhausting the evaluation budget leaves a term alone.

use super::evaluate::{Evaluator, Held};
use super::{Body, Expr, ExprId, FnId, Operation, Program};

const FUEL: u32 = 1024;

pub fn fold(program: &mut Program) {
    // Read equations before rewriting their bodies. Facts are immutable for
    // this pass; rewriting constants cannot change a definition's meaning.
    let operations = super::arithmetic::recognise(program);
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body else {
            continue;
        };
        let mut known = vec![None; program.params(id).len()];
        in_body(program, &operations, body, &mut known);
    }
}

fn in_body(
    program: &mut Program,
    operations: &[Option<Operation>],
    body: Body,
    known: &mut Vec<Option<Held>>,
) {
    for binding in program.bindings(body.bindings).to_vec() {
        let held = in_expr(program, operations, binding, known);
        known.push(held);
    }
    in_expr(program, operations, body.tail, known);
}

fn in_expr(
    program: &mut Program,
    operations: &[Option<Operation>],
    id: ExprId,
    known: &mut Vec<Option<Held>>,
) -> Option<Held> {
    let evaluator = Evaluator {
        program,
        operations,
    };
    let mut fuel = FUEL;
    if let Some(value) = evaluator.expr(id, known, &mut fuel) {
        let held = program.intern_encoded(&value.bytes);
        program.write(id, Expr::Static(value.owner, held));
        return Some(value);
    }
    if let Expr::Match(_, arms) = program.expr(id) {
        for arm in program.arms(arms).to_vec() {
            let level = known.len();
            known.resize(level + program.fields(arm.ctor).len(), None);
            in_body(program, operations, arm.body, known);
            known.truncate(level);
        }
    }
    None
}
