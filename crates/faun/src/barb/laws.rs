//! Local identities justified by recognized equations, never by names.
//! Arguments are ANF locals: replacing a call does not discard, reorder or
//! duplicate the bindings which evaluated them. No general dead-code removal.

use super::{Atom, Body, ConstantView, Expr, ExprId, FnId, Operation, Program};

pub(super) fn laws(program: &mut Program) {
    let operations = super::arithmetic::recognise(program);
    for at in 0..program.functions().len() {
        if operations[at].is_some() {
            continue;
        }
        let id = FnId::at(at);
        if let Some(body) = program.function(id).body() {
            let mut small = vec![None; program.params(id).len()];
            in_body(program, &operations, body, &mut small, 128);
        }
    }
}

fn in_body(
    program: &mut Program,
    ops: &[Option<Operation>],
    body: Body,
    small: &mut Vec<Option<u8>>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    for at in body.bindings.range() {
        let id = program.bindings[at];
        let value = in_expr(program, ops, id, small, depth);
        small.push(value);
    }
    in_expr(program, ops, body.tail, small, depth);
}

#[expect(
    clippy::too_many_lines,
    reason = "one exhaustive expression dispatch for local identity facts"
)]
fn in_expr(
    program: &mut Program,
    ops: &[Option<Operation>],
    id: ExprId,
    small: &mut Vec<Option<u8>>,
    depth: usize,
) -> Option<u8> {
    match program.expr(id) {
        Expr::Atom(a) => small[a.0.index()],
        Expr::Static(value) => {
            let ConstantView::Natural(number) = program.constant(value).view() else {
                return None;
            };
            match number.try_u64() {
                Ok(0) => Some(0),
                Ok(1) => Some(1),
                _ => None,
            }
        }
        Expr::Con(ctor, fields) => {
            let (nil, _) = super::arithmetic::natural(program, program.ctor(ctor).owner)?;
            if ctor == nil {
                Some(0)
            } else if small[program.atoms(fields)[0].0.index()] == Some(0) {
                Some(1)
            } else {
                None
            }
        }
        Expr::Match(_, arms) => {
            for at in arms.range() {
                let arm = program.arms[at];
                let level = small.len();
                small.resize(level + program.fields(arm.ctor).len(), None);
                in_body(program, ops, arm.body, small, depth - 1);
                small.truncate(level);
            }
            None
        }
        Expr::Call(called, args) => {
            let replacement = identity(program, ops[called.index()]?, called, args, small)?;
            program.write(id, replacement);
            match replacement {
                Expr::Atom(a) => small[a.0.index()],
                Expr::Static(..) => Some(0),
                _ => None,
            }
        }
    }
}

fn identity(
    program: &mut Program,
    op: Operation,
    called: FnId,
    args: super::Range,
    small: &[Option<u8>],
) -> Option<Expr> {
    let [a, b] = program.atoms(args) else {
        return None;
    };
    let (a, b) = (*a, *b);
    let value = |a: Atom| small[a.0.index()];
    let (x, y) = (value(a), value(b));
    Some(match op {
        Operation::Add if x == Some(0) => Expr::Atom(b),
        Operation::Add | Operation::Monus | Operation::Mod if y == Some(0) => Expr::Atom(a),
        Operation::Mul if x == Some(1) => Expr::Atom(b),
        Operation::Mul | Operation::Div if y == Some(1) => Expr::Atom(a),
        Operation::Monus if x == Some(0) || a == b => zero(program, called),
        Operation::Mul | Operation::Div if x == Some(0) || y == Some(0) => zero(program, called),
        Operation::Mod if x == Some(0) || y == Some(1) || a == b => zero(program, called),
        Operation::Equals { yes, .. } if a == b => Expr::Con(yes, super::Range::default()),
        Operation::LessThan { no, .. } if a == b => Expr::Con(no, super::Range::default()),
        // In particular x/x is NOT one: x can be zero.
        _ => return None,
    })
}

fn zero(program: &mut Program, called: FnId) -> Expr {
    let owner = program.function(called).result;
    let value = program.intern_number(owner, 0);
    Expr::Static(value)
}
