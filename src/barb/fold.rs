//! What a program works out before it runs.
//!
//! A term everything under is known is that value, and holding it as the
//! value costs nothing to work out here and cannot be worked out below:
//! `Succ(Succ(Zero))` is three terms the machine tier lowers to three
//! instructions, and two is a constant. The same is true of a call whose
//! arguments are all known, which is the one that matters -- a definition
//! nothing reaches after its callers fold is not emitted at all.
//!
//! Nothing observable folds. An effect has no body to read, so a call to
//! one answers nothing here, and a pure name may not call an effect, so
//! anything with a body is something whose answer is all it does.
//!
//! Working a term out is bounded, since nothing yet says a definition
//! stops. A term that runs past its budget is left as it was written, which
//! is always an answer: what a program says is what it does, and what this
//! tier says of it is only ever less.

use super::constant::{Value, decode};
use super::ir::{Body, Expr, ExprId, FnId, Program};

/// How much working out one term is worth. A number built one constructor
/// at a time costs a step per constructor, so this is also the largest one
/// a program can be handed for free.
const FUEL: u32 = 1024;

/// Hold every term whose value is known as that value.
pub fn fold(program: &mut Program) {
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body else {
            continue;
        };
        // A parameter is whatever it was called with, which is not known
        // here. Everything after them is what this reads.
        let mut known = vec![None; program.params(id).len()];
        in_body(program, body, &mut known);
    }
}

/// Each binding takes the next local, so what is known of one is known by
/// where it sits.
fn in_body(program: &mut Program, body: Body, known: &mut Vec<Option<Value>>) {
    for binding in program.bindings(body.bindings).to_vec() {
        let held = in_expr(program, binding, known);
        known.push(held);
    }
    in_expr(program, body.tail, known);
}

fn in_expr(program: &mut Program, id: ExprId, known: &mut Vec<Option<Value>>) -> Option<Value> {
    let mut fuel = FUEL;
    if let Some(value) = eval(program, id, known, &mut fuel) {
        // What the value is says which type it belongs to, and nothing
        // else has to.
        let owner = program.ctor(value.0).owner;
        let held = program.intern(owner, &value);
        program.write(id, Expr::Static(owner, held));
        return Some(value);
    }
    // Not known, so what is inside it may still be: the arms of a match on
    // something this tier cannot see are lowered like any other body.
    if let Expr::Match(_, arms) = program.expr(id) {
        for arm in program.arms(arms).to_vec() {
            // Sibling arms bind the same locals, being alternatives rather
            // than a sequence, and a field of a value nothing knows is one
            // more thing nothing knows.
            let level = known.len();
            known.resize(level + program.fields(arm.ctor).len(), None);
            in_body(program, arm.body, known);
            known.truncate(level);
        }
    }
    None
}

/// What a term is, where everything it reads is known.
fn eval(program: &Program, id: ExprId, env: &[Option<Value>], fuel: &mut u32) -> Option<Value> {
    *fuel = fuel.checked_sub(1)?;
    match program.expr(id) {
        Expr::Atom(atom) => env.get(atom.0.index())?.clone(),
        Expr::Static(owner, held) => Some(decode(program, owner, program.known_bytes(held)).0),
        Expr::Con(ctor, args) => {
            let fields = held(program, args, env)?;
            Some(Value(ctor, fields))
        }
        // A name something outside answers for has no body to work out, and
        // that is what makes it the one thing this cannot see through.
        Expr::Call(called, args) => {
            let body = program.function(called).body?;
            let args = held(program, args, env)?;
            in_scope(program, body, args.into_iter().map(Some).collect(), fuel)
        }
        Expr::Match(scrutinee, arms) => {
            let value = env.get(scrutinee.0.index())?.clone()?;
            let arm = program.arms(arms).iter().find(|arm| arm.ctor == value.0)?;
            let mut inner = env.to_vec();
            inner.extend(value.1.into_iter().map(Some));
            in_scope(program, arm.body, inner, fuel)
        }
    }
}

/// A body worked out, with its bindings taking the locals after `env`.
fn in_scope(
    program: &Program,
    body: Body,
    mut env: Vec<Option<Value>>,
    fuel: &mut u32,
) -> Option<Value> {
    for binding in program.bindings(body.bindings) {
        let held = eval(program, *binding, &env, fuel);
        env.push(held);
    }
    eval(program, body.tail, &env, fuel)
}

/// The values a run of arguments holds, where every one of them is known.
fn held(program: &Program, args: super::ir::Range, env: &[Option<Value>]) -> Option<Vec<Value>> {
    program
        .atoms(args)
        .iter()
        .map(|atom| env.get(atom.0.index())?.clone())
        .collect()
}
