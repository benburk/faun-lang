//! A definition taking two numbers down together is a subtraction.
//!
//! ```text
//! f(.. a .. b ..) = match a
//!   zero => E1
//!   step(x) => match b
//!     zero => E2
//!     step(y) => f(.. x .. y ..)
//! ```
//!
//! steps both down until one is nought, with nothing else changing on the
//! way, so it answers what its base cases answer for `a` less `b` and `b`
//! less `a`: of those two, at least one is nought, and where the first is
//! not the second is. Written that way it walks nothing, calls nothing but
//! two subtractions, and calls itself not at all, so a caller may take it
//! in whole where it once had to call it:
//!
//! ```text
//! f(.. a .. b ..) =
//!   a' = a monus b
//!   b' = b monus a
//!   match a'
//!     zero => E1 with a', b' for a, b
//!     step(x) => E2 with a', b' for a, b
//! ```
//!
//! A signed number's sum is written this way, where its signs differ, and
//! it is a loop as long as the smaller magnitude until it is not.
//!
//! Nothing is recognized by name: the equation's shape is what is read,
//! and the subtraction is whichever definition is recognized as natural
//! monus over that type, or one written here in the shape the recognizer
//! reads where the program has none.

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::walk::{calls, split_arms, top_match};
use super::{Atom, Body, CtorId, Expr, FnId, Local, Operation, Program, TypeId, TypeShape};

/// Rewrite every definition of that shape.
pub(crate) fn descend(program: &mut Program) {
    let recognised = program.recognised().clone();
    let count = program.functions().len();
    let mut bodies = Vec::new();
    for at in 0..count {
        let id = FnId::at(at);
        if recognised.answered(id) {
            continue;
        }
        let Some(found) = descent(program, id) else {
            continue;
        };
        let monus = monus(program, &recognised, found.number);
        bodies.push((id, rewritten(program, id, &found, monus)));
    }
    program.replace_bodies(bodies);
}

/// Where a definition of the shape takes its two numbers down, and the
/// arms answering once one of them is nought.
struct Descent {
    number: TypeId,
    /// The parameters taken down, the first the one matched first.
    first: usize,
    second: usize,
    /// What answers where the first is nought, and where only the second is.
    first_empty: Body,
    second_empty: Body,
    /// The constructors, in the order a match on the type takes them.
    arms: [CtorId; 2],
    step: CtorId,
}

#[expect(
    clippy::too_many_lines,
    reason = "each condition of the descent shape is one early return, read in order"
)]
fn descent(program: &Program, id: FnId) -> Option<Descent> {
    let body = program.function(id).body()?;
    let params = program.params(id);
    let arity = params.len();
    let (first, outer) = top_match(program, body)?;
    let number = params[first];
    let TypeShape::Natural { empty, push, .. } = super::type_shape(program, number) else {
        return None;
    };
    let [first_empty, first_step] = split_arms(program, outer, empty, push)?.map(|arm| arm.body);
    let (second, inner) = top_match(program, first_step)?;
    if second == first || second >= arity || params[second] != number {
        return None;
    }
    let [second_empty, both_step] = split_arms(program, inner, empty, push)?.map(|arm| arm.body);
    // Both a step: itself again, on the two numbers one less, with every
    // other parameter as it was.
    if !both_step.bindings.is_empty() {
        return None;
    }
    let Expr::Call(again, args) = program.expr(both_step.tail) else {
        return None;
    };
    let args = program.atoms(args);
    let taken_down = |at: usize| match at {
        at if at == first => arity,
        at if at == second => arity + 1,
        at => at,
    };
    if again != id
        || args.len() != arity
        || (0..arity).any(|at| args[at].0.index() != taken_down(at))
    {
        return None;
    }
    // And nowhere else: the base cases are what it answers.
    if calls(program, first_empty, id) || calls(program, second_empty, id) {
        return None;
    }
    let arms = program.arms(outer);
    Some(Descent {
        number,
        first,
        second,
        first_empty,
        second_empty,
        arms: [arms[0].ctor, arms[1].ctor],
        step: push,
    })
}

/// The definition recognized as natural monus over `number`, or one written
/// in the shape the recognizer reads.
fn monus(program: &mut Program, recognised: &Recognised, number: TypeId) -> FnId {
    let params = [number, number];
    recognised
        .operation_over(program, Operation::Monus, &params, number)
        .unwrap_or_else(|| super::arithmetic::write_monus(program, number))
}

fn rewritten(program: &mut Program, id: FnId, found: &Descent, monus: FnId) -> Body {
    let arity = program.params(id).len();
    let mut scope = Scope::at(arity);
    let param = |at: usize| Atom(Local::at(at));
    let (a, b) = (param(found.first), param(found.second));
    let args = program.terms.hold_atoms([a, b].into_iter());
    let less = copy::push(program, &mut scope, Expr::Call(monus, args));
    let args = program.terms.hold_atoms([b, a].into_iter());
    let more = copy::push(program, &mut scope, Expr::Call(monus, args));
    let locals: Vec<_> = (0..arity)
        .map(|at| match at {
            at if at == found.first => less,
            at if at == found.second => more,
            at => param(at),
        })
        .collect();
    let arms: Vec<_> = found
        .arms
        .iter()
        .map(|&ctor| {
            let body = if ctor == found.step {
                let mut inner = locals.clone();
                inner.push(Atom(Local::at(scope.level)));
                copy::body(program, found.second_empty, inner, scope.level + 1, None)
            } else {
                copy::body(
                    program,
                    found.first_empty,
                    locals.clone(),
                    scope.level,
                    None,
                )
            };
            super::Arm { ctor, body }
        })
        .collect();
    let arms = program.terms.hold_arms(&arms);
    let answer = copy::push(program, &mut scope, Expr::Match(less, arms));
    copy::close(program, scope, answer)
}
