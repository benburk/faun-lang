//! Copying terms into a body under construction, every local read through
//! a map from the levels the terms were written at to the atoms they stand
//! for where they are copied.
//!
//! A pass building a definition out of pieces of others -- fusing two walks,
//! or putting a definition's base cases where its recursion was -- copies
//! each piece where it goes. Terms are appended; nothing is shared with the
//! bodies copied from, which stay as they were until a pass replaces them.

use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program};

/// The bindings of a body under construction, and the level the next takes.
pub(super) struct Scope {
    pub bindings: Vec<ExprId>,
    pub level: usize,
}

impl Scope {
    /// A scope whose first binding takes `level`.
    pub(super) const fn at(level: usize) -> Self {
        Self {
            bindings: Vec::new(),
            level,
        }
    }
}

/// Calls of `from` whose argument `at` is `rest` go to `to` instead, with
/// `leading` before the rest of their arguments.
pub(super) struct Redirect {
    pub from: FnId,
    pub at: usize,
    pub rest: Atom,
    pub to: FnId,
    pub leading: Vec<Atom>,
}

/// Copy `body` as a body of its own, whose first binding takes `level`.
pub(super) fn body(
    program: &mut Program,
    body: Body,
    locals: Vec<Atom>,
    level: usize,
    redirect: Option<&Redirect>,
) -> Body {
    let mut scope = Scope::at(level);
    let answer = into(program, body, locals, &mut scope, redirect);
    close(program, scope, answer)
}

/// Copy `body`'s bindings into `scope`, answering what its tail comes to.
pub(super) fn into(
    program: &mut Program,
    body: Body,
    mut locals: Vec<Atom>,
    scope: &mut Scope,
    redirect: Option<&Redirect>,
) -> Atom {
    for binding in program.bindings(body.bindings).to_vec() {
        let value = expr(program, binding, &locals, scope, redirect);
        locals.push(value);
    }
    expr(program, body.tail, &locals, scope, redirect)
}

/// Copy one expression into `scope`, answering the local it takes, or the
/// atom it reads where it is only that.
#[expect(
    clippy::too_many_lines,
    reason = "one arm per expression kind, each copied through the map"
)]
pub(super) fn expr(
    program: &mut Program,
    id: ExprId,
    locals: &[Atom],
    scope: &mut Scope,
    redirect: Option<&Redirect>,
) -> Atom {
    let map = |held: &[Atom]| -> Vec<Atom> { held.iter().map(|a| locals[a.0.index()]).collect() };
    let copied = match program.expr(id) {
        Expr::Atom(atom) => return locals[atom.0.index()],
        held @ Expr::Static(_) => held,
        Expr::Con(ctor, fields) => {
            let fields = map(program.atoms(fields));
            Expr::Con(ctor, program.terms.hold_atoms(fields.into_iter()))
        }
        Expr::Call(callee, args) => {
            let args = map(program.atoms(args));
            let (callee, args) = match redirect {
                Some(redirect) if callee == redirect.from && args[redirect.at] == redirect.rest => {
                    let mut going = redirect.leading.clone();
                    going.extend(
                        args.iter()
                            .enumerate()
                            .filter(|&(at, _)| at != redirect.at)
                            .map(|(_, &atom)| atom),
                    );
                    (redirect.to, going)
                }
                _ => (callee, args),
            };
            Expr::Call(callee, program.terms.hold_atoms(args.into_iter()))
        }
        Expr::Match(on, arms) => {
            let mut rebuilt = Vec::new();
            for arm in program.arms(arms).to_vec() {
                let fields = program.fields(arm.ctor).len();
                let mut inner = locals.to_vec();
                inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
                let copied = body(program, arm.body, inner, scope.level + fields, redirect);
                rebuilt.push(Arm {
                    ctor: arm.ctor,
                    body: copied,
                });
            }
            let arms = program.terms.hold_arms(&rebuilt);
            Expr::Match(locals[on.0.index()], arms)
        }
    };
    push(program, scope, copied)
}

/// Write an expression down as the next binding, answering its local.
pub(super) fn push(program: &mut Program, scope: &mut Scope, expr: Expr) -> Atom {
    let id = program.terms.push(expr);
    scope.bindings.push(id);
    let held = Atom(Local::at(scope.level));
    scope.level += 1;
    held
}

/// A scope's bindings, answering `answer`: the last binding is the tail
/// where it is what the scope answers.
pub(super) fn close(program: &mut Program, mut scope: Scope, answer: Atom) -> Body {
    let tail = if answer.0.index() + 1 == scope.level && !scope.bindings.is_empty() {
        scope.bindings.pop().expect("the last binding")
    } else {
        program.terms.push(Expr::Atom(answer))
    };
    program.terms.hold_body(&scope.bindings, tail)
}
