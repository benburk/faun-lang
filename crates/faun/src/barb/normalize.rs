//! Capture-free structural rebuilding, with optional bounded helper expansion.
//!
//! Structural normalization substitutes aliases without planning any inlining.
//! Expanding rewrites use the policy in `inline`; both preserve eager bindings
//! and protect recognized arithmetic definitions from changes to their equations.

use super::inline::{InlineLimits, Inlining};
use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range};

/// Remove local aliases without expanding calls or dropping eager bindings.
pub fn structural(program: &mut Program) {
    rewrite(program, None);
}

/// Normalize aliases and inline nonrecursive helpers within the supplied limits.
/// A zero limit disables expansion without computing recursion or copy costs.
pub fn normalize_with_limits(program: &mut Program, limits: InlineLimits) {
    let inlining = Inlining::new(program, limits);
    rewrite(program, inlining);
}

/// Whether every arm puts back the constructor it took apart, out of that
/// constructor's own fields and nothing else.
///
/// A match like that asks which one it is and answers with the one it is, so
/// it is the value it took apart. Nothing is dropped by saying so: an arm
/// shaped this way holds no bindings, so there is nothing in it to evaluate,
/// and validation has already said the arms cover the type. A type with no
/// constructors is left alone -- a match on one never answers, and the value
/// it took apart does.
///
/// `level` is the local the first arm binds its fields at.
fn rebuilt(program: &Program, arms: &[Arm], level: usize) -> bool {
    !arms.is_empty()
        && arms.iter().all(|arm| {
            arm.body.bindings.is_empty()
                && match program.expr(arm.body.tail) {
                    Expr::Con(ctor, fields) => {
                        ctor == arm.ctor
                            && program
                                .atoms(fields)
                                .iter()
                                .enumerate()
                                .all(|(at, held)| held.0.index() == level + at)
                    }
                    _ => false,
                }
        })
}

fn rewrite(program: &mut Program, inlining: Option<Inlining>) {
    let operations = super::arithmetic::recognise(program);
    let mut rewrite = Rewrite {
        program,
        operations,
        inlining,
        inline_depth: 0,
    };
    // Reads name existing entries; writes only append. Keep all function roots
    // unchanged until the end, so later callers still inline original bodies
    // using the costs and depth limits computed for those bodies.
    let mut bodies = vec![];
    for at in 0..rewrite.program.functions().len() {
        let id = FnId::at(at);
        if rewrite.operations[at].is_some() {
            continue;
        }
        let Some(body) = rewrite.program.function(id).body() else {
            continue;
        };
        if let Some(inlining) = &mut rewrite.inlining {
            inlining.begin_function();
        }
        let count = rewrite.program.params(id).len();
        let locals: Vec<_> = (0..count).map(|at| Atom(Local::at(at))).collect();
        let body = rewrite.body(body, locals, count);
        bodies.push((id, body));
    }
    rewrite.program.replace_bodies(bodies);
}

struct Rewrite<'a> {
    program: &'a mut Program,
    operations: Vec<Option<super::Operation>>,
    inlining: Option<Inlining>,
    inline_depth: usize,
}
struct Scope {
    bindings: Vec<ExprId>,
    level: usize,
}
impl Rewrite<'_> {
    fn body(&mut self, body: Body, locals: Vec<Atom>, level: usize) -> Body {
        let mut scope = Scope {
            bindings: vec![],
            level,
        };
        let answer = self.into(body, locals, &mut scope);
        let tail = if answer.0.index() + 1 == scope.level && !scope.bindings.is_empty() {
            scope.bindings.pop().expect("the last binding")
        } else {
            self.program.terms.push(Expr::Atom(answer))
        };
        self.program.terms.hold_body(&scope.bindings, tail)
    }
    fn into(&mut self, body: Body, mut locals: Vec<Atom>, scope: &mut Scope) -> Atom {
        for at in body.bindings.range() {
            let binding = self.program.terms.binding(at);
            let value = self.expr(binding, &locals, scope);
            locals.push(value);
        }
        self.expr(body.tail, &locals, scope)
    }
    fn expr(&mut self, id: ExprId, locals: &[Atom], scope: &mut Scope) -> Atom {
        let expr = match self.program.expr(id) {
            Expr::Atom(a) => return locals[a.0.index()],
            value @ Expr::Static(..) => value,
            Expr::Con(ctor, fields) => {
                let fields = self.args(fields, locals);
                Expr::Con(ctor, self.program.terms.hold_atoms(fields.into_iter()))
            }
            Expr::Call(called, args) => {
                let args = self.args(args, locals);
                if let Some(body) = self.callee(called) {
                    self.inline_depth += 1;
                    let answer = self.into(body, args, scope);
                    self.inline_depth -= 1;
                    return answer;
                }
                Expr::Call(called, self.program.terms.hold_atoms(args.into_iter()))
            }
            Expr::Match(value, arms) => match self.matching(value, arms, locals, scope) {
                Some(held) => held,
                // One that puts back what it took apart is what it took apart.
                None => return locals[value.0.index()],
            },
        };
        let id = self.program.terms.push(expr);
        scope.bindings.push(id);
        let value = Atom(Local::at(scope.level));
        scope.level += 1;
        value
    }
    /// Rebuild a match's arms, or nothing at all where every arm puts back
    /// the constructor it took apart and the match is its own scrutinee.
    fn matching(
        &mut self,
        value: Atom,
        arms: Range,
        locals: &[Atom],
        scope: &Scope,
    ) -> Option<Expr> {
        let mut found = vec![];
        for at in arms.range() {
            let arm = self.program.terms.arm(at);
            let fields = self.program.fields(arm.ctor).len();
            let mut inner = locals.to_vec();
            inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
            found.push(Arm {
                ctor: arm.ctor,
                body: self.body(arm.body, inner, scope.level + fields),
            });
        }
        if rebuilt(self.program, &found, scope.level) {
            return None;
        }
        let arms = self.program.terms.hold_arms(&found);
        Some(Expr::Match(locals[value.0.index()], arms))
    }

    fn callee(&mut self, called: FnId) -> Option<Body> {
        if self.operations[called.index()].is_some() {
            return None;
        }
        self.inlining
            .as_mut()?
            .callee(self.program, called, self.inline_depth)
    }

    fn args(&self, args: Range, locals: &[Atom]) -> Vec<Atom> {
        self.program
            .atoms(args)
            .iter()
            .map(|a| locals[a.0.index()])
            .collect()
    }
}
