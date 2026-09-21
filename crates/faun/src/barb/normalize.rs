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

/// The same walk again, for what folding made knowable.
///
/// A program says a modulus by working one out, and what a sum modulo a
/// power of two is worth knowing about cannot be seen until that power of
/// two is a number rather than a run of products.
pub(super) fn reduce(program: &mut Program) {
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
    /// The level this scope began at, so that a local it bound can be
    /// looked back up: the one at `level` is `bindings[level - base]`.
    base: usize,
}

impl Scope {
    /// What wrote a local, where this scope wrote it. A parameter or a
    /// field an arm took apart was written somewhere else and says nothing.
    fn wrote(&self, atom: Atom) -> Option<ExprId> {
        let at = atom.0.index();
        self.bindings.get(at.checked_sub(self.base)?).copied()
    }
}
impl Rewrite<'_> {
    fn body(&mut self, body: Body, locals: Vec<Atom>, level: usize) -> Body {
        let mut scope = Scope {
            bindings: vec![],
            level,
            base: level,
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
                if let Some(held) = self.reduced(called, &args, scope) {
                    return held;
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

    /// A sum or a product taken modulo a power of two, worked out modulo
    /// that power of two throughout.
    ///
    /// Adding and multiplying carry through a remainder: what two numbers
    /// come to modulo `m` is what their remainders come to modulo `m`. So a
    /// program asking for the low bits of a sum is asking for a sum of low
    /// bits, and nothing in between it and the answer has to be any wider
    /// than the answer is.
    ///
    /// This is the whole of how a language whose only number counts without
    /// a last step says eight-bit wrapping arithmetic. Written the other way
    /// round it says the same and means two arbitrary-precision numbers, a
    /// heap to hold them, and a division to finish.
    ///
    /// Only a power of two: any other modulus leaves three divisions where
    /// there was one. And not truncated subtraction, which stops at nought
    /// rather than carrying through, nor division or the remainder itself.
    fn reduced(&mut self, called: FnId, args: &[Atom], scope: &mut Scope) -> Option<Atom> {
        if self.operations[called.index()] != Some(super::Operation::Mod) {
            return None;
        }
        let [held, modulus] = *args else {
            return None;
        };
        if !self.power_of_two(scope, modulus) {
            return None;
        }
        let Expr::Call(inner, held) = self.program.expr(scope.wrote(held)?) else {
            return None;
        };
        if !matches!(
            self.operations[inner.index()],
            Some(super::Operation::Add | super::Operation::Mul)
        ) {
            return None;
        }
        let [left, right] = *self.program.atoms(held) else {
            return None;
        };
        let args = self.held(&[left, modulus]);
        let left = self.push(Expr::Call(called, args), scope);
        let args = self.held(&[right, modulus]);
        let right = self.push(Expr::Call(called, args), scope);
        let args = self.held(&[left, right]);
        let sum = self.push(Expr::Call(inner, args), scope);
        let args = self.held(&[sum, modulus]);
        Some(self.push(Expr::Call(called, args), scope))
    }

    /// Whether a local was written as a power of two, known before the
    /// program runs.
    fn power_of_two(&self, scope: &Scope, atom: Atom) -> bool {
        let Some(Expr::Static(value)) = scope.wrote(atom).map(|id| self.program.expr(id)) else {
            return false;
        };
        let super::ConstantView::Natural(number) = self.program.constant(value).view() else {
            return false;
        };
        matches!(number.try_u64(), Ok(held) if held.is_power_of_two())
    }

    fn held(&mut self, atoms: &[Atom]) -> Range {
        self.program.terms.hold_atoms(atoms.iter().copied())
    }

    /// Write an expression down and answer the local it took.
    fn push(&mut self, expr: Expr, scope: &mut Scope) -> Atom {
        let id = self.program.terms.push(expr);
        scope.bindings.push(id);
        let held = Atom(Local::at(scope.level));
        scope.level += 1;
        held
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
