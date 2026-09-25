//! Capture-free structural rebuilding, with optional bounded helper expansion.
//!
//! Structural normalization substitutes aliases without planning any inlining.
//! Expanding rewrites use the policy in `inline`; both preserve eager bindings
//! and protect recognized arithmetic definitions from changes to their equations.

use super::budget::{Budget, FoldLimits};
use super::evaluate::Evaluator;
use super::facts::Recognised;
use super::inline::{InlineLimits, Inlining};
use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Operation, Program, Range};

/// Remove local aliases without expanding calls or dropping eager bindings.
pub(crate) fn structural(program: &mut Program) {
    rewrite(program, None, None);
}

/// The same walk again, for what folding made knowable.
///
/// Recognized addition and multiplication are associative and commutative, so
/// constants separated by one of them can be combined. A program also says a
/// modulus by working one out, and what a sum modulo a power of two is worth
/// knowing about cannot be seen until that power is folded.
pub(super) fn algebra(program: &mut Program, limits: FoldLimits) {
    rewrite(program, None, Some(limits));
}

/// Normalize aliases and inline nonrecursive helpers within the supplied limits.
/// A zero limit disables expansion without computing recursion or copy costs.
pub(crate) fn normalize_with_limits(program: &mut Program, limits: InlineLimits) {
    let inlining = Inlining::new(program, limits);
    rewrite(program, inlining, None);
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

fn rewrite(program: &mut Program, inlining: Option<Inlining>, algebra_limits: Option<FoldLimits>) {
    let recognised = program.recognised().clone();
    let mut rewrite = Rewrite {
        program,
        recognised,
        inlining,
        algebra: algebra_limits.map(Budget::new),
        inline_depth: 0,
    };
    // Reads name existing entries; writes only append. Keep all function roots
    // unchanged until the end, so later callers still inline original bodies
    // using the costs and depth limits computed for those bodies.
    let mut bodies = vec![];
    for at in 0..rewrite.program.functions().len() {
        let id = FnId::at(at);
        if rewrite.recognised.answered(id) {
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
    /// Recognised definitions keep their bodies and are called, not
    /// expanded, so what they were recognised as stays true of them.
    recognised: Recognised,
    inlining: Option<Inlining>,
    /// One shared resource budget for this algebra pass. Its absence means a
    /// structural or inlining walk that must not perform algebraic rewrites.
    algebra: Option<Budget>,
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
                if self.algebra.is_some() {
                    if let Some(held) = self.chained(called, &args, scope) {
                        return held;
                    }
                    if let Some(held) = self.associated(called, &args, scope) {
                        return held;
                    }
                    if let Some(held) = self.reduced(called, &args, scope) {
                        return held;
                    }
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

    /// Combine the constants in a left-associated monus or quotient.
    ///
    /// Natural monus is truncated at zero, and division by zero answers zero.
    /// Those definitions make both directional laws total, including where
    /// either constant is zero:
    ///
    /// ```text
    /// (x monus a) monus b = x monus (a + b)
    /// (x / a) / b         = x / (a * b)
    /// ```
    fn chained(&mut self, called: FnId, args: &[Atom], scope: &mut Scope) -> Option<Atom> {
        let op @ (Operation::Monus | Operation::Div) = self.recognised.operations[called.index()]?
        else {
            return None;
        };
        let [inner, outer_constant] = *args else {
            return None;
        };
        self.constant(scope, outer_constant)?;
        let Expr::Call(inner_called, inner_args) = self.program.expr(scope.wrote(inner)?) else {
            return None;
        };
        if self.recognised.operations[inner_called.index()] != Some(op) {
            return None;
        }
        let [dynamic, inner_constant] = *self.program.atoms(inner_args) else {
            return None;
        };
        self.constant(scope, inner_constant)?;
        let combine = match op {
            Operation::Monus => Operation::Add,
            Operation::Div => Operation::Mul,
            _ => unreachable!("a directional arithmetic chain"),
        };
        let combined = self.calculate(combine, called, inner_constant, outer_constant, scope)?;
        let args = self.held(&[dynamic, combined]);
        Some(self.push(Expr::Call(called, args), scope))
    }

    /// Combine constants across one nested associative operation.
    ///
    /// Calls are A-normal, so `3 + (x + 5)` is an outer call whose second
    /// argument names an earlier call. Recognition proves both calls are the
    /// same pure, total operation; rewriting them neither drops nor reorders
    /// observable work. Constants are combined under the same bounded
    /// evaluator as ordinary folding.
    fn associated(&mut self, called: FnId, args: &[Atom], scope: &mut Scope) -> Option<Atom> {
        let op @ (Operation::Add | Operation::Mul) = self.recognised.operations[called.index()]?
        else {
            return None;
        };
        let [left, right] = *args else {
            return None;
        };
        let (outer_constant, inner, swap) = match (
            self.constant(scope, left).is_some(),
            self.constant(scope, right).is_some(),
        ) {
            (true, false) => (left, right, true),
            (false, true) => (right, left, false),
            _ => return None,
        };
        let Some(inner_expr) = scope.wrote(inner) else {
            return self.commuted(called, inner, outer_constant, swap, scope);
        };
        let Expr::Call(inner_called, inner_args) = self.program.expr(inner_expr) else {
            return self.commuted(called, inner, outer_constant, swap, scope);
        };
        if self.recognised.operations[inner_called.index()] != Some(op) {
            return self.commuted(called, inner, outer_constant, swap, scope);
        }
        let [inner_left, inner_right] = *self.program.atoms(inner_args) else {
            return None;
        };
        let (dynamic, inner_constant) = match (
            self.constant(scope, inner_left).is_some(),
            self.constant(scope, inner_right).is_some(),
        ) {
            (true, false) => (inner_right, inner_left),
            (false, true) => (inner_left, inner_right),
            _ => return None,
        };
        let combined = self.calculate(op, called, outer_constant, inner_constant, scope)?;
        let args = self.held(&[dynamic, combined]);
        Some(self.push(Expr::Call(called, args), scope))
    }

    /// Put a lone constant on the right, leaving an already canonical call
    /// for the ordinary rebuilding path.
    fn commuted(
        &mut self,
        called: FnId,
        dynamic: Atom,
        constant: Atom,
        swap: bool,
        scope: &mut Scope,
    ) -> Option<Atom> {
        if !swap {
            return None;
        }
        let args = self.held(&[dynamic, constant]);
        Some(self.push(Expr::Call(called, args), scope))
    }

    /// Evaluate two known operands under this pass's shared folding budget.
    fn calculate(
        &mut self,
        op: Operation,
        called: FnId,
        left: Atom,
        right: Atom,
        scope: &mut Scope,
    ) -> Option<Atom> {
        let (left, right) = (self.constant(scope, left)?, self.constant(scope, right)?);
        let budget = self.algebra.as_mut()?;
        let left = self.program.constant(left).to_owned(budget).ok()?;
        let right = self.program.constant(right).to_owned(budget).ok()?;
        let value = Evaluator {
            program: self.program,
            operations: &self.recognised.operations,
        }
        .arithmetic(
            op,
            self.program.function(called).result,
            &[left, right],
            budget,
        )
        .ok()?;
        let value = self.program.intern_held(&value);
        Some(self.push(Expr::Static(value), scope))
    }

    /// Which constant wrote a local, if one did.
    fn constant(&self, scope: &Scope, atom: Atom) -> Option<super::ConstId> {
        let Expr::Static(value) = self.program.expr(scope.wrote(atom)?) else {
            return None;
        };
        Some(value)
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
        if self.recognised.operations[called.index()] != Some(Operation::Mod) {
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
            self.recognised.operations[inner.index()],
            Some(Operation::Add | Operation::Mul)
        ) {
            return None;
        }
        let [left, right] = *self.program.atoms(held) else {
            return None;
        };
        // A side already within the modulus is left alone, and where both
        // are there is nothing to do: saying it twice says no more, and
        // this walk happens more than once.
        let done = (
            self.within(scope, left, modulus),
            self.within(scope, right, modulus),
        );
        if done.0 && done.1 {
            return None;
        }
        let low = self.reduce_side(called, left, modulus, done.0, scope);
        // One side reduced once where both sides are the same side.
        let right = if left == right {
            low
        } else {
            self.reduce_side(called, right, modulus, done.1, scope)
        };
        let args = self.held(&[low, right]);
        let sum = self.push(Expr::Call(inner, args), scope);
        let args = self.held(&[sum, modulus]);
        Some(self.push(Expr::Call(called, args), scope))
    }

    /// One side of it, reduced unless it already is.
    fn reduce_side(
        &mut self,
        called: FnId,
        side: Atom,
        modulus: Atom,
        done: bool,
        scope: &mut Scope,
    ) -> Atom {
        if done {
            return side;
        }
        let args = self.held(&[side, modulus]);
        self.push(Expr::Call(called, args), scope)
    }

    /// Whether a side of a sum is already every bit of itself the modulus
    /// keeps, and so needs no remainder of its own.
    ///
    /// Two ways of being that, and both have to be asked. A side written as a
    /// remainder by this same modulus has been round this law already, which
    /// is what stops it nesting one inside another; and a side known to be
    /// under the modulus before the program runs was never going to lose
    /// anything to it. Asking only the first wraps a constant in a remainder
    /// that cannot do anything, and what the tier below reads then is a
    /// number widened to the modulus and narrowed back.
    fn within(&self, scope: &Scope, atom: Atom, modulus: Atom) -> bool {
        self.reduced_by(scope, atom, modulus) || self.under(scope, atom, modulus)
    }

    /// Whether a local was written as a remainder by this same modulus.
    fn reduced_by(&self, scope: &Scope, atom: Atom, modulus: Atom) -> bool {
        let Some(Expr::Call(called, args)) = scope.wrote(atom).map(|id| self.program.expr(id))
        else {
            return false;
        };
        self.recognised.operations[called.index()] == Some(Operation::Mod)
            && self.program.atoms(args).last() == Some(&modulus)
    }

    /// Whether both locals are numbers known before the program runs, the
    /// first under the second.
    fn under(&self, scope: &Scope, atom: Atom, modulus: Atom) -> bool {
        match (self.number(scope, atom), self.number(scope, modulus)) {
            (Some(held), Some(limit)) => held < limit,
            _ => false,
        }
    }

    /// Whether a local was written as a power of two, known before the
    /// program runs.
    fn power_of_two(&self, scope: &Scope, atom: Atom) -> bool {
        self.number(scope, atom).is_some_and(u64::is_power_of_two)
    }

    /// The number a local is, where it is one known before the program runs
    /// and small enough to work out with.
    fn number(&self, scope: &Scope, atom: Atom) -> Option<u64> {
        let Some(Expr::Static(value)) = scope.wrote(atom).map(|id| self.program.expr(id)) else {
            return None;
        };
        let super::ConstantView::Natural(number) = self.program.constant(value).view() else {
            return None;
        };
        number.try_u64().ok()
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
        if self.recognised.answered(called) {
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
