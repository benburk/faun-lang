//! Capture-free structural rebuilding, with optional bounded helper expansion.
//!
//! Structural normalization substitutes aliases without planning any inlining.
//! Expanding rewrites use the policy in `inline`; both preserve eager bindings
//! and protect recognized arithmetic definitions from changes to their equations.
//!
//! Every walk also decides what is already decided. A match on a local
//! written as a constructor, or as a known value, is the arm for that
//! constructor, with its fields what built it: nothing is tested. And a
//! match whose arms bind nothing and are the same asks a question whose
//! answer changes nothing, so it is that arm. Neither drops or reorders a
//! binding: the arm taken is the one that would have run, and the arms that
//! are not were never going to.
//!
//! A match whose answer is taken apart by the match after it, and by nothing
//! else, is one match: where every arm of the first ends by building a
//! constructor, the second's arm for that constructor is where it goes on.
//!
//! ```text
//! x = match s                     match s
//!   A => .. C(a)                    A => .. (arm C of the second, with a)
//!   B => .. D(b)          =>        B => .. (arm D of the second, with b)
//! match x
//!   C(p) => ..
//!   D(q) => ..
//! ```
//!
//! Nothing is built only to be asked what it is, and a field one
//! constructor carries and another does not is never held in one place for
//! both. Only where no arm of the second is taken by two arms of the first,
//! so nothing is copied twice.

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

/// Whether anything in `body` reads the local at `level`.
fn reads(program: &Program, body: Body, level: usize) -> bool {
    let is = |atom: &Atom| atom.0.index() == level;
    program
        .bindings(body.bindings)
        .iter()
        .chain([&body.tail])
        .any(|&expr| match program.expr(expr) {
            Expr::Atom(atom) => is(&atom),
            Expr::Static(_) => false,
            Expr::Con(_, atoms) | Expr::Call(_, atoms) => program.atoms(atoms).iter().any(is),
            Expr::Match(on, arms) => {
                is(&on)
                    || program
                        .arms(arms)
                        .iter()
                        .any(|arm| reads(program, arm.body, level))
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
        written: Vec::new(),
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
        rewrite.written.clear();
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
    /// What wrote each local of the body being rebuilt, by level, where a
    /// binding of it did: a parameter or a field an arm took apart says
    /// nothing. Arms reuse levels, so this is cut back to where each begins.
    written: Vec<Option<ExprId>>,
}
/// What rebuilding a match came to.
enum Matched {
    Rebuilt(Expr),
    /// Every arm binds nothing and says the same: this one.
    Same(Body),
    /// Every arm puts back what it took apart.
    Scrutinee,
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
        self.body_with(level, |rewrite, scope| rewrite.into(body, locals, scope))
    }

    /// A body of its own, whose first binding takes `level`, written by
    /// `write`.
    fn body_with(
        &mut self,
        level: usize,
        write: impl FnOnce(&mut Self, &mut Scope) -> Atom,
    ) -> Body {
        self.written.truncate(level);
        self.written.resize(level, None);
        let mut scope = Scope {
            bindings: vec![],
            level,
            base: level,
        };
        let answer = write(self, &mut scope);
        let tail = if answer.0.index() + 1 == scope.level && !scope.bindings.is_empty() {
            scope.bindings.pop().expect("the last binding")
        } else {
            self.program.terms.push(Expr::Atom(answer))
        };
        self.program.terms.hold_body(&scope.bindings, tail)
    }
    fn into(&mut self, body: Body, mut locals: Vec<Atom>, scope: &mut Scope) -> Atom {
        let cased = self.cased(body, locals.len());
        let last = body.bindings.range().end;
        for at in body.bindings.range() {
            if let Some((scrutinee, first, second)) = cased
                && at + 1 == last
            {
                return self.merged(scrutinee, first, second, &locals, scope);
            }
            let binding = self.program.terms.binding(at);
            let value = self.expr(binding, &locals, scope);
            locals.push(value);
        }
        self.expr(body.tail, &locals, scope)
    }

    /// Where a body ends by taking apart, and only taking apart, a match
    /// that is its last binding, each of whose arms ends by building a
    /// constructor, no two of them one taken by the same arm: the first
    /// match's scrutinee and arms, and the second's arms. `level` is the
    /// level of the body's first binding.
    fn cased(&self, body: Body, level: usize) -> Option<(Atom, Range, Range)> {
        let bindings = self.program.bindings(body.bindings);
        let &last = bindings.last()?;
        let answer = level + bindings.len() - 1;
        let Expr::Match(Atom(on), second) = self.program.expr(body.tail) else {
            return None;
        };
        let Expr::Match(scrutinee, first) = self.program.expr(last) else {
            return None;
        };
        if on.index() != answer {
            return None;
        }
        let mut taken = vec![false; self.program.arms(second).len()];
        for arm in self.program.arms(first) {
            let Expr::Con(ctor, _) = self.program.expr(arm.body.tail) else {
                return None;
            };
            let at = self
                .program
                .arms(second)
                .iter()
                .position(|arm| arm.ctor == ctor)?;
            if std::mem::replace(&mut taken[at], true) {
                return None;
            }
        }
        let read = self
            .program
            .arms(second)
            .iter()
            .any(|arm| reads(self.program, arm.body, answer));
        (!read).then_some((scrutinee, first, second))
    }

    /// The first match, each arm going on into the second's arm for the
    /// constructor it built.
    fn merged(
        &mut self,
        scrutinee: Atom,
        first: Range,
        second: Range,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Atom {
        let second: Vec<_> = self.program.arms(second).to_vec();
        let mut found = vec![];
        for at in first.range() {
            let arm = self.program.terms.arm(at);
            let fields = self.program.fields(arm.ctor).len();
            let mut inner = locals.to_vec();
            inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
            self.written.truncate(scope.level);
            let body = self.body_with(scope.level + fields, |rewrite, arm_scope| {
                for at in arm.body.bindings.range() {
                    let binding = rewrite.program.terms.binding(at);
                    let value = rewrite.expr(binding, &inner, arm_scope);
                    inner.push(value);
                }
                let Expr::Con(ctor, built) = rewrite.program.expr(arm.body.tail) else {
                    unreachable!("every arm was seen to build a constructor");
                };
                let built = rewrite.args(built, &inner);
                let next = second
                    .iter()
                    .find(|arm| arm.ctor == ctor)
                    .expect("every constructor built has an arm");
                // Nothing reads the first match's answer, so its level may
                // stand for anything.
                let mut going = locals.to_vec();
                going.push(locals[scrutinee.0.index()]);
                going.extend(built);
                rewrite.into(next.body, going, arm_scope)
            });
            found.push(Arm {
                ctor: arm.ctor,
                body,
            });
        }
        self.written.truncate(scope.level);
        let arms = self.program.terms.hold_arms(&found);
        self.push(Expr::Match(locals[scrutinee.0.index()], arms), scope)
    }
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per expression kind, and the match arm decides before it rebuilds"
    )]
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
            Expr::Match(value, arms) => {
                let scrutinee = locals[value.0.index()];
                if let Some(answer) = self.selected(scrutinee, arms, locals, scope) {
                    return answer;
                }
                match self.matching(value, arms, locals, scope) {
                    Matched::Rebuilt(held) => held,
                    Matched::Same(body) => return self.spliced(body, scope),
                    // One that puts back what it took apart is what it took apart.
                    Matched::Scrutinee => return scrutinee,
                }
            }
        };
        self.push(expr, scope)
    }

    /// The arm a match takes where its scrutinee was written as one
    /// constructor or as a known value, taken where the match stands: its
    /// fields are the atoms that built it, or known values of their own.
    fn selected(
        &mut self,
        scrutinee: Atom,
        arms: Range,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Option<Atom> {
        let wrote = (*self.written.get(scrutinee.0.index())?)?;
        let (ctor, fields) = match self.program.expr(wrote) {
            Expr::Con(ctor, fields) => (ctor, self.program.atoms(fields).to_vec()),
            Expr::Static(value) => self.opened(value, scope)?,
            Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => return None,
        };
        let arm = self
            .program
            .arms(arms)
            .iter()
            .find(|arm| arm.ctor == ctor)
            .copied()?;
        let mut inner = locals.to_vec();
        inner.extend(fields);
        Some(self.into(arm.body, inner, scope))
    }

    /// A known value's constructor, and each of its fields as a known value
    /// of its own, bound here. A known number is its successor's step, or
    /// nought; a known sequence is left to be taken apart where it runs.
    fn opened(
        &mut self,
        value: super::ConstId,
        scope: &mut Scope,
    ) -> Option<(super::CtorId, Vec<Atom>)> {
        let constant = self.program.constant(value);
        let ctor = constant.constructor();
        let owner = constant.owner();
        let fields: Vec<_> = match constant.view() {
            super::ConstantView::Constructor(view) => {
                let mut budget = Budget::new(FoldLimits::default());
                let fields = view.fields(&mut budget).ok()?;
                fields
                    .into_iter()
                    .map(|field| field.to_owned(&mut budget))
                    .collect::<Result<Vec<_>, _>>()
                    .ok()?
                    .into_iter()
                    .map(|held| self.program.intern_held(&held))
                    .collect()
            }
            super::ConstantView::Natural(number) => {
                let number = number.to_biguint();
                if number == num_bigint::BigUint::default() {
                    Vec::new()
                } else {
                    let before = number - 1u8;
                    vec![self.program.intern_natural(owner, &before).ok()?]
                }
            }
            super::ConstantView::Spine(_) => return None,
        };
        let atoms = fields
            .into_iter()
            .map(|field| self.push(Expr::Static(field), scope))
            .collect();
        Some((ctor, atoms))
    }

    /// A rebuilt arm that binds nothing, laid where the match stood: its
    /// bindings already take the levels they would take here.
    fn spliced(&mut self, body: Body, scope: &mut Scope) -> Atom {
        for &binding in &self.program.bindings(body.bindings).to_vec() {
            scope.bindings.push(binding);
            self.written.truncate(scope.level);
            self.written.push(Some(binding));
            scope.level += 1;
        }
        match self.program.expr(body.tail) {
            Expr::Atom(atom) => atom,
            tail => self.push(tail, scope),
        }
    }
    /// Rebuild a match's arms: as a match, as the one arm every arm is, or
    /// as its scrutinee where every arm puts back the constructor it took
    /// apart.
    fn matching(&mut self, value: Atom, arms: Range, locals: &[Atom], scope: &Scope) -> Matched {
        let mut found = vec![];
        for at in arms.range() {
            let arm = self.program.terms.arm(at);
            let fields = self.program.fields(arm.ctor).len();
            let mut inner = locals.to_vec();
            inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
            // A sibling arm's bindings may have taken this arm's fields'
            // levels, and what wrote them is not what this arm binds.
            self.written.truncate(scope.level);
            found.push(Arm {
                ctor: arm.ctor,
                body: self.body(arm.body, inner, scope.level + fields),
            });
        }
        self.written.truncate(scope.level);
        if rebuilt(self.program, &found, scope.level) {
            return Matched::Scrutinee;
        }
        if let Some((first, rest)) = found.split_first()
            && self.program.fields(first.ctor).is_empty()
            && rest.iter().all(|arm| {
                self.program.fields(arm.ctor).is_empty() && self.same_body(first.body, arm.body)
            })
        {
            return Matched::Same(first.body);
        }
        let arms = self.program.terms.hold_arms(&found);
        Matched::Rebuilt(Expr::Match(locals[value.0.index()], arms))
    }

    /// Whether two bodies say the same thing, term for term. Known values
    /// are compared by what they are, since equal ones are held apart.
    fn same_body(&self, a: Body, b: Body) -> bool {
        let (left, right) = (
            self.program.bindings(a.bindings),
            self.program.bindings(b.bindings),
        );
        left.len() == right.len()
            && left.iter().zip(right).all(|(&x, &y)| self.same_expr(x, y))
            && self.same_expr(a.tail, b.tail)
    }

    fn same_expr(&self, a: ExprId, b: ExprId) -> bool {
        match (self.program.expr(a), self.program.expr(b)) {
            (Expr::Atom(x), Expr::Atom(y)) => x == y,
            (Expr::Static(x), Expr::Static(y)) => {
                let (x, y) = (self.program.constant(x), self.program.constant(y));
                x.owner() == y.owner() && x.encoded() == y.encoded()
            }
            (Expr::Con(x, xs), Expr::Con(y, ys)) => {
                x == y && self.program.atoms(xs) == self.program.atoms(ys)
            }
            (Expr::Call(x, xs), Expr::Call(y, ys)) => {
                x == y && self.program.atoms(xs) == self.program.atoms(ys)
            }
            (Expr::Match(x, xs), Expr::Match(y, ys)) => {
                let (xs, ys) = (self.program.arms(xs), self.program.arms(ys));
                x == y
                    && xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys)
                        .all(|(l, r)| l.ctor == r.ctor && self.same_body(l.body, r.body))
            }
            _ => false,
        }
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
        self.written.truncate(scope.level);
        self.written.resize(scope.level, None);
        self.written.push(Some(id));
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
