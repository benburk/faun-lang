//! Capture-free structural rebuilding, with optional bounded helper expansion.
//!
//! Structural normalization substitutes aliases without planning any inlining.
//! Expanding rewrites use the policy in `inline`; both preserve eager bindings
//! and protect recognized arithmetic definitions from changes to their equations.
//!
//! A walk may also evaluate: a construction or call whose every input is a
//! known value is written as the value it comes to, and a match on a known
//! sequence, which is not taken apart here, is evaluated whole. That is
//! constant folding. Such a walk reads each definition after what it calls,
//! publishing each as it goes, so a caller evaluates its callees as they now
//! stand; a refusal leaves the expression as it was.
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
use super::constant::Held;
use super::evaluate::{CannotFold, Evaluation, Evaluator};
use super::facts::Recognised;
use super::inline::{InlineLimits, Inlining};
use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Operation, Program, Range};

/// What a walk does beyond rebuilding, substituting aliases and deciding
/// what is already decided, which every walk does.
#[derive(Clone, Copy, Default)]
struct Rules {
    /// Write a recognized operation an identity decides as what it
    /// decides: see [`Rewrite::identity`].
    identities: bool,
    /// Combine constants across recognized operations, and work a sum or
    /// product modulo a power of two out modulo it throughout.
    algebra: bool,
    /// Write a construction or call whose every input is known as the value
    /// it evaluates to, reading each definition after what it calls.
    evaluate: bool,
}

/// Remove local aliases without expanding calls or dropping eager bindings.
pub(crate) fn structural(program: &mut Program) {
    rewrite(program, None, Rules::default(), FoldLimits::default(), None);
}

/// The same walk, writing a recognized operation an identity decides as
/// what it decides: see [`Rewrite::identity`].
#[cfg(test)]
pub(super) fn identities(program: &mut Program) {
    let rules = Rules {
        identities: true,
        ..Rules::default()
    };
    rewrite(program, None, rules, FoldLimits::default(), None);
}

/// Normalize aliases and inline nonrecursive helpers within the supplied limits.
/// A zero limit disables expansion without computing recursion or copy costs.
#[cfg(test)]
pub(crate) fn normalize_with_limits(program: &mut Program, limits: InlineLimits) {
    let inlining = Inlining::new(program, limits);
    rewrite(
        program,
        inlining,
        Rules::default(),
        FoldLimits::default(),
        None,
    );
}

/// Inline as [`normalize_with_limits`] does, and apply the identities as
/// [`identities`] does, in one walk.
pub(super) fn inline_with_identities(program: &mut Program, limits: InlineLimits) {
    let inlining = Inlining::new(program, limits);
    let rules = Rules {
        identities: true,
        ..Rules::default()
    };
    rewrite(program, inlining, rules, FoldLimits::default(), None);
}

/// Constant folding alone: the walk evaluating what it can, without the
/// identities or algebra.
#[cfg(test)]
pub(crate) fn fold(program: &mut Program) {
    fold_with_limits(program, FoldLimits::default());
}

/// [`fold`], within `limits`.
#[cfg(test)]
pub(crate) fn fold_with_limits(program: &mut Program, limits: FoldLimits) {
    // Nothing to spend evaluates nothing, and the walk is not worth taking.
    if limits.work == 0 || limits.work_per_function == 0 {
        return;
    }
    let rules = Rules {
        evaluate: true,
        ..Rules::default()
    };
    rewrite(program, None, rules, limits, None);
}

/// Evaluate what is known, apply the identities, and combine what is left.
///
/// Each definition is rewritten after what it calls, so a call of one whose
/// answer is known outright is a constant by the time a caller asks, and
/// combining constants sees what evaluating made known in the same walk:
/// recognized addition and multiplication are associative and commutative,
/// so constants separated by one of them can be combined, and what a sum
/// modulo a power of two is worth knowing about cannot be seen until that
/// power is folded. Each definition draws at most a per-definition
/// allowance from one budget, so a costly answer declined in one leaves
/// the rest something to work with.
pub(super) fn simplify(program: &mut Program) {
    rewrite(program, None, SIMPLIFY, FoldLimits::default(), None);
}

/// [`simplify`] again for only `changed`, which a later stage handed
/// something new to read, with a budget of its own.
pub(super) fn resimplify(program: &mut Program, changed: &[FnId]) {
    if changed.is_empty() {
        return;
    }
    rewrite(
        program,
        None,
        SIMPLIFY,
        FoldLimits::default(),
        Some(changed),
    );
}

const SIMPLIFY: Rules = Rules {
    identities: true,
    algebra: true,
    evaluate: true,
};

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

fn rewrite(
    program: &mut Program,
    inlining: Option<Inlining>,
    rules: Rules,
    limits: FoldLimits,
    only: Option<&[FnId]>,
) {
    let recognised = program.recognised().clone();
    let order = order(program, rules, only);
    let mut rewrite = Rewrite {
        program,
        recognised,
        inlining,
        rules,
        budget: Budget::new(limits),
        inline_depth: 0,
        written: Vec::new(),
    };
    let mut remaining = limits.work;
    // Inlining reads existing entries; writes only append. Keep all function
    // roots unchanged until the end, so later callers still inline original
    // bodies using the costs and depth limits computed for those bodies.
    let mut bodies = vec![];
    for id in order {
        if rewrite.recognised.answered(id) {
            continue;
        }
        let Some(body) = rewrite.program.function(id).body() else {
            continue;
        };
        if let Some(inlining) = &mut rewrite.inlining {
            inlining.begin_function();
        }
        let allowance = remaining.min(limits.work_per_function);
        rewrite.budget = Budget::new(FoldLimits {
            work: allowance,
            ..limits
        });
        let count = rewrite.program.params(id).len();
        let locals: Vec<_> = (0..count).map(|at| Atom(Local::at(at))).collect();
        rewrite.written.clear();
        let body = rewrite.body(body, locals, count);
        remaining -= allowance - rewrite.budget.remaining;
        if rewrite.inlining.is_some() {
            bodies.push((id, body));
        } else {
            rewrite.program.replace_bodies(vec![(id, body)]);
        }
    }
    rewrite.program.replace_bodies(bodies);
}

/// The definitions a walk rewrites, `only` where it is given, in the order
/// it rewrites them. Evaluating reads callees as they now stand, so each is
/// rewritten, and published, before what calls it; a single definition
/// needs no order.
fn order(program: &Program, rules: Rules, only: Option<&[FnId]>) -> Vec<FnId> {
    match only {
        Some(&[id]) => vec![id],
        Some(ids) => super::calls::callees_first(program)
            .into_iter()
            .filter(|id| ids.contains(id))
            .collect(),
        None if rules.evaluate => super::calls::callees_first(program),
        None => (0..program.functions().len()).map(FnId::at).collect(),
    }
}

/// The most answers a question of tags is composed through.
const TAG_TREE_LEAVES: usize = 16;

/// Questions about tags, answered with tags.
enum Tags {
    Leaf(super::CtorId),
    /// The local asked about, where the answers are what was asked.
    Same(Atom),
    Split(Atom, Vec<(super::CtorId, Self)>),
}

/// What `map` turns `tag` into, where it turns it.
fn turned(map: &[(super::CtorId, super::CtorId)], tag: super::CtorId) -> Option<super::CtorId> {
    map.iter()
        .find(|&&(ctor, _)| ctor == tag)
        .map(|&(_, answer)| answer)
}

impl Tags {
    /// The same questions, of the locals `locals` gives for each level.
    fn renamed(&self, locals: &[Atom]) -> Self {
        match self {
            Self::Leaf(tag) => Self::Leaf(*tag),
            Self::Same(atom) => Self::Same(locals[atom.0.index()]),
            Self::Split(on, branches) => Self::Split(
                locals[on.0.index()],
                branches
                    .iter()
                    .map(|(ctor, tree)| (*ctor, tree.renamed(locals)))
                    .collect(),
            ),
        }
    }

    /// Each answer turned into another, or nothing where one is not turned.
    fn mapped(&self, to: &dyn Fn(super::CtorId) -> Option<super::CtorId>) -> Option<Self> {
        Some(match self {
            Self::Leaf(tag) => Self::Leaf(to(*tag)?),
            Self::Same(atom) => Self::Same(*atom),
            Self::Split(on, branches) => Self::Split(
                *on,
                branches
                    .iter()
                    .map(|(ctor, tree)| Some((*ctor, tree.mapped(to)?)))
                    .collect::<Option<_>>()?,
            ),
        })
    }

    /// Without questions whose answers agree, or that answer with the tag
    /// asked about.
    fn collapsed(self) -> Self {
        let Self::Split(on, branches) = self else {
            return self;
        };
        let branches: Vec<_> = branches
            .into_iter()
            .map(|(ctor, tree)| (ctor, tree.collapsed()))
            .collect();
        let leaf = |tree: &Self| match tree {
            Self::Leaf(tag) => Some(*tag),
            _ => None,
        };
        let tags: Option<Vec<_>> = branches.iter().map(|(_, tree)| leaf(tree)).collect();
        if let Some(tags) = tags {
            if tags.iter().all(|&tag| tag == tags[0]) {
                return Self::Leaf(tags[0]);
            }
            if branches
                .iter()
                .all(|&(ctor, ref tree)| leaf(tree) == Some(ctor))
            {
                return Self::Same(on);
            }
        }
        Self::Split(on, branches)
    }
}

struct Rewrite<'a> {
    program: &'a mut Program,
    /// Recognised definitions keep their bodies and are called, not
    /// expanded, so what they were recognised as stays true of them.
    recognised: Recognised,
    inlining: Option<Inlining>,
    rules: Rules,
    /// What evaluating and combining constants may still spend in the
    /// definition being rewritten.
    budget: Budget,
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
        } else if let Some(value) = self.known(answer).filter(|_| self.rules.evaluate) {
            // Answering the value itself leaves the local it was written to
            // for nothing to read, where it was written before a match
            // whose other arms do not need it.
            self.program.terms.push(Expr::Static(value))
        } else {
            self.program.terms.push(Expr::Atom(answer))
        };
        self.program.terms.hold_body(&scope.bindings, tail)
    }
    fn into(&mut self, body: Body, locals: Vec<Atom>, scope: &mut Scope) -> Atom {
        let from = body.bindings.range().start;
        self.rest_of(body, from, locals, scope)
    }

    /// The rest of `body`, from its binding at `from`, where `locals` has
    /// what each binding before it came to.
    fn rest_of(
        &mut self,
        body: Body,
        from: usize,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
    ) -> Atom {
        let first = locals.len() - (from - body.bindings.range().start);
        let cased = self.cased(body, first);
        let last = body.bindings.range().end;
        for at in from..last {
            if let Some((scrutinee, first, second)) = cased
                && at + 1 == last
                && !self.decided(locals[scrutinee.0.index()])
            {
                return self.merged(scrutinee, first, second, &locals, scope);
            }
            let binding = self.program.terms.binding(at);
            if let Some(arm) = self.floats(binding, &locals) {
                return self.floated(body, at, arm, locals, scope);
            }
            let value = self.expr(binding, &locals, scope);
            locals.push(value);
        }
        self.expr(body.tail, &locals, scope)
    }

    /// The one arm of a match a binding is, where it takes apart what no
    /// match has yet: see [`Self::floated`].
    fn floats(&self, binding: ExprId, locals: &[Atom]) -> Option<Arm> {
        let Expr::Match(value, arms) = self.program.expr(binding) else {
            return None;
        };
        let &[arm] = self.program.arms(arms) else {
            return None;
        };
        (!self.decided(locals[value.0.index()])).then_some(arm)
    }

    /// Whether a local was written as a constructor or a known value, so
    /// that a match on it takes one arm: see [`Self::selected`].
    fn decided(&self, atom: Atom) -> bool {
        self.written
            .get(atom.0.index())
            .copied()
            .flatten()
            .is_some_and(|wrote| {
                matches!(self.program.expr(wrote), Expr::Con(..) | Expr::Static(..))
            })
    }

    /// A match of one arm, which cannot but take it, taking apart a value
    /// the rest of the body may take apart again: the rest goes on in that
    /// arm, where what it took apart is known, and every match on it again
    /// takes the same arm rather than asking.
    ///
    /// ```text
    /// x = match s                  match s
    ///   U8(n) => .. a                U8(n) =>
    /// y = match s          =>          .. a      (x)
    ///   U8(m) => .. b                  .. b      (y, with m as n)
    /// ```
    fn floated(
        &mut self,
        body: Body,
        at: usize,
        arm: Arm,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
    ) -> Atom {
        let Expr::Match(value, _) = self.program.expr(self.program.terms.binding(at)) else {
            unreachable!("a floated binding is a match");
        };
        let scrutinee = locals[value.0.index()];
        let fields = self.program.fields(arm.ctor).len();
        let taken: Vec<_> = (0..fields)
            .map(|at| Atom(Local::at(scope.level + at)))
            .collect();
        self.written.truncate(scope.level);
        let rest = self.known_as(scrutinee, arm.ctor, &taken, |rewrite| {
            rewrite.body_with(scope.level + fields, |rewrite, arm_scope| {
                let mut inner = locals.clone();
                inner.extend(&taken);
                let value = rewrite.into(arm.body, inner, arm_scope);
                locals.push(value);
                rewrite.rest_of(body, at + 1, locals, arm_scope)
            })
        });
        self.written.truncate(scope.level);
        let arms = self.program.terms.hold_arms(&[Arm {
            ctor: arm.ctor,
            body: rest,
        }]);
        self.push(Expr::Match(scrutinee, arms), scope)
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
        let read = self.program.arms(second).iter().any(|arm| {
            super::walk::reads(
                self.program,
                super::walk::within(self.program, arm.body),
                answer,
            ) > 0
        });
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
                if let Some(held) = self.evaluated(&fields, scope, |evaluator, fields, budget| {
                    evaluator.construct(ctor, &fields, budget)
                }) {
                    return held;
                }
                Expr::Con(ctor, self.program.terms.hold_atoms(fields.into_iter()))
            }
            Expr::Call(called, args) => {
                let args = self.args(args, locals);
                if let Some(held) = self.evaluated(&args, scope, |evaluator, args, budget| {
                    evaluator.call(called, args, budget)
                }) {
                    return held;
                }
                if let Some(held) = self.counted(called, &args, scope) {
                    return held;
                }
                if self.rules.identities
                    && let Some(held) = self.identity(called, &args, scope)
                {
                    return held;
                }
                if let Some(body) = self.callee(called) {
                    self.inline_depth += 1;
                    let answer = self.into(body, args, scope);
                    self.inline_depth -= 1;
                    return answer;
                }
                if self.rules.algebra {
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
                if let Some(answer) = self.evaluated_match(id, scrutinee, locals, scope) {
                    return answer;
                }
                if let Some(answer) = self.composed(scrutinee, arms, scope) {
                    return answer;
                }
                if let Some(answer) = self.composed_within(scrutinee, arms, scope) {
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

    /// A match turning tags into tags, on a local another match wrote out of
    /// tags alone, is one match: the first's questions, each answered with
    /// the tag the second turns its answer into. So `a < b`, which asks an
    /// order and turns it into a truth, asks the comparison itself, and
    /// what a branch on it says of `a` and `b` is seen by range analysis.
    /// Nothing is copied but tags, and a question whose answers agree, or
    /// that answers with what it asked about, is not asked at all.
    fn composed(&mut self, scrutinee: Atom, arms: Range, scope: &mut Scope) -> Option<Atom> {
        let wrote = (*self.written.get(scrutinee.0.index())?)?;
        let inner = self.tag_tree(wrote, TAG_TREE_LEAVES)?;
        let outer = self.tag_map(arms)?;
        let mapped = inner.mapped(&|tag| turned(&outer, tag))?;
        Some(self.emit_tags(mapped.collapsed(), scope))
    }

    /// The same, where the other match works something out in an arm
    /// before it answers with tags, as taking a number apart to compare it
    /// does: that match again, each arm working out what it did and
    /// answering with the tags this one turns its answer into. The first
    /// match is left for cleanup, nothing reading it any more.
    fn composed_within(&mut self, scrutinee: Atom, arms: Range, scope: &mut Scope) -> Option<Atom> {
        let level = scrutinee.0.index();
        let wrote = (*self.written.get(level)?)?;
        let Expr::Match(on, inner) = self.program.expr(wrote) else {
            return None;
        };
        let outer = self.tag_map(arms)?;
        let inner = self.program.arms(inner).to_vec();
        let leaves = TAG_TREE_LEAVES / inner.len().max(1);
        let trees = inner
            .iter()
            .map(|arm| {
                let tree = self.tag_tree(arm.body.tail, leaves)?;
                tree.mapped(&|tag| turned(&outer, tag))
            })
            .collect::<Option<Vec<_>>>()?;
        let mut found = vec![];
        for (arm, tree) in inner.iter().zip(trees) {
            let fields = self.program.fields(arm.ctor).len();
            // What the arm read from outside it is where it was, and it
            // began at the level its match was written at.
            let mut locals: Vec<_> = (0..level).map(|at| Atom(Local::at(at))).collect();
            locals.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
            self.written.truncate(scope.level);
            let body = self.body_with(scope.level + fields, |rewrite, arm_scope| {
                for at in arm.body.bindings.range() {
                    let binding = rewrite.program.terms.binding(at);
                    let value = rewrite.expr(binding, &locals, arm_scope);
                    locals.push(value);
                }
                rewrite.emit_tags(tree.renamed(&locals).collapsed(), arm_scope)
            });
            found.push(Arm {
                ctor: arm.ctor,
                body,
            });
        }
        self.written.truncate(scope.level);
        let arms = self.program.terms.hold_arms(&found);
        Some(self.push(Expr::Match(on, arms), scope))
    }

    /// Whether `a` is below `b`, and if not whether it is `b`, is three
    /// answers, one each for below, equal and above. Where two of them
    /// agree it is one question: below or equal is not above, and above or
    /// below is not equal.
    fn ordered(&mut self, tags: Tags, scope: &mut Scope) -> Tags {
        let Tags::Split(on, ref branches) = tags else {
            return tags;
        };
        let Some((less, a, b)) = self.asked(on) else {
            return tags;
        };
        let Operation::LessThan {
            yes: lt_yes,
            no: lt_no,
        } = less
        else {
            return tags;
        };
        let branch = |ctor| {
            branches
                .iter()
                .find(|&&(tag, _)| tag == ctor)
                .map(|(_, tree)| tree)
        };
        let (Some(Tags::Leaf(below)), Some(rest)) = (branch(lt_yes), branch(lt_no)) else {
            return tags;
        };
        let Some((asked, equal, above)) = self.equality(rest, a, b) else {
            return tags;
        };
        let below = *below;
        if below == above {
            return Tags::Same(asked);
        }
        if below == equal {
            let called = self.called(on).expect("asked is a call");
            let args = self.program.terms.hold_atoms([b, a].into_iter());
            let swapped = self.push(Expr::Call(called, args), scope);
            // The arms in the order the type declares its tags.
            let branches = branches
                .iter()
                .map(|&(tag, _)| (tag, Tags::Leaf(if tag == lt_yes { above } else { below })))
                .collect();
            return Tags::Split(swapped, branches);
        }
        tags
    }

    /// Where `tree` answers whether `a` equals `b`: what asks it, and its
    /// answers for equal and not.
    fn equality(
        &self,
        tree: &Tags,
        a: Atom,
        b: Atom,
    ) -> Option<(Atom, super::CtorId, super::CtorId)> {
        let &Tags::Same(asked) = tree else {
            return None;
        };
        let (Operation::Equals { yes, no }, x, y) = self.asked(asked)? else {
            return None;
        };
        ((x, y) == (a, b) || (x, y) == (b, a)).then_some((asked, yes, no))
    }

    /// The operation a local was written as a call of, with its two
    /// operands.
    fn asked(&self, atom: Atom) -> Option<(Operation, Atom, Atom)> {
        let wrote = (*self.written.get(atom.0.index())?)?;
        let Expr::Call(called, args) = self.program.expr(wrote) else {
            return None;
        };
        let operation = self.recognised.operations[called.index()]?;
        let &[a, b] = self.program.atoms(args) else {
            return None;
        };
        Some((operation, a, b))
    }

    fn called(&self, atom: Atom) -> Option<FnId> {
        let wrote = (*self.written.get(atom.0.index())?)?;
        match self.program.expr(wrote) {
            Expr::Call(called, _) => Some(called),
            _ => None,
        }
    }

    /// The tag each arm of a match answers with, by the tag it takes, where
    /// every arm only answers with one.
    fn tag_map(&self, arms: Range) -> Option<Vec<(super::CtorId, super::CtorId)>> {
        self.program
            .arms(arms)
            .iter()
            .map(|arm| {
                let tag = arm
                    .body
                    .bindings
                    .is_empty()
                    .then(|| self.tag(arm.body.tail))??;
                Some((arm.ctor, tag))
            })
            .collect()
    }

    /// The nullary constructor `expr` builds or knows, where it is one.
    fn tag(&self, expr: ExprId) -> Option<super::CtorId> {
        let ctor = match self.program.expr(expr) {
            Expr::Con(ctor, fields) if fields.is_empty() => ctor,
            Expr::Static(value) => self.program.constant(value).constructor(),
            _ => return None,
        };
        self.program.fields(ctor).is_empty().then_some(ctor)
    }

    /// `expr` as questions about tags answered with tags, of at most
    /// `leaves` answers.
    fn tag_tree(&self, expr: ExprId, leaves: usize) -> Option<Tags> {
        if let Some(tag) = self.tag(expr) {
            return Some(Tags::Leaf(tag));
        }
        let Expr::Match(on, arms) = self.program.expr(expr) else {
            return None;
        };
        let arms = self.program.arms(arms);
        if arms.len() > leaves {
            return None;
        }
        let branches = arms
            .iter()
            .map(|arm| {
                let bare = arm.body.bindings.is_empty() && self.program.fields(arm.ctor).is_empty();
                let tree = bare.then(|| self.tag_tree(arm.body.tail, leaves / arms.len()))??;
                Some((arm.ctor, tree))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Tags::Split(on, branches))
    }

    fn emit_tags(&mut self, tags: Tags, scope: &mut Scope) -> Atom {
        let tags = self.ordered(tags, scope);
        match tags {
            Tags::Leaf(tag) => self.push(Expr::Con(tag, Range::default()), scope),
            Tags::Same(atom) => atom,
            Tags::Split(on, branches) => {
                let arms: Vec<_> = branches
                    .into_iter()
                    .map(|(ctor, tree)| Arm {
                        ctor,
                        body: self.body_with(scope.level, |rewrite, inner| {
                            rewrite.emit_tags(tree, inner)
                        }),
                    })
                    .collect();
                self.written.truncate(scope.level);
                let arms = self.program.terms.hold_arms(&arms);
                self.push(Expr::Match(on, arms), scope)
            }
        }
    }

    /// The length of a sequence written as a known value, which is a number
    /// known too.
    fn counted(&mut self, called: FnId, args: &[Atom], scope: &mut Scope) -> Option<Atom> {
        if self.recognised.sequences[called.index()] != Some(super::SequenceOperation::Length) {
            return None;
        }
        let &[sequence] = args else {
            return None;
        };
        let wrote = (*self.written.get(sequence.0.index())?)?;
        let Expr::Static(value) = self.program.expr(wrote) else {
            return None;
        };
        let value = super::single_field_constant(self.program, self.program.constant(value));
        let super::ConstantView::Spine(spine) = value.view() else {
            return None;
        };
        let length = u64::try_from(spine.length()).ok()?;
        let result = self.program.function(called).result;
        let length = self.program.intern_number(result, length).ok()?;
        Some(self.push(Expr::Static(length), scope))
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
    /// `write`, where `atom` is known to be `ctor` of `fields`: in an arm,
    /// what its match took apart is what the arm took it apart into, and a
    /// match on it again takes that arm.
    fn known_as<T>(
        &mut self,
        atom: Atom,
        ctor: super::CtorId,
        fields: &[Atom],
        write: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let level = atom.0.index();
        let Some(&before) = self.written.get(level) else {
            return write(self);
        };
        let fields = self.program.terms.hold_atoms(fields.iter().copied());
        let known = self.program.terms.push(Expr::Con(ctor, fields));
        self.written[level] = Some(known);
        let written = write(self);
        if let Some(entry) = self.written.get_mut(level) {
            *entry = before;
        }
        written
    }

    /// Rebuild a match's arms: as a match, as the one arm every arm is, or
    /// as its scrutinee where every arm puts back the constructor it took
    /// apart.
    fn matching(&mut self, value: Atom, arms: Range, locals: &[Atom], scope: &Scope) -> Matched {
        let mut found = vec![];
        let scrutinee = locals[value.0.index()];
        for at in arms.range() {
            let arm = self.program.terms.arm(at);
            let fields = self.program.fields(arm.ctor).len();
            let taken: Vec<_> = (0..fields)
                .map(|at| Atom(Local::at(scope.level + at)))
                .collect();
            let mut inner = locals.to_vec();
            inner.extend(&taken);
            // A sibling arm's bindings may have taken this arm's fields'
            // levels, and what wrote them is not what this arm binds.
            self.written.truncate(scope.level);
            let body = self.known_as(scrutinee, arm.ctor, &taken, |rewrite| {
                rewrite.body(arm.body, inner, scope.level + fields)
            });
            found.push(Arm {
                ctor: arm.ctor,
                body,
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

    /// A recognized operation whose answer an identity decides, from which
    /// operands are the same local or known to be nought or one: that
    /// operand, nought, or the comparison's answer. Its argument bindings
    /// stay where they are, so nothing they evaluate is dropped.
    fn identity(&mut self, called: FnId, args: &[Atom], scope: &mut Scope) -> Option<Atom> {
        let op = self.recognised.operations[called.index()]?;
        let &[a, b] = args else {
            return None;
        };
        let (x, y) = (self.small(a), self.small(b));
        let zero = |rewrite: &mut Self, scope: &mut Scope| {
            let result = rewrite.program.function(called).result;
            let zero = rewrite
                .program
                .intern_number(result, 0)
                .expect("a recognized natural result");
            rewrite.push(Expr::Static(zero), scope)
        };
        Some(match op {
            Operation::Add | Operation::Or | Operation::Xor if x == Some(0) => b,
            Operation::Add | Operation::Monus | Operation::Mod | Operation::Or | Operation::Xor
                if y == Some(0) =>
            {
                a
            }
            Operation::Mul if x == Some(1) => b,
            Operation::Mul | Operation::Div | Operation::Pow if y == Some(1) => a,
            Operation::And | Operation::Or if a == b => a,
            Operation::Monus if x == Some(0) => zero(self, scope),
            Operation::Monus | Operation::Xor if a == b => zero(self, scope),
            Operation::Mul | Operation::Div | Operation::And if x == Some(0) || y == Some(0) => {
                zero(self, scope)
            }
            Operation::Mod if x == Some(0) || y == Some(1) || a == b => zero(self, scope),
            Operation::Equals { yes, .. } if a == b => {
                self.push(Expr::Con(yes, Range::default()), scope)
            }
            Operation::LessThan { no, .. } if a == b => {
                self.push(Expr::Con(no, Range::default()), scope)
            }
            // In particular x/x is NOT one: x can be zero.
            _ => return None,
        })
    }

    /// Whether a local is a natural known to be nought or one: written as
    /// that number, or as nought or the step of nought.
    fn small(&self, atom: Atom) -> Option<u8> {
        let wrote = (*self.written.get(atom.0.index())?)?;
        match self.program.expr(wrote) {
            Expr::Static(value) => {
                let super::ConstantView::Natural(number) = self.program.constant(value).view()
                else {
                    return None;
                };
                match number.try_u64() {
                    Ok(0) => Some(0),
                    Ok(1) => Some(1),
                    _ => None,
                }
            }
            Expr::Con(ctor, fields) => {
                let (nil, _) =
                    super::arithmetic::natural(self.program, self.program.ctor(ctor).owner)?;
                if ctor == nil {
                    Some(0)
                } else if self.small(self.program.atoms(fields)[0]) == Some(0) {
                    Some(1)
                } else {
                    None
                }
            }
            Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => None,
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
        let budget = &mut self.budget;
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

    /// What `evaluate` answers for `args`, written as a known value, where
    /// the walk evaluates and every one of `args` is known. A refusal --
    /// an input known only as it runs, a call with no body, or the budget --
    /// leaves the expression to be written as it was.
    fn evaluated(
        &mut self,
        args: &[Atom],
        scope: &mut Scope,
        evaluate: impl FnOnce(&Evaluator, Vec<Held>, &mut Budget) -> Evaluation,
    ) -> Option<Atom> {
        if !self.rules.evaluate || self.budget.remaining == 0 {
            return None;
        }
        let known = args
            .iter()
            .map(|&atom| self.known(atom))
            .collect::<Option<Vec<_>>>()?;
        let budget = &mut self.budget;
        let values = known
            .into_iter()
            .map(|value| self.program.constant(value).to_owned(budget))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let evaluator = Evaluator {
            program: self.program,
            operations: &self.recognised.operations,
        };
        let value = evaluate(&evaluator, values, budget).ok()?;
        let value = self.program.intern_held(&value);
        Some(self.push(Expr::Static(value), scope))
    }

    /// A match on a known value [`Self::selected`] does not take apart, a
    /// sequence, evaluated whole, where the walk evaluates: the arm it takes
    /// may read only what is known. Opening the sequence instead would hold
    /// its rest as a second known value, a copy of all but one element.
    fn evaluated_match(
        &mut self,
        id: ExprId,
        scrutinee: Atom,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Option<Atom> {
        if !self.rules.evaluate || self.budget.remaining == 0 {
            return None;
        }
        self.known(scrutinee)?;
        // Only what the match reads from outside it is worth copying out.
        let mut read = vec![false; locals.len()];
        for expr in super::walk::nested(self.program, [id]) {
            for atom in super::walk::operands(self.program, expr) {
                if let Some(read) = read.get_mut(atom.0.index()) {
                    *read = true;
                }
            }
        }
        let known: Vec<_> = locals
            .iter()
            .zip(read)
            .map(|(&atom, read)| self.known(atom).filter(|_| read))
            .collect();
        let budget = &mut self.budget;
        let mut env = Vec::with_capacity(known.len());
        for value in known {
            let held = match value {
                Some(value) => Ok(self.program.constant(value).to_owned(budget).ok()?),
                None => Err(CannotFold::DynamicInput),
            };
            env.push(held);
        }
        let evaluator = Evaluator {
            program: self.program,
            operations: &self.recognised.operations,
        };
        let value = evaluator.expr(id, &env, budget).ok()?;
        let value = self.program.intern_held(&value);
        Some(self.push(Expr::Static(value), scope))
    }

    /// The known value a local was written as, in this scope or one
    /// around it.
    fn known(&self, atom: Atom) -> Option<super::ConstId> {
        let wrote = (*self.written.get(atom.0.index())?)?;
        let Expr::Static(value) = self.program.expr(wrote) else {
            return None;
        };
        Some(value)
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
