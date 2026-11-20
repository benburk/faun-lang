//! Constants, worked out once.
//!
//! A definition taking nothing is a constant: whatever calls it, it answers
//! the same. Called as a definition it is worked out again at every call,
//! and one named inside a walk, as a lookup table is, is built again every
//! round. So each constant that does any work is settled here, before
//! inlining can copy it into the walks that name it:
//!
//! - **Folded,** where it can be worked out now within the folding budget:
//!   its body becomes the value, and a tier below lays it out before the
//!   program runs, as it does a literal.
//! - **Left alone,** where it runs at most once anyway: named at one call,
//!   in a definition itself made at most once, so in no walk. Inlining may
//!   then copy it where it is read and fuse it with what reads it, as
//!   `List.range(n).map(f).sum()` is fused.
//! - **Handed down** otherwise. The entry works it out once, before what
//!   reads it, and every definition reaching a call of it takes it as one
//!   more parameter, reading that where it called the constant:
//!
//! ```text
//! k = table(..)                   main(h) = k = table(..); .. step(k, x) ..
//! step(x) = .. k() .. step(x')    step(x, k) = .. k .. step(x', k)
//! main(h) = .. step(x) ..
//! ```
//!
//! A parameter passed on as it came is borrowed: the entry holds the
//! constant, and every round reads it without counting it. Nothing is held
//! in a static place, so nothing needs marking as never freed or never
//! written: the count does what it does for any value, a write in place
//! copying it while anything else still holds it, and the last claim
//! freeing it once nothing still running can read it.
//!
//! The entry binds each constant before the body it had, and cleanup then
//! moves the binding into the one arm that reads it, where only one does.
//! A constant only some paths read may still be worked out on a path that
//! does not: that is the price of working it out once, as in a strict
//! language's top-level bindings. It is pure, so it does nothing else; one
//! that would not come back hangs the program before the work that read it.

use std::collections::BTreeSet;

use super::budget::{Budget, FoldLimits};
use super::copy::{self, Scope};
use super::evaluate::Evaluator;
use super::{Atom, Expr, ExprId, FnId, Local, Program};

/// Settle every constant the entry reaches: fold it, leave it to be
/// inlined where it runs once, or work it out in the entry and hand it
/// down.
pub(super) fn once(program: &mut Program) {
    let entry = program.entry();
    let reached = super::sweep::reached(program, entry).0;
    let candidates = constants(program, entry, &reached);
    if candidates.is_empty() {
        return;
    }
    let left = fold(program, candidates);
    let mut handed = repeated(program, entry, &reached, &left);
    loop {
        if handed.is_empty() {
            return;
        }
        let needs = needs(program, &handed);
        // A definition answered as what it was recognized as, rather than
        // by its body, keeps the signature it was recognized by.
        let recognised = program.recognised();
        let blocked: BTreeSet<usize> = needs
            .iter()
            .enumerate()
            .filter(|&(at, _)| recognised.answered(FnId::at(at)))
            .flat_map(|(_, needed)| needed.iter().copied())
            .collect();
        if blocked.is_empty() {
            hand_down(program, entry, &handed, &needs);
            return;
        }
        handed = handed
            .into_iter()
            .enumerate()
            .filter(|(at, _)| !blocked.contains(at))
            .map(|(_, id)| id)
            .collect();
    }
}

/// The constants the entry reaches that do some work: pure definitions
/// taking nothing, calling something, and not reaching themselves. One
/// answering a type no value has never answers at all, and stands where
/// the program cannot go, so it is left there.
fn constants(program: &mut Program, entry: FnId, reached: &[bool]) -> Vec<FnId> {
    let recognised = program.recognised().clone();
    let pure = super::calls::pure(program, &recognised);
    let recursive = super::calls::recursive(program);
    super::calls::callees_first(program)
        .into_iter()
        .filter(|&id| {
            let function = program.function(id);
            id != entry
                && reached[id.index()]
                && pure[id.index()]
                && !recursive[id.index()]
                && !recognised.answered(id)
                && program.params(id).is_empty()
                && !matches!(
                    super::type_shape(program, function.result),
                    super::TypeShape::Uninhabited
                )
                && function.body().is_some_and(|body| {
                    super::walk::within(program, body)
                        .any(|expr| matches!(program.expr(expr), Expr::Call(..)))
                })
        })
        .collect()
}

/// Work out each of `candidates` that can be within the folding budget,
/// callees first, making its body the value; the rest, in the same order.
fn fold(program: &mut Program, candidates: Vec<FnId>) -> Vec<FnId> {
    let limits = FoldLimits::default();
    let mut remaining = limits.work;
    let mut left = Vec::new();
    for id in candidates {
        let operations = program.recognised().operations.clone();
        let body = program.function(id).body().expect("a constant has a body");
        let allowance = remaining.min(limits.work_per_function);
        let mut budget = Budget::new(FoldLimits {
            work: allowance,
            ..limits
        });
        let evaluator = Evaluator {
            program,
            operations: &operations,
        };
        let answer = evaluator.body(body, Vec::new(), &mut budget);
        remaining -= allowance - budget.remaining;
        match answer {
            Ok(held) => {
                let value = program.intern_held(&held);
                let mut scope = Scope::at(0);
                let answer = copy::push(program, &mut scope, Expr::Static(value));
                let body = copy::close(program, scope, answer);
                program.replace_bodies(vec![(id, body)]);
            }
            Err(_) => left.push(id),
        }
    }
    left
}

/// Which of `constants` may be worked out more than once: named at more
/// than one call, or at one in a definition that may itself be made more
/// than once.
fn repeated(program: &Program, entry: FnId, reached: &[bool], constants: &[FnId]) -> Vec<FnId> {
    let callers = callers(program, reached);
    let once = made_once(program, entry, reached);
    constants
        .iter()
        .copied()
        .filter(|id| !callers[id.index()].is_empty() && !once[id.index()])
        .collect()
}

/// Each definition's callers among those `reached`, one entry per call.
fn callers(program: &Program, reached: &[bool]) -> Vec<Vec<FnId>> {
    let mut callers: Vec<Vec<FnId>> = vec![Vec::new(); program.functions().len()];
    for (at, &reached) in reached.iter().enumerate() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body().filter(|_| reached) else {
            continue;
        };
        for expr in super::walk::within(program, body) {
            if let Expr::Call(callee, _) = program.expr(expr) {
                callers[callee.index()].push(id);
            }
        }
    }
    callers
}

/// Which definitions are made at most once, by definition. One is where it
/// is the entry, or is called at one place only, by one made at most once;
/// a body runs each of its calls at most once, since a walk is a definition
/// calling itself.
pub(super) fn made_once(program: &Program, entry: FnId, reached: &[bool]) -> Vec<bool> {
    let callers = callers(program, reached);
    let mut once = vec![false; callers.len()];
    once[entry.index()] = true;
    let mut changed = true;
    while changed {
        changed = false;
        for (at, callers) in callers.iter().enumerate() {
            if !once[at]
                && let [caller] = callers[..]
                && caller.index() != at
                && once[caller.index()]
            {
                once[at] = true;
                changed = true;
            }
        }
    }
    once
}

/// For each definition, which of `handed` (by place) it must be handed:
/// those it calls, and those what it calls must be handed, but for a
/// constant handed down, which the definition reads rather than calls.
/// Definitions the entry does not reach count too: every call of one given
/// parameters must pass them, wherever it is, until the sweep.
fn needs(program: &Program, handed: &[FnId]) -> Vec<BTreeSet<usize>> {
    let calls = super::calls::graph(program);
    let mut needs = vec![BTreeSet::new(); calls.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for (at, callees) in calls.iter().enumerate() {
            let mut needed = needs[at].clone();
            for callee in callees {
                if let Some(place) = handed.iter().position(|id| id == callee) {
                    needed.insert(place);
                } else {
                    needed.extend(needs[callee.index()].iter().copied());
                }
            }
            if needed.len() != needs[at].len() {
                needs[at] = needed;
                changed = true;
            }
        }
    }
    needs
}

/// What handing constants down needs to know: which constants, which each
/// definition needs, and how many parameters each took before.
struct Handing<'a> {
    entry: FnId,
    handed: &'a [FnId],
    needs: &'a [BTreeSet<usize>],
    original: Vec<usize>,
}

/// Work out in the entry each of `handed` it needs, each after those it
/// needs itself, and give every other definition needing some those as
/// parameters, reading them where it called them and passing them on where
/// it calls another needing them.
fn hand_down(program: &mut Program, entry: FnId, handed: &[FnId], needs: &[BTreeSet<usize>]) {
    let handing = Handing {
        entry,
        handed,
        needs,
        original: (0..needs.len())
            .map(|at| program.params(FnId::at(at)).len())
            .collect(),
    };
    let rewritten: Vec<FnId> = (0..needs.len())
        .map(FnId::at)
        .filter(|&id| id == entry || !needs[id.index()].is_empty())
        .filter(|&id| program.function(id).body().is_some())
        .collect();
    // Every definition needing one is given its parameters before any body
    // is rewritten, so nothing is read in between.
    for &id in rewritten.iter().filter(|&&id| id != entry) {
        let extra: Vec<_> = needs[id.index()]
            .iter()
            .map(|&place| {
                let constant = program.function(handed[place]);
                (program.name(constant.name).to_owned(), constant.result)
            })
            .collect();
        let extra: Vec<_> = extra
            .iter()
            .map(|(name, ty)| (name.as_str(), *ty))
            .collect();
        program.add_params(id, &extra);
    }
    let bodies = rewritten
        .into_iter()
        .map(|id| (id, handing.body(program, id, id == entry)))
        .collect();
    program.replace_bodies(bodies);
}

impl Handing<'_> {
    /// `id`'s body, rewritten: in the entry, working out first each
    /// constant it needs; elsewhere, reading each from its parameters.
    fn body(&self, program: &mut Program, id: FnId, entry: bool) -> super::Body {
        let body = program
            .function(id)
            .body()
            .expect("a rewritten definition has a body");
        let params = self.original[id.index()];
        let locals: Vec<Atom> = (0..params).map(|at| Atom(Local::at(at))).collect();
        // Where each constant this definition needs is held.
        let mut held: Vec<Option<Atom>> = vec![None; self.handed.len()];
        let mut scope;
        if entry {
            scope = Scope::at(params);
            for place in self.order(id) {
                let args = self.needs[self.handed[place].index()]
                    .iter()
                    .map(|&needed| held[needed].expect("a constant after what it needs"));
                let args = program.terms.hold_atoms(args);
                let call = Expr::Call(self.handed[place], args);
                held[place] = Some(copy::push(program, &mut scope, call));
            }
        } else {
            for (at, &place) in self.needs[id.index()].iter().enumerate() {
                held[place] = Some(Atom(Local::at(params + at)));
            }
            scope = Scope::at(params + self.needs[id.index()].len());
        }
        let mut edit = |program: &mut Program, _: &mut Scope, _: ExprId, expr: Expr| -> Expr {
            self.call(program, &held, expr)
        };
        let answer = copy::into(program, body, locals, &mut scope, Some(&mut edit));
        copy::close(program, scope, answer)
    }

    /// What `expr` becomes where each constant is `held`: a constant read
    /// rather than called, and a definition needing some handed them.
    fn call(&self, program: &mut Program, held: &[Option<Atom>], expr: Expr) -> Expr {
        let Expr::Call(callee, args) = expr else {
            return expr;
        };
        if let Some(place) = self.handed.iter().position(|&id| id == callee) {
            return Expr::Atom(held[place].expect("a constant read where it is held"));
        }
        // The entry works its constants out itself, whoever calls it.
        let needed = &self.needs[callee.index()];
        if needed.is_empty() || callee == self.entry {
            return expr;
        }
        let mut atoms = program.atoms(args).to_vec();
        atoms.extend(
            needed
                .iter()
                .map(|&place| held[place].expect("a constant passed on")),
        );
        Expr::Call(callee, program.terms.hold_atoms(atoms.into_iter()))
    }

    /// The constants the entry `id` needs, each after those it needs.
    fn order(&self, id: FnId) -> Vec<usize> {
        let mut order = Vec::new();
        let mut placed = vec![false; self.handed.len()];
        for &place in &self.needs[id.index()] {
            settle(place, self.handed, self.needs, &mut placed, &mut order);
        }
        order
    }
}

/// Place `place` in `order` after every constant it needs.
fn settle(
    place: usize,
    handed: &[FnId],
    needs: &[BTreeSet<usize>],
    placed: &mut [bool],
    order: &mut Vec<usize>,
) {
    if placed[place] {
        return;
    }
    placed[place] = true;
    for &needed in &needs[handed[place].index()] {
        settle(needed, handed, needs, placed, order);
    }
    order.push(place);
}
