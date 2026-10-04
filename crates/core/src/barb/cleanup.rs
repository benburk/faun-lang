//! Backward liveness for inert bindings, followed by capture-free renaming.
//! A call of a definition reaching an external routine is retained even
//! when its answer is unused. A call of a pure one -- a recognized
//! operation, or a definition reaching no external routine -- is inert, and
//! so is a match whose every arm is: it answers whichever arm it takes.
//! Dropping a constructor never drops eager calls reaching external
//! routines that produced its fields.
//!
//! An inert binding is worked out only on the paths that read it: one read
//! only inside one arm of a later match moves to the top of that arm, and
//! what it reads may follow it there. Each run moves work one match down.
//! Rebuild into fresh term pools, then replace the old pools in one commit.
//! Declarations and constants stay in place; expression IDs and ranges change.

use super::terms::TermArena;
use std::collections::HashMap;

use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range};

pub(super) fn cleanup(program: &mut Program) {
    let recognised = program.recognised().clone();
    let mut inert = Inert {
        pure: super::calls::pure(program, &recognised),
        known: HashMap::new(),
    };
    let mut rewrite = Rewrite {
        source: program,
        terms: TermArena::default(),
        copied: HashMap::new(),
    };
    let mut bodies = vec![];
    // Every definition is a root, not just the entry or its reachable callees.
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let body = if recognised.answered(id) {
            // Protected equations need new pool references, but no rewriting.
            rewrite.copy_body(body)
        } else {
            let count = program.params(id).len();
            let (plan, _) = plan_body(program, &mut inert, body, count);
            let locals = (0..count).map(|at| Some(Atom(Local::at(at)))).collect();
            rewrite.body(plan, locals, count)
        };
        bodies.push((id, body));
    }
    program.replace_terms(rewrite.terms, bodies);
}

// Plans belong to occurrences, not ExprIds: an arena expression can be used
// in different lexical scopes. Only retained matches have child body plans.
struct PlannedBody {
    /// Bindings of an enclosing body moved to the top of this one, each
    /// with the local it bound there, last first.
    sunk: Vec<(usize, PlannedExpr)>,
    bindings: Vec<Option<PlannedExpr>>,
    tail: PlannedExpr,
}

struct PlannedExpr {
    id: ExprId,
    arms: Vec<PlannedBody>,
}

/// Where a body's local is read, as far as that body can tell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Read {
    Unread,
    /// Only inside one arm of the match the body binds or answers at `site`:
    /// a binding's index, or the number of bindings for the tail.
    InArm {
        site: usize,
        arm: usize,
    },
    /// Anywhere else, or in more than one arm.
    Here,
}

impl Read {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unread, read) | (read, Self::Unread) => read,
            (read, other) if read == other => read,
            _ => Self::Here,
        }
    }
}

/// Which expressions may go unevaluated where nothing reads them, found
/// once for each: an expression is inert wherever it stands.
struct Inert {
    /// Indexed by definition: see [`super::calls::pure`].
    pure: Vec<bool>,
    known: HashMap<ExprId, bool>,
}

impl Inert {
    fn is(&mut self, program: &Program, id: ExprId) -> bool {
        if let Some(&known) = self.known.get(&id) {
            return known;
        }
        let inert = match program.expr(id) {
            Expr::Call(called, _) => self.pure[called.index()],
            Expr::Match(_, arms) => program.arms(arms).iter().all(|arm| {
                program
                    .bindings(arm.body.bindings)
                    .iter()
                    .chain([&arm.body.tail])
                    .all(|&inner| self.is(program, inner))
            }),
            Expr::Atom(..) | Expr::Static(..) | Expr::Con(..) => true,
        };
        self.known.insert(id, inert);
        inert
    }
}

/// Plan `body`, whose first `base` locals are its enclosing scope's, and
/// say which of those it reads.
fn plan_body(
    program: &Program,
    inert: &mut Inert,
    body: Body,
    base: usize,
) -> (PlannedBody, Vec<bool>) {
    let bindings = program.bindings(body.bindings);
    let mut reads = vec![Read::Unread; base + bindings.len()];
    let mut tail = plan_expr(program, inert, body.tail, &mut reads, bindings.len(), None);
    let mut kept: Vec<Option<PlannedExpr>> = (0..bindings.len()).map(|_| None).collect();
    for (index, &id) in bindings.iter().enumerate().rev() {
        let read = reads.pop().expect("one local per binding");
        match (read, inert.is(program, id)) {
            (Read::Unread, true) => {}
            (Read::InArm { site, arm }, true) => {
                let planned = plan_expr(program, inert, id, &mut reads, index, Some((site, arm)));
                let target = if site == bindings.len() {
                    &mut tail
                } else {
                    kept[site]
                        .as_mut()
                        .expect("a binding read in an arm is kept")
                };
                target.arms[arm].sunk.push((base + index, planned));
            }
            _ => kept[index] = Some(plan_expr(program, inert, id, &mut reads, index, None)),
        }
    }
    let captures = reads.iter().map(|&read| read != Read::Unread).collect();
    (
        PlannedBody {
            sunk: vec![],
            bindings: kept,
            tail,
        },
        captures,
    )
}

/// Plan the expression at `site` of the body `reads` belongs to, which
/// stands there or, where `within` says, at the top of an arm of a later
/// match, where every local it reads is read too.
fn plan_expr(
    program: &Program,
    inert: &mut Inert,
    id: ExprId,
    reads: &mut [Read],
    site: usize,
    within: Option<(usize, usize)>,
) -> PlannedExpr {
    let here = within.map_or(Read::Here, |(site, arm)| Read::InArm { site, arm });
    let read = |reads: &mut [Read], a: Atom, as_read: Read| {
        let at = &mut reads[a.0.index()];
        *at = at.and(as_read);
    };
    let mut children = vec![];
    match program.expr(id) {
        Expr::Atom(a) => read(reads, a, here),
        Expr::Static(..) => {}
        Expr::Con(_, args) | Expr::Call(_, args) => {
            for &a in program.atoms(args) {
                read(reads, a, here);
            }
        }
        Expr::Match(value, arms) => {
            read(reads, value, here);
            for (index, arm) in program.arms(arms).iter().enumerate() {
                let in_arm = within.map_or(Read::InArm { site, arm: index }, |_| here);
                let base = reads.len() + program.fields(arm.ctor).len();
                let (plan, captures) = plan_body(program, inert, arm.body, base);
                // Fields are local to this arm, not captures of its parent.
                for (at, captured) in captures.into_iter().enumerate().take(reads.len()) {
                    if captured {
                        reads[at] = reads[at].and(in_arm);
                    }
                }
                children.push(plan);
            }
        }
    }
    PlannedExpr { id, arms: children }
}

struct Rewrite<'a> {
    source: &'a Program,
    terms: TermArena,
    // Copying protected equations is context-free, unlike liveness rewriting.
    // Preserve expression sharing there, including shared match subtrees.
    copied: HashMap<ExprId, ExprId>,
}

impl Rewrite<'_> {
    fn body(&mut self, plan: PlannedBody, mut locals: Vec<Option<Atom>>, mut level: usize) -> Body {
        let mut bindings = vec![];
        // Moved here from an enclosing body, they come first, in the order
        // they were written, each read in the scope it was written in: the
        // locals before its own, which a match's fields are numbered after.
        for (local, sunk) in plan.sunk.into_iter().rev() {
            let value = if let Expr::Atom(a) = self.source.expr(sunk.id) {
                self::local(&locals, a)
            } else {
                let expr = self.expr(sunk, &locals[..local], level);
                bindings.push(self.terms.push(expr));
                level += 1;
                Atom(Local::at(level - 1))
            };
            locals[local] = Some(value);
        }
        for binding in plan.bindings {
            let value = binding.map(|binding| {
                if let Expr::Atom(a) = self.source.expr(binding.id) {
                    return local(&locals, a);
                }
                let expr = self.expr(binding, &locals, level);
                bindings.push(self.terms.push(expr));
                let value = Atom(Local::at(level));
                level += 1;
                value
            });
            locals.push(value);
        }
        let expr = self.expr(plan.tail, &locals, level);
        // A body answering its last binding is that binding's expression.
        let tail = match expr {
            Expr::Atom(answer) if answer.0.index() + 1 == level && !bindings.is_empty() => {
                bindings.pop().expect("the last binding")
            }
            _ => self.terms.push(expr),
        };
        self.terms.hold_body(&bindings, tail)
    }

    fn expr(&mut self, plan: PlannedExpr, locals: &[Option<Atom>], level: usize) -> Expr {
        match self.source.expr(plan.id) {
            Expr::Atom(a) => Expr::Atom(local(locals, a)),
            value @ Expr::Static(..) => value,
            Expr::Con(ctor, args) => Expr::Con(ctor, self.args(args, locals)),
            Expr::Call(called, args) => Expr::Call(called, self.args(args, locals)),
            Expr::Match(value, arms) => {
                let mut found = vec![];
                for (arm, body) in self.source.arms(arms).iter().zip(plan.arms) {
                    let fields = self.source.fields(arm.ctor).len();
                    let mut inner = locals.to_vec();
                    inner.extend((0..fields).map(|at| Some(Atom(Local::at(level + at)))));
                    found.push(Arm {
                        ctor: arm.ctor,
                        body: self.body(body, inner, level + fields),
                    });
                }
                Expr::Match(local(locals, value), self.terms.hold_arms(&found))
            }
        }
    }

    fn args(&mut self, args: Range, locals: &[Option<Atom>]) -> Range {
        self.terms
            .hold_atoms(self.source.atoms(args).iter().map(|&a| local(locals, a)))
    }

    fn copy_body(&mut self, body: Body) -> Body {
        let bindings: Vec<_> = self
            .source
            .bindings(body.bindings)
            .iter()
            .map(|&id| self.copy_expr(id))
            .collect();
        let tail = self.copy_expr(body.tail);
        self.terms.hold_body(&bindings, tail)
    }

    fn copy_expr(&mut self, id: ExprId) -> ExprId {
        if let Some(&copied) = self.copied.get(&id) {
            return copied;
        }
        let expr = match self.source.expr(id) {
            value @ (Expr::Atom(_) | Expr::Static(..)) => value,
            Expr::Con(ctor, args) => Expr::Con(ctor, self.copy_args(args)),
            Expr::Call(called, args) => Expr::Call(called, self.copy_args(args)),
            Expr::Match(value, arms) => {
                let arms: Vec<_> = self
                    .source
                    .arms(arms)
                    .iter()
                    .map(|arm| Arm {
                        ctor: arm.ctor,
                        body: self.copy_body(arm.body),
                    })
                    .collect();
                Expr::Match(value, self.terms.hold_arms(&arms))
            }
        };
        let copied = self.terms.push(expr);
        self.copied.insert(id, copied);
        copied
    }

    fn copy_args(&mut self, args: Range) -> Range {
        self.terms
            .hold_atoms(self.source.atoms(args).iter().copied())
    }
}

fn local(locals: &[Option<Atom>], a: Atom) -> Atom {
    locals[a.0.index()].expect("a retained expression reads only live locals")
}
