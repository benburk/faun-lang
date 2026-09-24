//! Backward liveness for inert bindings, followed by capture-free renaming.
//! Matches and calls of unknown meaning are retained even when their answers
//! are unused. A structurally recognized arithmetic call is pure and total,
//! so it is inert. Dropping a constructor never drops eager opaque calls that
//! produced its fields.
//! Rebuild into fresh term pools, then replace the old pools in one commit.
//! Declarations and constants stay in place; expression IDs and ranges change.

use super::terms::TermArena;
use std::collections::HashMap;

use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range};

pub(super) fn cleanup(program: &mut Program) {
    let operations = program.operations().to_vec();
    let mut rewrite = Rewrite {
        source: program,
        terms: TermArena::default(),
        copied: HashMap::new(),
    };
    let mut bodies = vec![];
    // Every definition is a root, not just the entry or its reachable callees.
    for (at, op) in operations.iter().enumerate() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let body = if op.is_some() {
            // Protected equations need new pool references, but no rewriting.
            rewrite.copy_body(body)
        } else {
            let count = program.params(id).len();
            let (plan, _) = plan_body(program, &operations, body, count);
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
    bindings: Vec<Option<PlannedExpr>>,
    tail: PlannedExpr,
}
struct PlannedExpr {
    id: ExprId,
    arms: Vec<PlannedBody>,
}

fn plan_body(
    program: &Program,
    operations: &[Option<super::Operation>],
    body: Body,
    base: usize,
) -> (PlannedBody, Vec<bool>) {
    let bindings = program.bindings(body.bindings);
    let mut live = vec![false; base + bindings.len()];
    let tail = plan_expr(program, operations, body.tail, &mut live);
    let mut kept = Vec::with_capacity(bindings.len());
    for &id in bindings.iter().rev() {
        let needed = live.pop().expect("one local per binding");
        let eager = match program.expr(id) {
            Expr::Call(called, _) => operations[called.index()].is_none(),
            Expr::Match(..) => true,
            Expr::Atom(..) | Expr::Static(..) | Expr::Con(..) => false,
        };
        kept.push((needed || eager).then(|| plan_expr(program, operations, id, &mut live)));
    }
    kept.reverse();
    (
        PlannedBody {
            bindings: kept,
            tail,
        },
        live,
    )
}

fn plan_expr(
    program: &Program,
    operations: &[Option<super::Operation>],
    id: ExprId,
    live: &mut [bool],
) -> PlannedExpr {
    let mut children = vec![];
    match program.expr(id) {
        Expr::Atom(a) => live[a.0.index()] = true,
        Expr::Static(..) => {}
        Expr::Con(_, args) | Expr::Call(_, args) => {
            for a in program.atoms(args) {
                live[a.0.index()] = true;
            }
        }
        Expr::Match(value, arms) => {
            live[value.0.index()] = true;
            for arm in program.arms(arms) {
                let base = live.len() + program.fields(arm.ctor).len();
                let (plan, captures) = plan_body(program, operations, arm.body, base);
                // Fields are local to this arm, not captures of its parent.
                for (used, captured) in live.iter_mut().zip(captures) {
                    *used |= captured;
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
        let tail = self.terms.push(expr);
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
