//! Backward liveness for inert bindings, followed by capture-free renaming.
//! Calls and matches are always retained, even when their answers are unused.
//! Dropping a constructor never drops the eager calls that produced its fields.

use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range};

pub(super) fn cleanup(program: &mut Program) {
    let source = program.clone();
    let operations = super::arithmetic::recognise(&source);
    let mut rewrite = Rewrite {
        source: &source,
        program,
    };
    for (at, op) in operations.iter().enumerate() {
        if op.is_some() {
            continue;
        }
        let id = FnId::at(at);
        let Some(body) = source.function(id).body else {
            continue;
        };
        let count = source.params(id).len();
        let (plan, _) = plan_body(&source, body, count);
        let locals = (0..count).map(|at| Some(Atom(Local::at(at)))).collect();
        let body = rewrite.body(plan, locals, count);
        rewrite.program.functions[at].body = Some(body);
    }
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

fn plan_body(program: &Program, body: Body, base: usize) -> (PlannedBody, Vec<bool>) {
    let bindings = program.bindings(body.bindings);
    let mut live = vec![false; base + bindings.len()];
    let tail = plan_expr(program, body.tail, &mut live);
    let mut kept = Vec::with_capacity(bindings.len());
    for &id in bindings.iter().rev() {
        let needed = live.pop().expect("one local per binding");
        let eager = matches!(program.expr(id), Expr::Call(..) | Expr::Match(..));
        kept.push((needed || eager).then(|| plan_expr(program, id, &mut live)));
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

fn plan_expr(program: &Program, id: ExprId, live: &mut [bool]) -> PlannedExpr {
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
                let (plan, captures) = plan_body(program, arm.body, base);
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
    program: &'a mut Program,
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
                bindings.push(self.push(expr));
                let value = Atom(Local::at(level));
                level += 1;
                value
            });
            locals.push(value);
        }
        let expr = self.expr(plan.tail, &locals, level);
        let tail = self.push(expr);
        let start = self.program.bindings.len();
        self.program.bindings.extend_from_slice(&bindings);
        Body {
            bindings: Range::of(start, bindings.len()),
            tail,
        }
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
                let start = self.program.arms.len();
                self.program.arms.extend_from_slice(&found);
                Expr::Match(local(locals, value), Range::of(start, found.len()))
            }
        }
    }

    fn args(&mut self, args: Range, locals: &[Option<Atom>]) -> Range {
        let start = self.program.atoms.len();
        self.program
            .atoms
            .extend(self.source.atoms(args).iter().map(|&a| local(locals, a)));
        Range::of(start, args.len())
    }

    fn push(&mut self, expr: Expr) -> ExprId {
        let id = ExprId::at(self.program.exprs.len());
        self.program.exprs.push(expr);
        id
    }
}

fn local(locals: &[Option<Atom>], a: Atom) -> Atom {
    locals[a.0.index()].expect("a retained expression reads only live locals")
}
