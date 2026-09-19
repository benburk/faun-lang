//! Bounded, capture-free inlining of nonrecursive helpers. In particular a
//! comparison followed by a selector becomes a match in the same scope, so
//! range analysis can connect the condition to its operands. ANF arguments
//! are evaluated once; no bodyless call is duplicated or moved across arms.

use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range};

pub fn normalize(program: &mut Program) {
    let source = program.clone();
    let operations = super::arithmetic::recognise(&source);
    let recursive = super::stops::recursive(&source);
    let mut rewrite = Rewrite {
        source: &source,
        program,
        recursive,
        operations,
        fuel: 0,
    };
    for at in 0..source.functions().len() {
        let id = FnId::at(at);
        if rewrite.operations[at].is_some() {
            continue;
        }
        let Some(body) = source.function(id).body else {
            continue;
        };
        rewrite.fuel = 1024;
        let count = source.params(id).len();
        let locals: Vec<_> = (0..count).map(|at| Atom(Local::at(at))).collect();
        let body = rewrite.body(body, locals, count);
        rewrite.program.functions[at].body = Some(body);
    }
}

struct Rewrite<'a> {
    source: &'a Program,
    program: &'a mut Program,
    recursive: Vec<bool>,
    operations: Vec<Option<super::Operation>>,
    fuel: usize,
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
            self.push(Expr::Atom(answer))
        };
        let start = self.program.bindings.len();
        self.program.bindings.extend_from_slice(&scope.bindings);
        Body {
            bindings: Range::of(start, scope.bindings.len()),
            tail,
        }
    }
    fn into(&mut self, body: Body, mut locals: Vec<Atom>, scope: &mut Scope) -> Atom {
        for &binding in self.source.bindings(body.bindings) {
            let value = self.expr(binding, &locals, scope);
            locals.push(value);
        }
        self.expr(body.tail, &locals, scope)
    }
    fn expr(&mut self, id: ExprId, locals: &[Atom], scope: &mut Scope) -> Atom {
        let expr = match self.source.expr(id) {
            Expr::Atom(a) => return locals[a.0.index()],
            Expr::Static(..) => self.source.expr(id),
            Expr::Con(ctor, fields) => {
                let fields = self.args(fields, locals);
                Expr::Con(ctor, self.hold(&fields))
            }
            Expr::Call(called, args) => {
                let args = self.args(args, locals);
                if self.fuel > 0
                    && !self.recursive[called.index()]
                    && self.operations[called.index()].is_none()
                    && let Some(body) = self.source.function(called).body
                {
                    self.fuel -= 1;
                    return self.into(body, args, scope);
                }
                Expr::Call(called, self.hold(&args))
            }
            Expr::Match(value, arms) => {
                let mut found = vec![];
                for arm in self.source.arms(arms) {
                    let fields = self.source.fields(arm.ctor).len();
                    let mut inner = locals.to_vec();
                    inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
                    found.push(Arm {
                        ctor: arm.ctor,
                        body: self.body(arm.body, inner, scope.level + fields),
                    });
                }
                let start = self.program.arms.len();
                self.program.arms.extend_from_slice(&found);
                Expr::Match(locals[value.0.index()], Range::of(start, found.len()))
            }
        };
        let id = self.push(expr);
        scope.bindings.push(id);
        let value = Atom(Local::at(scope.level));
        scope.level += 1;
        value
    }
    fn args(&self, args: Range, locals: &[Atom]) -> Vec<Atom> {
        self.source
            .atoms(args)
            .iter()
            .map(|a| locals[a.0.index()])
            .collect()
    }
    fn hold(&mut self, args: &[Atom]) -> Range {
        let start = self.program.atoms.len();
        self.program.atoms.extend_from_slice(args);
        Range::of(start, args.len())
    }
    fn push(&mut self, expr: Expr) -> ExprId {
        let id = ExprId::at(self.program.exprs.len());
        self.program.exprs.push(expr);
        id
    }
}
