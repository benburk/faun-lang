//! Small affine summaries for recognized natural arithmetic.
//!
//! These are facts about existing five-node Barb terms, not another term
//! language. They stop at nonlinear products and at a small term count, so
//! analysis never expands a general polynomial.

use super::{Atom, ConstantView, Expr, ExprId, FnId, Local, Operation, Program};

/// Enough independent terms for ordinary indexes, offsets and small formulas
/// without turning this into a symbolic-algebra system.
const TERM_LIMIT: usize = 8;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Affine {
    pub constant: u64,
    pub terms: Vec<(Atom, u64)>,
}

impl Affine {
    fn atom(atom: Atom) -> Self {
        Self {
            constant: 0,
            terms: vec![(atom, 1)],
        }
    }

    const fn constant(value: u64) -> Self {
        Self {
            constant: value,
            terms: Vec::new(),
        }
    }

    fn plus(mut self, other: Self) -> Option<Self> {
        self.constant = self.constant.checked_add(other.constant)?;
        for (atom, coefficient) in other.terms {
            if let Some((_, held)) = self.terms.iter_mut().find(|(held, _)| *held == atom) {
                *held = held.checked_add(coefficient)?;
            } else {
                if self.terms.len() == TERM_LIMIT {
                    return None;
                }
                self.terms.push((atom, coefficient));
            }
        }
        self.terms.sort_by_key(|(atom, _)| atom.0.index());
        Some(self)
    }

    fn scaled(mut self, coefficient: u64) -> Option<Self> {
        self.constant = self.constant.checked_mul(coefficient)?;
        for (_, held) in &mut self.terms {
            *held = held.checked_mul(coefficient)?;
        }
        self.terms.retain(|(_, held)| *held != 0);
        Some(self)
    }

    fn number(&self) -> Option<u64> {
        self.terms.is_empty().then_some(self.constant)
    }
}

/// Derive one summary per expression where every lexical occurrence agrees.
pub(super) fn analyze(program: &Program, operations: &[Option<Operation>]) -> Vec<Option<Affine>> {
    let mut analysis = Analysis {
        program,
        operations,
        found: vec![Finding::Unseen; program.exprs_count()],
    };
    for (at, operation) in operations.iter().enumerate() {
        let id = FnId::at(at);
        if operation.is_some() {
            continue;
        }
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let scope = (0..program.params(id).len())
            .map(|at| Affine::atom(Atom(Local::at(at))))
            .collect();
        analysis.body(body, scope);
    }
    analysis
        .found
        .into_iter()
        .map(|found| match found {
            Finding::Unseen => None,
            Finding::Seen(held) => held,
        })
        .collect()
}

#[derive(Clone)]
enum Finding {
    Unseen,
    Seen(Option<Affine>),
}

struct Analysis<'a> {
    program: &'a Program,
    operations: &'a [Option<Operation>],
    found: Vec<Finding>,
}

impl Analysis<'_> {
    fn body(&mut self, body: super::Body, mut scope: Vec<Affine>) -> Option<Affine> {
        for &binding in self.program.bindings(body.bindings) {
            let held = self.expr(binding, &scope);
            let local = Atom(Local::at(scope.len()));
            scope.push(held.unwrap_or_else(|| Affine::atom(local)));
        }
        self.expr(body.tail, &scope)
    }

    fn expr(&mut self, id: ExprId, scope: &[Affine]) -> Option<Affine> {
        let held = match self.program.expr(id) {
            Expr::Atom(atom) => Some(scope[atom.0.index()].clone()),
            Expr::Static(value) => match self.program.constant(value).view() {
                ConstantView::Natural(number) => number.try_u64().ok().map(Affine::constant),
                ConstantView::Constructor(_) | ConstantView::Spine(_) => None,
            },
            Expr::Call(called, args) => self.call(called, args, scope),
            Expr::Match(_, arms) => {
                for arm in self.program.arms(arms) {
                    let mut inner = scope.to_vec();
                    inner.extend(
                        (0..self.program.fields(arm.ctor).len())
                            .map(|at| Affine::atom(Atom(Local::at(scope.len() + at)))),
                    );
                    self.body(arm.body, inner);
                }
                None
            }
            // Constructor arithmetic is left to lowering. Recognized calls
            // are the canonical semantic boundary this analysis needs.
            Expr::Con(..) => None,
        };
        self.record(id, held.clone());
        held
    }

    fn call(&self, called: FnId, args: super::Range, scope: &[Affine]) -> Option<Affine> {
        let [left, right] = self.program.atoms(args) else {
            return None;
        };
        let (left, right) = (
            scope[left.0.index()].clone(),
            scope[right.0.index()].clone(),
        );
        match self.operations[called.index()]? {
            Operation::Add => left.plus(right),
            Operation::Mul => match (left.number(), right.number()) {
                (Some(coefficient), _) => right.scaled(coefficient),
                (_, Some(coefficient)) => left.scaled(coefficient),
                (None, None) => None,
            },
            Operation::Monus
            | Operation::Div
            | Operation::Mod
            | Operation::And
            | Operation::Or
            | Operation::Xor
            | Operation::Pow
            | Operation::Equals { .. }
            | Operation::LessThan { .. } => None,
        }
    }

    fn record(&mut self, id: ExprId, held: Option<Affine>) {
        let slot = &mut self.found[id.index()];
        match slot {
            Finding::Unseen => *slot = Finding::Seen(held),
            Finding::Seen(found) if *found == held => {}
            Finding::Seen(_) => *slot = Finding::Seen(None),
        }
    }
}
