//! Helper-expansion policy and budgets, separate from structural rebuilding.

use super::{Body, Expr, FnId, Program};

/// Copied arena entries, rather than call count, bound helper expansion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InlineLimits {
    pub max_callee: usize,
    pub per_function: usize,
    pub total: usize,
    pub max_depth: usize,
}

impl Default for InlineLimits {
    fn default() -> Self {
        Self {
            max_callee: 256,
            per_function: 4096,
            total: 65_536,
            max_depth: 32,
        }
    }
}

/// Only expanding rewrites need call-graph analysis, copy costs and budgets.
pub(super) struct Inlining {
    recursive: Vec<bool>,
    costs: Vec<usize>,
    limits: InlineLimits,
    function_left: usize,
    total_left: usize,
}

impl Inlining {
    pub(super) fn new(program: &Program, limits: InlineLimits) -> Option<Self> {
        if limits.total == 0
            || limits.per_function == 0
            || limits.max_callee == 0
            || limits.max_depth == 0
        {
            return None;
        }
        Some(Self {
            recursive: super::stops::recursive(program),
            costs: program
                .functions()
                .iter()
                .map(|f| f.body().map_or(0, |body| cost(program, body)))
                .collect(),
            limits,
            function_left: 0,
            total_left: limits.total,
        })
    }

    pub(super) const fn begin_function(&mut self) {
        self.function_left = self.limits.per_function;
    }

    /// A permitted expansion, charged before the rewriter copies its body.
    /// The caller protects recognized arithmetic definitions separately.
    pub(super) fn callee(&mut self, program: &Program, called: FnId, depth: usize) -> Option<Body> {
        let cost = self.costs[called.index()];
        if depth >= self.limits.max_depth
            || cost > self.limits.max_callee
            || cost > self.function_left
            || cost > self.total_left
            || self.recursive[called.index()]
        {
            return None;
        }
        let body = program.function(called).body()?;
        self.function_left -= cost;
        self.total_left -= cost;
        Some(body)
    }
}

// Count expressions, bindings, argument slots and arms which copying a body
// can allocate. Nested expansions pay separately; aliases may cost less than
// this conservative estimate. This walk does not recurse on the Rust stack.
fn cost(program: &Program, body: Body) -> usize {
    let mut pending = vec![body];
    let mut cost = 0usize;
    while let Some(body) = pending.pop() {
        cost = cost.saturating_add(program.bindings(body.bindings).len());
        // One possible alias tail is manufactured for each copied body.
        cost = cost.saturating_add(1);
        for &id in program
            .bindings(body.bindings)
            .iter()
            .chain(std::iter::once(&body.tail))
        {
            cost = cost.saturating_add(1);
            match program.expr(id) {
                Expr::Con(_, args) | Expr::Call(_, args) => cost = cost.saturating_add(args.len()),
                Expr::Match(_, arms) => {
                    cost = cost.saturating_add(arms.len());
                    pending.extend(program.arms(arms).iter().map(|a| a.body));
                }
                Expr::Atom(_) | Expr::Static(..) => {}
            }
        }
    }
    cost
}
