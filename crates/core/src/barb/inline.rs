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
            total: 1_048_576,
            max_depth: 32,
        }
    }
}

/// Only expanding rewrites need call-graph analysis, copy costs and budgets.
pub(super) struct Inlining {
    /// The definitions a call of is never expanded, which keeps every
    /// expansion finite.
    breakers: Vec<bool>,
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
            breakers: super::stops::breakers(program),
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
            || self.breakers[called.index()]
        {
            return None;
        }
        let body = program.function(called).body()?;
        self.function_left -= cost;
        self.total_left -= cost;
        Some(body)
    }
}

/// Unrolling: a call of a definition calling itself is expanded where it is
/// handed a known value for the parameter the definition takes apart before
/// anything else. The walk then takes the arm that value selects, with its
/// fields known too, so the call on what is left of it is one more of these,
/// and a loop over a known list or count is laid out a step at a time.
///
/// Each expansion of a definition inside another of the same one must be
/// handed a smaller value, so the walk ends; the copies a definition may
/// take bound how much of one is laid out, and a loop over more than that
/// is left calling itself on the rest.
pub(super) struct Unrolling {
    /// Which parameter each definition takes apart first, where it calls
    /// itself and does.
    opens: Vec<Option<usize>>,
    costs: Vec<usize>,
    function_left: usize,
    /// The definitions being expanded, innermost last, each with the size of
    /// the known value it was handed.
    active: Vec<(FnId, usize)>,
}

/// What unrolling may copy into one definition.
const UNROLLED: usize = 65_536;
/// How deep unrolled expansions nest, which the rewriter walks on its stack.
const UNROLL_DEPTH: usize = 128;

impl Unrolling {
    pub(super) fn new(program: &Program) -> Self {
        let breakers = super::stops::breakers(program);
        let opens = program
            .functions()
            .iter()
            .zip(breakers)
            .map(|(function, breaker)| {
                let body = function.body().filter(|_| breaker)?;
                if !body.bindings.is_empty() {
                    return None;
                }
                match program.expr(body.tail) {
                    Expr::Match(on, _) if on.0.index() < function.params.len() => {
                        Some(on.0.index())
                    }
                    _ => None,
                }
            })
            .collect();
        Self {
            opens,
            costs: program
                .functions()
                .iter()
                .map(|f| f.body().map_or(0, |body| cost(program, body)))
                .collect(),
            function_left: 0,
            active: Vec::new(),
        }
    }

    pub(super) const fn begin_function(&mut self) {
        self.function_left = UNROLLED;
    }

    /// The parameter a call of `called` would have to be handed a known
    /// value for.
    pub(super) fn opens(&self, called: FnId) -> Option<usize> {
        self.opens[called.index()]
    }

    /// A permitted expansion of `called`, handed a known value of `size`
    /// bytes to take apart, charged before the rewriter copies its body.
    /// The caller ends it with [`Self::finish`].
    pub(super) fn begin(&mut self, program: &Program, called: FnId, size: usize) -> Option<Body> {
        let cost = self.costs[called.index()];
        let smaller = self
            .active
            .iter()
            .rev()
            .find(|(active, _)| *active == called)
            .is_none_or(|&(_, before)| size < before);
        if !smaller || cost > self.function_left || self.active.len() >= UNROLL_DEPTH {
            return None;
        }
        let body = program.function(called).body()?;
        self.function_left -= cost;
        self.active.push((called, size));
        Some(body)
    }

    pub(super) fn finish(&mut self) {
        self.active.pop();
    }
}

// Count expressions, bindings, argument slots and arms which copying a body
// can allocate. Nested expansions pay separately; aliases may cost less than
// this conservative estimate. This walk does not recurse on the Rust stack.
pub(super) fn cost(program: &Program, body: Body) -> usize {
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
