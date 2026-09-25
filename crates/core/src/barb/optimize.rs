//! A deliberately small, bounded schedule, not a fixed-point optimizer.

use super::{FoldLimits, InlineLimits, Program};

/// Optimize a validated program. Validation/totality must precede this: laws
/// and evaluation must not hide a malformed or nonterminating definition.
///
/// Each stage runs once, in this order: structural normalization, descent,
/// helper inlining, fusion, arithmetic laws, constant folding, invariant
/// arguments, algebraic normalization, the sweep and cleanup. Recognized induction equations are left intact. Cleanup removes
/// aliases and unused inert bindings, never calls or matches whose
/// evaluation may have effects. Inlining and folding stop at their fixed
/// budgets, which bound work rather than choose what is done.
///
/// Cleanup rebuilds the term pools: discard saved expression IDs and body or
/// range handles. Declaration and constant IDs are preserved.
pub fn optimize(program: &mut Program) {
    super::structural(program);
    super::descent::descend(program);
    super::normalize_with_limits(program, InlineLimits::default());
    super::fuse::fuse(program);
    super::laws::laws(program);
    super::fold(program);
    super::invariant::invariant(program);
    super::normalize::algebra(program, FoldLimits::default());
    super::sweep::sweep(program);
    super::cleanup::cleanup(program);
}
