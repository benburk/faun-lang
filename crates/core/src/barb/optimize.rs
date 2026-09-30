//! A deliberately small, bounded schedule, not a fixed-point optimizer.

use super::{FoldLimits, InlineLimits, Program};

/// Optimize a validated program.
///
/// Validation must precede this: laws and evaluation must not hide a
/// malformed definition. A definition may never come back; a pass may leave
/// out pure work nothing needs, and nothing else, as the module's rules say.
///
/// Each stage runs once, in this order: structural normalization, building
/// lists front to back, descent,
/// helper inlining, fusion, arithmetic laws, constant folding, copies of a
/// loop for the known values its callers hand it, invariant arguments and
/// folding again where they bound something, algebraic
/// normalization, the sweep and cleanup. Recognized induction equations are left intact. Cleanup removes
/// aliases and unused inert bindings, never calls or matches whose
/// evaluation may have effects. Inlining and folding stop at their fixed
/// budgets, which bound work rather than choose what is done.
///
/// Cleanup rebuilds the term pools: discard saved expression IDs and body or
/// range handles. Declaration and constant IDs are preserved.
pub fn optimize(program: &mut Program) {
    super::structural(program);
    super::forward::forward(program);
    super::descent::descend(program);
    super::normalize_with_limits(program, InlineLimits::default());
    super::fuse::fuse(program);
    super::laws::laws(program);
    super::fold(program);
    super::specialize::specialize(program);
    // What a definition now holds itself may fold what reads it.
    let held = super::invariant::invariant(program);
    super::fold::refold(program, &held);
    super::normalize::algebra(program, FoldLimits::default());
    super::sweep::sweep(program);
    super::cleanup::cleanup(program);
}
