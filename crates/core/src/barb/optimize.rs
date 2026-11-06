//! A deliberately small, bounded schedule, not a fixed-point optimizer.

use super::{InlineLimits, Program};

/// Optimize a validated program.
///
/// Validation must precede this: laws and evaluation must not hide a
/// malformed definition. A definition may never come back; a pass may leave
/// out pure work nothing needs, and nothing else, as the module's rules say.
///
/// Each stage runs once, in this order: structural normalization, building
/// lists front to back, descent, helper inlining with arithmetic
/// identities, fusion, writing a walk over a list in place, simplification -- evaluating what is known, the
/// identities and combining constants, in one walk -- copies of a loop for
/// the known values its callers hand it and the values they all hand alike,
/// simplified again where they bound something, joining what still calls
/// round through another definition, the sweep and cleanup. Recognized induction equations are left intact. Cleanup removes
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
    super::normalize::inline_with_identities(program, InlineLimits::default());
    super::fuse::fuse(program);
    super::head::heads(program);
    super::inplace::in_place(program);
    super::normalize::simplify(program);
    super::specialize::specialize(program);
    super::normalize::join_rounds(program);
    super::sweep::sweep(program);
    super::cleanup::cleanup(program);
}
