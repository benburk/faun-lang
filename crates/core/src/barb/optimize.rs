//! A deliberately small, bounded schedule, not a fixed-point optimizer.

use super::{InlineLimits, Program};

/// Optimize a validated program.
///
/// Validation must precede this: laws and evaluation must not hide a
/// malformed definition. A definition may never come back; a pass may leave
/// out pure work nothing needs, and nothing else, as the module's rules say.
///
/// The outer schedule runs once, in this order:
///
/// 1. Structural normalization.
/// 2. Forward list construction.
/// 3. Descent over natural numbers.
/// 4. Helper inlining with arithmetic identities.
/// 5. Producer/consumer fusion.
/// 6. First-element demand specialization.
/// 7. List walks expressed through functional replacements.
/// 8. Simplification, including constant evaluation and identities.
/// 9. Specialization for known arguments, resimplifying changed definitions.
/// 10. Joining recursive rounds through helper inlining.
/// 11. Reachability sweep.
/// 12. Effect-safe cleanup.
///
/// Recognized induction equations are left intact. Cleanup removes aliases
/// and unused pure bindings while preserving observable calls. Inlining and
/// folding use fixed work budgets.
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
