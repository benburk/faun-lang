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
/// 1. Canonicalization: structural normalization of every body, before
///    anything is recognized, then again with what is. Float operations
///    are recognized by their code in between.
/// 2. Forward list construction.
/// 3. Descent over natural numbers.
/// 4. Constants: each taking nothing and doing work is folded, left where
///    it runs at most once, or worked out once in the entry and handed down.
/// 5. Helper inlining with arithmetic identities.
/// 6. Producer/consumer fusion.
/// 7. First-element demand specialization.
/// 8. List walks expressed through functional replacements.
/// 9. Simplification, including constant evaluation and identities.
/// 10. Specialization for constructions handed to a definition that takes
///     them apart, then for known arguments, resimplifying changed
///     definitions.
/// 11. Joining recursive rounds through helper inlining.
/// 12. Reachability sweep.
/// 13. Effect-safe cleanup.
///
/// Recognized induction equations are left intact. Cleanup removes aliases
/// and unused pure bindings while preserving observable calls. Inlining and
/// folding use fixed work budgets.
///
/// Cleanup rebuilds the term pools: discard saved expression IDs and body or
/// range handles. Declaration and constant IDs are preserved.
pub fn optimize(program: &mut Program) {
    super::canonical(program);
    super::floats::recognise(program);
    super::structural(program);
    super::forward::forward(program);
    super::descent::descend(program);
    super::once::once(program);
    super::normalize::inline_with_identities(program, InlineLimits::default());
    super::fuse::fuse(program);
    super::head::heads(program);
    super::inplace::in_place(program);
    super::normalize::simplify(program);
    super::unbuilt::constructions(program);
    super::specialize::specialize(program);
    super::normalize::join_rounds(program);
    super::sweep::sweep(program);
    super::cleanup::cleanup(program);
}
