//! A deliberately small, bounded schedule, not a fixed-point optimizer.

use super::{FoldLimits, InlineLimits, Program};

/// Deterministic pass controls. Disabling helpers can reduce backend range
/// knowledge (and hence representability), but does not change Barb semantics.
// Independent ablation switches, not mutually exclusive states.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptimizeOptions {
    pub structural: bool,
    pub inline_helpers: bool,
    pub arithmetic_laws: bool,
    pub constant_fold: bool,
    pub cleanup: bool,
    pub inline_limits: InlineLimits,
    pub fold_limits: FoldLimits,
}

impl Default for OptimizeOptions {
    fn default() -> Self {
        Self {
            structural: true,
            inline_helpers: true,
            arithmetic_laws: true,
            constant_fold: true,
            cleanup: true,
            inline_limits: InlineLimits::default(),
            fold_limits: FoldLimits::default(),
        }
    }
}

/// Optimize a validated program. Validation/totality must precede this: laws
/// and evaluation must not hide a malformed or nonterminating definition.
///
/// Each stage runs at most once, in this order. Recognized induction equations
/// are left intact. Cleanup removes aliases and unused inert bindings, never
/// calls or matches whose evaluation may have effects.
///
/// Cleanup rebuilds the term pools: discard saved expression IDs, body/range
/// handles and analysis facts after optimization. Declaration and constant IDs
/// are preserved.
pub fn optimize(program: &mut Program, options: &OptimizeOptions) {
    if options.structural {
        super::structural(program);
    }
    if options.inline_helpers {
        super::normalize_with_limits(program, options.inline_limits);
    }
    if options.arithmetic_laws {
        super::laws::laws(program);
    }
    if options.constant_fold {
        super::fold_with_limits(program, options.fold_limits);
    }
    if options.cleanup {
        super::cleanup::cleanup(program);
    }
}
