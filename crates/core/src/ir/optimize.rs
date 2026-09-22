//! A deliberately small, bounded schedule over machine IR.
//!
//! Lowering answers one question at a time -- what a value can be, what a
//! constructor is, what a routine reads -- and a tier that answers one
//! question at a time writes things a tier reading the whole program would
//! not. Recognising those here keeps lowering saying one thing per place,
//! and keeps every target from finding the same shapes out for itself.
//!
//! Each stage runs at most once, in this order. Nothing here is a fixed
//! point, and nothing here changes what a program means.

use super::{Program, prune, simplify};

/// Deterministic pass controls, for saying which stage did what.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptimizeOptions {
    /// Recognise the shapes lowering leaves behind.
    pub simplify: bool,
    /// Drop what nothing reads, including what `simplify` stopped reading.
    pub prune: bool,
}

impl Default for OptimizeOptions {
    fn default() -> Self {
        Self {
            simplify: true,
            prune: true,
        }
    }
}

/// Rewrite a validated program.
///
/// Validation must precede this: a pass reads a program as structurally
/// sound and says nothing useful about one that is not. Values, instructions
/// and regions are renumbered, so nothing held across this call names the
/// same thing afterwards. Data, globals, names and function IDs do.
#[must_use]
pub fn optimize(program: &Program, options: &OptimizeOptions) -> Program {
    let mut held = if options.simplify {
        simplify::simplify(program)
    } else {
        program.clone()
    };
    if options.prune {
        held = prune::prune(&held);
    }
    held
}
