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
//!
//! Preparation for a target runs the schedule again once legalization has
//! written the runtime: its offsets are arithmetic on sizes known before the
//! program runs, which only then is at a width the program says.

use super::{Program, prune, simplify};

/// Rewrite a validated program: recognise the shapes lowering leaves
/// behind, then drop what nothing reads, including what that stopped
/// reading.
///
/// Validation must precede this: a pass reads a program as structurally
/// sound and says nothing useful about one that is not. Values, instructions
/// and regions are renumbered, so nothing held across this call names the
/// same thing afterwards. Data, globals, names and function IDs do.
#[must_use]
pub fn optimize(program: &Program) -> Program {
    prune::prune(&simplify::simplify(program))
}
