//! Storage for terms, independent of declarations and rewrite policy.
//!
//! Runs remain contiguous and expressions keep stable IDs while appending.
//! Replacing the arena invalidates those IDs and ranges; Program coordinates
//! replacement with the remapped function roots. IDs remain unbranded, and
//! construction still assumes well-formed references and lexical scopes.

use super::{Arm, Atom, Body, Expr, ExprId, Range};
use crate::index::{Pool, append_range};

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct TermArena {
    exprs: Pool<ExprId, Expr>,
    atoms: Vec<Atom>,
    bindings: Vec<ExprId>,
    arms: Vec<Arm>,
}

impl TermArena {
    pub(super) fn expr(&self, id: ExprId) -> Expr {
        self.exprs[id]
    }

    pub(super) const fn exprs_count(&self) -> usize {
        self.exprs.len()
    }

    pub(super) fn write(&mut self, id: ExprId, expr: Expr) {
        self.exprs[id] = expr;
    }

    pub(super) fn atoms(&self, range: Range) -> &[Atom] {
        &self.atoms[range.range()]
    }

    pub(super) fn bindings(&self, range: Range) -> &[ExprId] {
        &self.bindings[range.range()]
    }

    pub(super) fn arms(&self, range: Range) -> &[Arm] {
        &self.arms[range.range()]
    }

    // Mutating walks copy one stable slot before appending or rewriting.
    pub(super) fn binding(&self, at: usize) -> ExprId {
        self.bindings[at]
    }

    pub(super) fn arm(&self, at: usize) -> Arm {
        self.arms[at]
    }

    pub(super) fn push(&mut self, expr: Expr) -> ExprId {
        self.exprs.push(expr)
    }

    /// Accept copied or mapped arguments without requiring a temporary vector.
    /// Check the run before writing; a panicking iterator is not rolled back.
    pub(super) fn hold_atoms(&mut self, atoms: impl ExactSizeIterator<Item = Atom>) -> Range {
        let range = Range::of(self.atoms.len(), atoms.len());
        self.atoms.extend(atoms);
        range
    }

    pub(super) fn hold_body(&mut self, bindings: &[ExprId], tail: ExprId) -> Body {
        Body {
            bindings: append_range(&mut self.bindings, bindings),
            tail,
        }
    }

    pub(super) fn hold_arms(&mut self, arms: &[Arm]) -> Range {
        append_range(&mut self.arms, arms)
    }
}
