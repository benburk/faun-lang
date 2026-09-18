//! What is known of a program beyond what it says.
//!
//! barb states what a program computes. Deciding how to compute it needs a
//! few things barb does not spell, and this records them once so that every
//! later decision reads them here rather than rediscovering them.
//!
//! So far that is one thing: which definitions compute an operation the
//! tiers below already have. `add` written as recursion over a constructor
//! is addition, and knowing so lets the machine tier emit an instruction
//! where the program wrote a recursive call. A fold or a constant folder
//! would read the same entry.

use super::bounds::{Bounds, Known};
use super::constant::{Shape, shape};
use super::ir::{Atom, Expr, ExprId, FnId, Local, Program};

/// An operation the tiers below have a name for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Add,
}

/// What is known of each function, by function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Facts {
    operations: Vec<Option<Operation>>,
    known: Known,
}

impl Facts {
    /// The operation a function computes, when it computes one.
    #[must_use]
    pub fn operation(&self, id: FnId) -> Option<Operation> {
        self.operations.get(id.index()).copied().flatten()
    }

    /// What a term answers.
    #[must_use]
    pub fn held(&self, id: ExprId) -> Bounds {
        self.known
            .terms
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }

    /// What a definition is handed, by parameter.
    #[must_use]
    pub fn takes(&self, id: FnId) -> &[Bounds] {
        self.known.takes.get(id.index()).map_or(&[], Vec::as_slice)
    }

    /// And what it answers.
    #[must_use]
    pub fn answers(&self, id: FnId) -> Bounds {
        self.known
            .answers
            .get(id.index())
            .copied()
            .unwrap_or(Bounds::ANY)
    }
}

/// Read what can be read off every definition.
#[must_use]
pub fn recognise(program: &Program) -> Facts {
    let operations: Vec<Option<Operation>> = (0..program.functions().len())
        .map(|at| operation(program, FnId::at(at)))
        .collect();
    // What a definition computes is read first, since what a number can be
    // is worked out through the operations rather than around them.
    let known = super::bounds::walk(program, &operations);
    Facts { operations, known }
}

/// Addition, as counting one argument down onto the other:
///
/// ```text
/// add(a, b) = match b { Zero => a; Succ(k) => Succ(add(a, k)) }
/// ```
///
/// Either argument may be the one counted down; the other rides through
/// untouched, which is what makes this addition rather than something else
/// shaped like it.
fn operation(program: &Program, id: FnId) -> Option<Operation> {
    let function = program.function(id);
    let [left, right] = program.params(id) else {
        return None;
    };
    if left != right || function.result != *left {
        return None;
    }
    let Shape::Spine { nil, cons, .. } = shape(program, *left) else {
        return None;
    };
    if program.fields(cons).len() != 1 {
        return None;
    }

    // The body is the match itself, over one of the two parameters.
    let body = function.body?;
    if !program.bindings(body.bindings).is_empty() {
        return None;
    }
    let Expr::Match(scrutinee, arms) = program.expr(body.tail) else {
        return None;
    };
    let counted = u32::try_from(scrutinee.0.index()).ok()?;
    if counted > 1 {
        return None;
    }
    let kept = 1 - counted;

    let arms = program.arms(arms);
    let empty = arms.iter().find(|arm| arm.ctor == nil)?;
    let step = arms.iter().find(|arm| arm.ctor == cons)?;

    // Nothing left to add: the other parameter, untouched.
    if !program.bindings(empty.body.bindings).is_empty()
        || program.expr(empty.body.tail) != Expr::Atom(Atom(Local(kept)))
    {
        return None;
    }
    counts_down(program, id, step, cons, counted).then_some(Operation::Add)
}

/// One less to add: the same call on the predecessor, wrapped back up. The
/// predecessor takes level two, and the call after it level three.
fn counts_down(
    program: &Program,
    id: FnId,
    step: &super::ir::Arm,
    cons: super::ir::CtorId,
    counted: u32,
) -> bool {
    let &[call] = program.bindings(step.body.bindings) else {
        return false;
    };
    let Expr::Call(callee, args) = program.expr(call) else {
        return false;
    };
    let carried = if counted == 0 {
        [Atom(Local(2)), Atom(Local(1))]
    } else {
        [Atom(Local(0)), Atom(Local(2))]
    };
    if callee != id || program.atoms(args) != carried {
        return false;
    }
    let Expr::Con(built, fields) = program.expr(step.body.tail) else {
        return false;
    };
    built == cons && program.atoms(fields) == [Atom(Local(3))]
}
