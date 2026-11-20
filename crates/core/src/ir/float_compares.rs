//! A float comparison a machine cannot make itself, as one on bit
//! patterns: for an emitter that selects no instruction for
//! [`Relation::FloatNotAbove`].

use super::rewrite::{self, Pass, Rebuild};
use super::{Builder, Op, Program, Relation, ValueId};

/// `program`, each [`Relation::FloatNotAbove`] compared on IEEE bit
/// patterns instead.
#[must_use]
pub fn expand_float_compares(program: &Program) -> Program {
    let compares = program.ops.iter().any(|op| {
        matches!(
            op,
            Op::Compare {
                relation: Relation::FloatNotAbove(_),
                ..
            }
        )
    });
    if !compares {
        return program.clone();
    }
    rewrite::rebuild(program, &mut Expanded)
}

struct Expanded;

impl Pass for Expanded {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let Op::Compare {
            relation: Relation::FloatNotAbove(format),
            left,
            right,
        } = op
        else {
            return false;
        };
        let held = b.float_not_above_in_bits(format, rebuild.value(left), rebuild.value(right));
        rebuild.stands_for(results[0], held);
        true
    }
}
