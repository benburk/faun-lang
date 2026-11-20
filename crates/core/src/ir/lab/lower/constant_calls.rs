//! A call to a function whose body only answers numbers it writes is those
//! numbers. Lowering writes such a body where the tier above proved every
//! arm but one unreachable, as a list's tail compared with nothing once
//! the caller has proven it empty; leaving the call costs its frame and the
//! arguments worked out for it, and the function, inlined, does nothing.

use std::collections::BTreeMap;

use crate::ir::rewrite::{self, Pass, Rebuild};
use crate::ir::{Builder, Exit, FunctionId, Op, Program, RegionId, ValueId};

/// `program`, each call to a function answering only constants replaced by
/// them.
pub(super) fn answered_in_place(program: &Program) -> Program {
    let answers: BTreeMap<_, _> = program
        .functions()
        .iter()
        .enumerate()
        .filter_map(|(at, function)| {
            let answers = constants_returned(program, function.body()?)?;
            Some((FunctionId::at(at), answers))
        })
        .collect();
    if answers.is_empty() {
        return program.clone();
    }
    rewrite::rebuild(program, &mut Answered(answers))
}

/// What a body answers, where it writes nothing but constants and returns
/// them.
fn constants_returned(program: &Program, body: RegionId) -> Option<Vec<u64>> {
    let region = program.region(body);
    let terminator = region.terminator.filter(|t| t.exit == Exit::Return)?;
    let mut written = BTreeMap::new();
    for (op, results) in program.walk(body) {
        let Op::Constant { value } = *op else {
            return None;
        };
        written.insert(results[0], value);
    }
    program
        .values(terminator.values)
        .iter()
        .map(|value| written.get(value).copied())
        .collect()
}

struct Answered(BTreeMap<FunctionId, Vec<u64>>);

impl Pass for Answered {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let Op::Call { function, .. } = op else {
            return false;
        };
        let Some(answers) = self.0.get(&function) else {
            return false;
        };
        for ((&old, class), &answer) in results.iter().zip(rebuild.classes(results)).zip(answers) {
            rebuild.stands_for(old, b.constant(class, answer));
        }
        true
    }
}
