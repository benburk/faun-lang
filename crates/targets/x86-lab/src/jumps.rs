//! Jumps the way lowering writes them, taken the way a reader would.
//!
//! Each structured branch is written without knowing what stands next to
//! it: an arm ends by jumping to where the branch joins, and the join may be
//! the next instruction, or another jump on to somewhere else. Read as a
//! whole, a jump to a jump is a jump to where the second goes, a jump to the
//! next instruction is nothing, and a conditional jump over one other jump is
//! that jump, taken the other way. What follows a jump or a return, up to
//! the next place anything may jump to, is never reached.
//!
//! An edge's copies are a few moves and a jump, so a way through several
//! edges jumps from run to run. Where one jump alone reaches such a run, and
//! nothing falls into it, the run takes that jump's place, and the run left
//! behind is reached by nothing: one jump fewer on the way, and no code
//! added.
//!
//! Nothing a jump or a call lands on is dropped, and nothing before the
//! first jump or return, so every place control may reach stays where it
//! was, and so does the entry, which is the first instruction.

use std::collections::HashSet;

use super::machine::Inst;
use faun_core::targets::code::{Code, Label};

/// The most instructions a jump is replaced by, beside the jump or return
/// that ends them.
const COPIED: usize = 2;

/// Rewrite `code` until none of those shapes is left.
pub(crate) fn thread(code: &mut Code<Inst>) {
    // Each round drops an instruction or stops, so this ends.
    while retarget(code) | drop_redundant(code) {}
    copy_short_runs(code);
    while retarget(code) | drop_redundant(code) {}
}

/// Replace a jump to a few moves and then a jump or a return by those
/// moves and that jump or return, so the way through takes one jump where
/// it took two. Edges write their copies as such runs. Only a run that one
/// jump reaches, and nothing falls into, is moved, so the run left behind
/// is reached by nothing and goes, and no code grows. Decided over the
/// code as it stands, so a run moved is never moved again.
fn copy_short_runs(code: &mut Code<Inst>) {
    let alone = reached_once(code);
    // From the last, so each replacement leaves the earlier positions be.
    for at in (0..code.insts().len()).rev() {
        let Inst::Jump {
            condition: None,
            target,
        } = code.insts()[at]
        else {
            continue;
        };
        let moves = alone[target.index()]
            && code
                .position(target)
                .is_some_and(|start| !falls_into(code, start));
        if moves && let Some(run) = short_run(code, target) {
            code.replace(at, run);
        }
    }
}

/// Whether one jump or call alone lands where each label stands, as the
/// code is before anything moves.
fn reached_once(code: &Code<Inst>) -> Vec<bool> {
    let mut reached = vec![0u32; code.insts().len() + 1];
    for inst in code.insts() {
        if let Inst::Jump { target, .. } | Inst::Call { target } = *inst
            && let Some(position) = code.position(target)
        {
            reached[position] += 1;
        }
    }
    code.labels()
        .map(|(_, position)| position.is_some_and(|position| reached[position] == 1))
        .collect()
}

/// Whether what stands before `at` goes on into it.
fn falls_into(code: &Code<Inst>, at: usize) -> bool {
    at > 0
        && !matches!(
            code.insts()[at - 1],
            Inst::Jump {
                condition: None,
                ..
            } | Inst::Return
        )
}

/// The few plain instructions at `label` and the jump or return ending
/// them, where that is what stands there and the jump leads elsewhere.
fn short_run(code: &Code<Inst>, label: Label) -> Option<Vec<Inst>> {
    let start = code.position(label)?;
    let mut run = Vec::new();
    for inst in code.insts().get(start..)?.iter().take(COPIED + 1) {
        match *inst {
            Inst::Move { .. } | Inst::XorSelf { .. } => run.push(*inst),
            Inst::Jump {
                condition: None,
                target,
            } if code.position(target) != Some(start) => {
                run.push(*inst);
                return (run.len() > 1).then_some(run);
            }
            Inst::Return => {
                run.push(*inst);
                return (run.len() > 1).then_some(run);
            }
            _ => return None,
        }
    }
    None
}

/// Point every jump past the unconditional jumps it lands on. Answers
/// whether any moved.
fn retarget(code: &mut Code<Inst>) -> bool {
    let mut landed = vec![None; code.labels().len()];
    let finals: Vec<_> = code
        .insts()
        .iter()
        .map(|inst| match *inst {
            Inst::Jump { target, .. } => Some(landing(code, target, &mut landed)),
            _ => None,
        })
        .collect();
    let mut moved = false;
    for (inst, landed) in code.insts_mut().iter_mut().zip(finals) {
        if let (Inst::Jump { target, .. }, Some(landed)) = (inst, landed)
            && *target != landed
        {
            *target = landed;
            moved = true;
        }
    }
    moved
}

/// Where a jump to `label` ends up, following unconditional jumps, and
/// stopping at the first one seen twice. Where the jumps followed end
/// somewhere, each label passed is kept in `landed` with where they end,
/// so a chain many jumps land in is followed once rather than once for
/// each of them.
fn landing(code: &Code<Inst>, mut label: Label, landed: &mut [Option<Label>]) -> Label {
    let mut seen = Vec::new();
    let mut passed = HashSet::new();
    let mut ended = true;
    while let Some(at) = code.position(label)
        && let Some(&Inst::Jump {
            condition: None,
            target,
        }) = code.insts().get(at)
    {
        if let Some(end) = landed[label.index()] {
            label = end;
            break;
        }
        if passed.contains(&target.index()) {
            ended = false;
            break;
        }
        passed.insert(label.index());
        seen.push(label);
        label = target;
    }
    if ended {
        for passed in seen {
            landed[passed.index()] = Some(label);
        }
    }
    label
}

/// Drop jumps to the next instruction and what nothing reaches, and turn a
/// conditional jump over a jump into one. Answers whether anything went.
fn drop_redundant(code: &mut Code<Inst>) -> bool {
    let count = code.insts().len();
    let labelled = landed_on(code);
    let mut kept = vec![true; count];
    let mut reached = true;
    for at in 0..count {
        reached |= labelled[at];
        if !reached {
            kept[at] = false;
            continue;
        }
        match code.insts()[at] {
            Inst::Jump { condition, target } => {
                if code.position(target) == Some(at + 1) {
                    kept[at] = false;
                } else if let Some(condition) = condition
                    && let Some(&Inst::Jump {
                        condition: None,
                        target: over,
                    }) = code.insts().get(at + 1)
                    && !labelled[at + 1]
                    && code.position(target) == Some(at + 2)
                {
                    code.insts_mut()[at] = Inst::Jump {
                        condition: Some(condition.inverse()),
                        target: over,
                    };
                    kept[at + 1] = false;
                }
                reached = condition.is_some();
            }
            Inst::Return => reached = false,
            _ => {}
        }
    }
    let dropped = kept.iter().any(|&held| !held);
    code.keep(&kept);
    dropped
}

/// Where something jumps or calls to, by position: a label nothing names
/// any more is only where one used to.
fn landed_on(code: &Code<Inst>) -> Vec<bool> {
    let mut labelled = vec![false; code.insts().len() + 1];
    for inst in code.insts() {
        if let Inst::Jump { target, .. } | Inst::Call { target } = *inst
            && let Some(position) = code.position(target)
        {
            labelled[position] = true;
        }
    }
    labelled
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{Condition, Reg};

    fn jump(condition: Option<Condition>, target: Label) -> Inst {
        Inst::Jump { condition, target }
    }

    #[test]
    fn a_jump_to_a_jump_goes_where_the_second_goes_and_the_second_goes() {
        let mut code = Code::default();
        let (first, second) = (code.label(), code.label());
        code.push(jump(Some(Condition::Equal), first));
        code.push(Inst::Return);
        code.bind(first);
        code.push(jump(None, second));
        code.push(Inst::XorSelf { dst: Reg::Rax });
        code.bind(second);
        code.push(Inst::Return);
        thread(&mut code);
        assert_eq!(
            code.insts(),
            [
                jump(Some(Condition::Equal), second),
                Inst::Return,
                Inst::Return
            ]
        );
        assert_eq!(code.position(second), Some(2));
    }

    #[test]
    fn a_jump_to_the_next_instruction_is_nothing() {
        let mut code = Code::default();
        let next = code.label();
        code.push(jump(None, next));
        code.bind(next);
        code.push(Inst::Return);
        thread(&mut code);
        assert_eq!(code.insts(), [Inst::Return]);
    }

    /// A run of moves one jump reaches, and nothing falls into, goes where
    /// the jump was, and the run left behind goes.
    #[test]
    fn a_short_run_one_jump_reaches_takes_its_place() {
        let mut code = Code::default();
        let (other, run, away) = (code.label(), code.label(), code.label());
        let moved = Inst::Move {
            dst: Reg::Rax,
            src: Reg::Rcx,
            width: crate::machine::RegisterWidth::Word,
        };
        code.push(jump(Some(Condition::Equal), other));
        code.push(Inst::XorSelf { dst: Reg::Rdi });
        code.push(jump(None, run));
        code.bind(other);
        code.push(Inst::XorSelf { dst: Reg::Rdx });
        code.push(Inst::Return);
        code.bind(run);
        code.push(moved);
        code.push(jump(None, away));
        code.push(Inst::XorSelf { dst: Reg::Rsi });
        code.bind(away);
        code.push(Inst::Return);
        thread(&mut code);
        assert_eq!(
            code.insts(),
            [
                jump(Some(Condition::Equal), other),
                Inst::XorSelf { dst: Reg::Rdi },
                moved,
                Inst::Return,
                Inst::XorSelf { dst: Reg::Rdx },
                Inst::Return
            ]
        );
    }

    /// A run two jumps reach stays, so no code grows.
    #[test]
    fn a_short_run_two_jumps_reach_stays_where_it_is() {
        let mut code = Code::default();
        let run = code.label();
        let moved = Inst::Move {
            dst: Reg::Rax,
            src: Reg::Rcx,
            width: crate::machine::RegisterWidth::Word,
        };
        code.push(jump(Some(Condition::Equal), run));
        code.push(jump(None, run));
        code.bind(run);
        code.push(moved);
        code.push(Inst::Return);
        thread(&mut code);
        assert_eq!(code.insts(), [moved, Inst::Return]);
    }

    #[test]
    fn a_conditional_jump_over_a_jump_is_that_jump_the_other_way() {
        let mut code = Code::default();
        let (over, away) = (code.label(), code.label());
        code.push(jump(Some(Condition::Below), over));
        code.push(jump(None, away));
        code.bind(over);
        code.push(Inst::XorSelf { dst: Reg::Rax });
        code.bind(away);
        code.push(Inst::Return);
        thread(&mut code);
        assert_eq!(
            code.insts(),
            [
                jump(Some(Condition::NotBelow), away),
                Inst::XorSelf { dst: Reg::Rax },
                Inst::Return
            ]
        );
    }
}
