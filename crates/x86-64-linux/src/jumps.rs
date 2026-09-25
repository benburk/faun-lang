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
//! Nothing a jump or a call lands on is dropped, and nothing before the
//! first jump or return, so every place control may reach stays where it
//! was, and so does the entry, which is the first instruction.

use super::machine::{Condition, Inst};
use faun_core::targets::code::{Code, Label};

/// Rewrite `code` until none of those shapes is left.
pub(crate) fn thread(code: &mut Code<Inst>) {
    // Each round drops an instruction or stops, so this ends.
    while retarget(code) | drop_redundant(code) {}
}

/// Point every jump past the unconditional jumps it lands on. Answers
/// whether any moved.
fn retarget(code: &mut Code<Inst>) -> bool {
    let finals: Vec<_> = code
        .insts()
        .iter()
        .map(|inst| match *inst {
            Inst::Jump { target, .. } => Some(landing(code, target)),
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
/// stopping at the first one seen twice.
fn landing(code: &Code<Inst>, mut label: Label) -> Label {
    let mut seen = Vec::new();
    while let Some(at) = code.position(label)
        && let Some(&Inst::Jump {
            condition: None,
            target,
        }) = code.insts().get(at)
        && !seen.contains(&target)
    {
        seen.push(label);
        label = target;
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
                        condition: Some(negated(condition)),
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

const fn negated(condition: Condition) -> Condition {
    match condition {
        Condition::Equal => Condition::NotEqual,
        Condition::NotEqual => Condition::Equal,
        Condition::Below => Condition::NotBelow,
        Condition::NotBelow => Condition::Below,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::Reg;

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
