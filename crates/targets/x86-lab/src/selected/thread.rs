//! Edges that carry a number to a block which only tests it, taken straight
//! to where the test sends them.
//!
//! A structured branch answering a condition, `a & b` or `a | b` among them,
//! is selected as arms that each jump to a join with a number, nought or one,
//! and a join that compares what it was handed and branches on that. Where an
//! arm hands over a number, the comparison's answer on that edge is known
//! before the join is reached, so the edge can go to the side the join would
//! take. The join is then asked only by the arms that hand it something
//! worked out, and a condition such as `count < most & …` becomes the
//! comparison and a conditional jump, with no number written and tested.
//!
//! A block is passed through only where nothing it writes, its parameters
//! among them, is read outside it, and everything it does is arithmetic with
//! no effect: skipping it then skips nothing anyone sees. A walk from an edge
//! follows such blocks while what it carries stays a number or a value the
//! edge already had, and stops at the first block it cannot pass or branch
//! it cannot decide. The edge is moved only where the walk decided a branch,
//! so an edge is never moved merely to land somewhere else. A block no edge
//! reaches any more is dropped afterwards, with its instructions.

use std::collections::HashMap;

use super::{BlockDraft, Immediate, Inst, Opcode, Selector, Terminator, VReg, append};
use faun_core::index::{Pool, Range};

use super::{BlockId, InstId};

/// The most blocks a walk from one edge passes through.
const STEPS: usize = 8;

/// What an instruction answers, as a walk passing it sees it.
enum Answer {
    /// What it writes, where that is known.
    Known(Carried),
    /// Something worked out from what is not known.
    Unknown,
    /// It has an effect, or is not arithmetic a walk reads, so its block
    /// cannot be passed.
    Stops,
}

/// What an edge carries, as a walk sees it.
#[derive(Clone, Copy)]
enum Carried {
    /// A value the edge's source already has.
    Value(VReg),
    /// A number, with a value the source already has holding it where there
    /// is one, and the width it was written at.
    Number(u64, Option<VReg>, u16),
}

impl Selector<'_> {
    /// Move every edge whose number decides a branch further on, then drop
    /// what nothing reaches.
    #[expect(clippy::too_many_lines, reason = "one rewrite per kind of edge")]
    pub(super) fn thread(&mut self) {
        let numbers = self.numbers();
        let outside = self.read_outside();
        let mut changed = false;
        for at in 0..self.blocks.len() {
            let block = BlockId::at(at);
            let Some(terminator) = self.blocks[block].terminator else {
                continue;
            };
            let moved = match terminator {
                Terminator::Jump { target, args } => self
                    .walk(block, target, args, &numbers, &outside)
                    .map(|(target, args)| Terminator::Jump { target, args }),
                Terminator::Branch {
                    condition,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    let then_side = self.walk(block, then_target, then_args, &numbers, &outside);
                    let else_side = self.walk(block, else_target, else_args, &numbers, &outside);
                    (then_side.is_some() || else_side.is_some()).then(|| {
                        let (then_target, then_args) =
                            then_side.unwrap_or((then_target, then_args));
                        let (else_target, else_args) =
                            else_side.unwrap_or((else_target, else_args));
                        Terminator::Branch {
                            condition,
                            then_target,
                            then_args,
                            else_target,
                            else_args,
                        }
                    })
                }
                Terminator::Return { .. } | Terminator::Halt => None,
            };
            if let Some(moved) = moved {
                self.blocks[block].terminator = Some(moved);
                changed = true;
            }
        }
        if changed {
            self.drop_unreached();
        }
    }

    /// The number each value written by a constant is.
    fn numbers(&self) -> HashMap<VReg, u64> {
        self.instructions
            .iter()
            .filter_map(|inst| match (inst.opcode, inst.immediate, inst.result) {
                (Opcode::Constant, Immediate::Integer(number), Some(result)) => {
                    Some((result, number))
                }
                _ => None,
            })
            .collect()
    }

    /// For each value, whether anything outside the block writing it reads
    /// it: an instruction, a branch's condition or an edge.
    #[expect(clippy::too_many_lines, reason = "one walk over every kind of read")]
    fn read_outside(&self) -> Vec<bool> {
        let mut home = vec![None; self.widths.len()];
        for (id, block) in self.blocks.iter_enumerated() {
            for &param in &block.params {
                home[param.index()] = Some(id);
            }
            for &inst in &block.instructions {
                if let Some(result) = self.instructions[inst].result {
                    home[result.index()] = Some(id);
                }
            }
        }
        let mut outside = vec![false; self.widths.len()];
        let mut read = |value: VReg, by: BlockId| {
            if home[value.index()] != Some(by) {
                outside[value.index()] = true;
            }
        };
        for (id, block) in self.blocks.iter_enumerated() {
            for &inst in &block.instructions {
                for &operand in &self.operands[self.instructions[inst].operands.range()] {
                    read(operand, id);
                }
            }
            match block.terminator {
                Some(Terminator::Jump { args, .. }) => {
                    for &arg in &self.operands[args.range()] {
                        read(arg, id);
                    }
                }
                Some(Terminator::Branch {
                    condition,
                    then_args,
                    else_args,
                    ..
                }) => {
                    read(condition, id);
                    for &arg in self.operands[then_args.range()]
                        .iter()
                        .chain(&self.operands[else_args.range()])
                    {
                        read(arg, id);
                    }
                }
                Some(Terminator::Return { values }) => {
                    for &value in &self.operands[values.range()] {
                        read(value, id);
                    }
                }
                Some(Terminator::Halt) | None => {}
            }
        }
        outside
    }

    /// Where the edge from `from` to `target` carrying `args` can go
    /// instead, and what it carries there, where the walk decided a branch.
    #[expect(
        clippy::too_many_lines,
        reason = "one walk through blocks, evaluating each"
    )]
    fn walk(
        &mut self,
        from: BlockId,
        target: BlockId,
        args: Range,
        numbers: &HashMap<VReg, u64>,
        outside: &[bool],
    ) -> Option<(BlockId, Range)> {
        let entries: Vec<_> = self
            .functions
            .iter()
            .map(|function| function.entry)
            .collect();
        let mut carried: Vec<Carried> = self.operands[args.range()]
            .iter()
            .map(|&value| match numbers.get(&value) {
                Some(&number) => Carried::Number(number, Some(value), self.widths[value.index()]),
                None => Carried::Value(value),
            })
            .collect();
        let mut at = target;
        let mut landing = None;
        for _ in 0..STEPS {
            if at == from || entries.contains(&at) {
                break;
            }
            let block = &self.blocks[at];
            let mut held: HashMap<VReg, Option<Carried>> = HashMap::new();
            for (&param, &value) in block.params.iter().zip(&carried) {
                held.insert(param, Some(value));
            }
            let outside = |value: VReg| outside.get(value.index()).copied().unwrap_or(true);
            if block.params.iter().any(|&param| outside(param)) {
                break;
            }
            let mut passable = true;
            for &inst in &block.instructions {
                let inst = self.instructions[inst];
                let Some(result) = inst.result else {
                    passable = false;
                    break;
                };
                if outside(result) {
                    passable = false;
                    break;
                }
                match self.evaluate(inst, &held) {
                    Answer::Known(value) => held.insert(result, Some(value)),
                    Answer::Unknown => held.insert(result, None),
                    Answer::Stops => {
                        passable = false;
                        break;
                    }
                };
            }
            if !passable {
                break;
            }
            // What a value read here is: its own where the block wrote it,
            // and where not, what the edge's source already has.
            let read = |value: VReg| match held.get(&value) {
                Some(&written) => written,
                None => Some(
                    numbers
                        .get(&value)
                        .map_or(Carried::Value(value), |&number| {
                            Carried::Number(number, Some(value), self.widths[value.index()])
                        }),
                ),
            };
            let (next, edge, decides) = match block.terminator {
                Some(Terminator::Jump { target, args }) => (target, args, false),
                Some(Terminator::Branch {
                    condition,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                }) => match read(condition) {
                    Some(Carried::Number(0, ..)) => (else_target, else_args, true),
                    Some(Carried::Number(..)) => (then_target, then_args, true),
                    _ => break,
                },
                _ => break,
            };
            let Some(next_carried) = self.operands[edge.range()]
                .iter()
                .map(|&value| read(value))
                .collect::<Option<Vec<_>>>()
            else {
                break;
            };
            carried = next_carried;
            at = next;
            if decides {
                landing = Some((at, carried.clone()));
            }
        }
        let (target, carried) = landing?;
        let args: Vec<VReg> = carried
            .into_iter()
            .map(|value| match value {
                Carried::Value(value) | Carried::Number(_, Some(value), _) => value,
                Carried::Number(number, None, width) => self.constant(from, number, width),
            })
            .collect();
        Some((target, append(&mut self.operands, &args)))
    }

    /// What an instruction with no effect answers on what it reads: a
    /// number where all it reads are numbers.
    fn evaluate(&self, inst: Inst, held: &HashMap<VReg, Option<Carried>>) -> Answer {
        let operands = &self.operands[inst.operands.range()];
        let number = |at: usize| match held.get(&operands[at]) {
            Some(Some(Carried::Number(number, ..))) => Some(*number),
            _ => None,
        };
        let Some(result) = inst.result else {
            return Answer::Stops;
        };
        let width = self.widths[result.index()];
        let masked = |value: u64, bits: u16| {
            if bits >= 64 {
                value
            } else {
                value & ((1 << bits) - 1)
            }
        };
        let answer = match (inst.opcode, inst.immediate) {
            (Opcode::Constant, Immediate::Integer(number)) => Some(number),
            (Opcode::Equal | Opcode::Below, Immediate::Bits(bits)) => {
                match (number(0), number(1)) {
                    (Some(left), Some(right)) => {
                        let (left, right) = (masked(left, bits), masked(right, bits));
                        Some(u64::from(if inst.opcode == Opcode::Equal {
                            left == right
                        } else {
                            left < right
                        }))
                    }
                    _ => None,
                }
            }
            (Opcode::Convert, Immediate::None) => number(0),
            (Opcode::Convert, Immediate::Bits(bits)) => number(0).map(|value| masked(value, bits)),
            _ => return Answer::Stops,
        };
        answer.map_or(Answer::Unknown, |number| {
            Answer::Known(Carried::Number(number, None, width))
        })
    }

    /// A value holding `number` written at the end of `block`.
    fn constant(&mut self, block: BlockId, number: u64, width: u16) -> VReg {
        let result = VReg::at(self.widths.len());
        self.widths.push(width);
        let id = self.instructions.push(Inst {
            opcode: Opcode::Constant,
            result: Some(result),
            operands: Range::EMPTY,
            immediate: Immediate::Integer(number),
        });
        self.blocks[block].instructions.push(id);
        result
    }

    /// Drop every block no function's entry reaches, and the instructions
    /// they held, numbering what is left again in the same order.
    #[expect(
        clippy::too_many_lines,
        reason = "finding, renumbering and rebuilding in one place"
    )]
    fn drop_unreached(&mut self) {
        let mut reached = vec![false; self.blocks.len()];
        let mut stack: Vec<BlockId> = self
            .functions
            .iter()
            .map(|function| function.entry)
            .collect();
        while let Some(block) = stack.pop() {
            if std::mem::replace(&mut reached[block.index()], true) {
                continue;
            }
            match self.blocks[block].terminator {
                Some(Terminator::Jump { target, .. }) => stack.push(target),
                Some(Terminator::Branch {
                    then_target,
                    else_target,
                    ..
                }) => stack.extend([then_target, else_target]),
                _ => {}
            }
        }
        if reached.iter().all(|&reached| reached) {
            return;
        }
        let mut renumbered = vec![None; self.blocks.len()];
        let mut kept = 0;
        for (at, &reached) in reached.iter().enumerate() {
            if reached {
                renumbered[at] = Some(BlockId::at(kept));
                kept += 1;
            }
        }
        let renumber = |block: BlockId| renumbered[block.index()].expect("a reached block");
        let drafts = std::mem::take(&mut self.blocks);
        let old_instructions = std::mem::take(&mut self.instructions);
        let mut instructions: Pool<InstId, Inst> = Pool::default();
        let mut blocks: Pool<BlockId, BlockDraft> = Pool::default();
        for (at, mut draft) in drafts.into_iter().enumerate() {
            if !reached[at] {
                continue;
            }
            draft.instructions = draft
                .instructions
                .iter()
                .map(|&inst| instructions.push(old_instructions[inst]))
                .collect();
            draft.terminator = draft.terminator.map(|terminator| match terminator {
                Terminator::Jump { target, args } => Terminator::Jump {
                    target: renumber(target),
                    args,
                },
                Terminator::Branch {
                    condition,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => Terminator::Branch {
                    condition,
                    then_target: renumber(then_target),
                    then_args,
                    else_target: renumber(else_target),
                    else_args,
                },
                other => other,
            });
            blocks.push(draft);
        }
        for function in &mut self.functions {
            function.entry = renumber(function.entry);
        }
        self.blocks = blocks;
        self.instructions = instructions;
    }
}

impl Selector<'_> {
    /// Move a comparison a block's branch alone reads to just before the
    /// branch, so the branch reads its flags rather than a number written
    /// from them and tested again.
    #[expect(
        clippy::too_many_lines,
        reason = "counting every read, then one move per branch"
    )]
    pub(super) fn sink_conditions(&mut self) {
        let mut reads = vec![0_u32; self.widths.len()];
        for inst in &self.instructions {
            for &operand in &self.operands[inst.operands.range()] {
                reads[operand.index()] += 1;
            }
        }
        for block in &self.blocks {
            match block.terminator {
                Some(Terminator::Jump { args, .. }) => {
                    for &arg in &self.operands[args.range()] {
                        reads[arg.index()] += 1;
                    }
                }
                Some(Terminator::Branch {
                    condition,
                    then_args,
                    else_args,
                    ..
                }) => {
                    reads[condition.index()] += 1;
                    for &arg in self.operands[then_args.range()]
                        .iter()
                        .chain(&self.operands[else_args.range()])
                    {
                        reads[arg.index()] += 1;
                    }
                }
                Some(Terminator::Return { values }) => {
                    for &value in &self.operands[values.range()] {
                        reads[value.index()] += 1;
                    }
                }
                Some(Terminator::Halt) | None => {}
            }
        }
        for block in &mut self.blocks {
            let Some(Terminator::Branch { condition, .. }) = block.terminator else {
                continue;
            };
            if reads[condition.index()] != 1 {
                continue;
            }
            let Some(at) = block.instructions.iter().position(|&inst| {
                let inst = self.instructions[inst];
                inst.result == Some(condition)
                    && matches!(inst.opcode, Opcode::Equal | Opcode::Below)
            }) else {
                continue;
            };
            let inst = block.instructions.remove(at);
            block.instructions.push(inst);
        }
    }
}
