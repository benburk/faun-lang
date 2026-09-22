//! Lowering from verified split allocation to symbolic x86 instructions.
//!
//! This is the only producer of `machine::Allocated`; every late pseudo
//! expansion is verified before encoding.

use super::{Allocation, BlockPoints, InstPoints, Liveness, Location, Point, Transition, place};
use crate::machine::{
    Allocated, AllocatedBuilder, Alu, Condition, FrameSlot, Label, MemoryWidth, Reg, RegisterWidth,
    ShiftDirection,
};
use crate::parallel_copy::{self, Copy as ParallelCopy, CopySource, Move as CopyMove, Place};
use crate::selected::{BlockId, Immediate, Opcode, Requirements, Selected, Terminator, VReg};
use faun_core::ir::{DataId, FunctionId, Offset, Width};

const SYS_WRITE: u64 = 1;
const SYS_MMAP: u64 = 9;
const SYS_EXIT: u64 = 60;
const STDOUT: u64 = 1;
const PROT_READ_WRITE: u64 = 0x3;
const MAP_PRIVATE_ANONYMOUS: u64 = 0x22;
const COPY_SCRATCH: Reg = Reg::R11;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Known {
    Integer(u64),
    Data(DataId),
}

pub(super) fn lower(
    selected: &Selected,
    liveness: &Liveness,
    allocation: &Allocation,
    entry: FunctionId,
) -> Result<Allocated, String> {
    Lowering::new(selected, liveness, allocation).run(entry)
}

struct Lowering<'a> {
    selected: &'a Selected,
    liveness: &'a Liveness,
    allocation: &'a Allocation,
    asm: AllocatedBuilder,
    block_labels: Vec<Label>,
    function_labels: Vec<Option<Label>>,
    known: [Option<Known>; 16],
    argument_count_in_rbx: bool,
    pending_condition: Option<(VReg, Condition)>,
    exit_epilogue: Option<Label>,
    final_block: Option<BlockId>,
}

impl<'a> Lowering<'a> {
    fn new(selected: &'a Selected, liveness: &'a Liveness, allocation: &'a Allocation) -> Self {
        let mut asm = AllocatedBuilder::default();
        let block_labels: Vec<_> = (0..selected.blocks.len()).map(|_| asm.label()).collect();
        let function_slots = selected
            .functions
            .iter()
            .map(|function| function.source.index())
            .max()
            .map_or(0, |last| last + 1);
        let mut function_labels = vec![None; function_slots];
        for function in &selected.functions {
            function_labels[function.source.index()] = Some(block_labels[function.entry.index()]);
        }
        Self {
            selected,
            liveness,
            allocation,
            asm,
            block_labels,
            function_labels,
            known: [None; 16],
            argument_count_in_rbx: false,
            pending_condition: None,
            exit_epilogue: None,
            final_block: None,
        }
    }

    fn run(mut self, entry: FunctionId) -> Result<Allocated, String> {
        self.configure_program(entry);
        for (at, layout) in self.liveness.blocks.iter().enumerate() {
            let block = self.selected.blocks[layout.block.index()];
            let next = self.liveness.blocks.get(at + 1).map(|layout| layout.block);
            self.asm.bind(self.block_labels[layout.block.index()]);
            self.known.fill(None);
            self.pending_condition = None;
            if let Some(function) = self
                .selected
                .functions
                .iter()
                .find(|function| function.entry == layout.block)
            {
                if function.source == entry && self.argument_count_in_rbx {
                    self.asm.load_stack(Reg::Rbx, 0);
                }
                let spill_slots = self.spill_slots(function.source);
                if spill_slots > 0 {
                    self.asm.open_frame(spill_slots);
                }
            }
            for points in &layout.instructions {
                self.emit_instruction_setup(points)?;
                self.emit_late_transitions(points, true)?;
                self.emit_instruction(points)?;
                self.emit_late_transitions(points, false)?;
            }
            self.emit_transitions(layout.terminator)?;
            self.emit_terminator(layout, block.terminator, next, entry)?;
        }
        if let Some(epilogue) = self.exit_epilogue {
            self.asm.bind(epilogue);
            self.known.fill(None);
            self.materialize(Reg::Rax, SYS_EXIT);
            self.asm.syscall();
        }
        self.asm.finish()
    }

    fn configure_program(&mut self, entry: FunctionId) {
        self.argument_count_in_rbx = self.liveness.blocks.iter().any(|layout| {
            self.selected.blocks[layout.block.index()].owner != entry
                && layout.instructions.iter().any(|points| {
                    self.selected.instructions[points.instruction.index()].opcode
                        == Opcode::ArgumentCount
                })
        });
        let exits = self
            .selected
            .instructions
            .iter()
            .filter(|instruction| instruction.opcode == Opcode::Exit)
            .count();
        let returns = self
            .selected
            .blocks
            .iter()
            .filter(|block| {
                block.owner == entry && matches!(block.terminator, Terminator::Return { .. })
            })
            .count();
        self.exit_epilogue = (exits + returns > 1).then(|| self.asm.label());
        self.final_block = self.liveness.blocks.last().map(|layout| layout.block);
    }

    fn emit_instruction_setup(&mut self, points: &InstPoints) -> Result<(), String> {
        let inst = self.selected.instructions[points.instruction.index()];
        let before = Point::at(
            points
                .early
                .index()
                .checked_sub(1)
                .ok_or_else(|| "x86 instruction has no incoming point".to_owned())?,
        )?;
        let mut copies: Vec<_> = self
            .allocation
            .transitions
            .iter()
            .filter(|transition| transition.at == points.early)
            .map(|transition| ParallelCopy::between(place(transition.from), place(transition.to)))
            .collect();
        for (&value, &destination) in self.selected.operands[inst.operands.range()]
            .iter()
            .zip(&self.allocation.operand_locations[points.instruction.index()])
        {
            let copy =
                ParallelCopy::between(place(self.location(before, value)?), place(destination));
            if !copies.contains(&copy) {
                copies.push(copy);
            }
        }
        let owner = self.owner_at(points.early);
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner))?;
        self.emit_moves(plan.moves());
        Ok(())
    }

    fn emit_late_transitions(&mut self, points: &InstPoints, before: bool) -> Result<(), String> {
        let requirements = self.selected.instructions[points.instruction.index()]
            .opcode
            .requirements();
        let copies: Vec<_> = self
            .allocation
            .transitions
            .iter()
            .filter(|transition| {
                transition.at == points.late
                    && transition_before_instruction(**transition, requirements) == before
            })
            .map(|transition| ParallelCopy::between(place(transition.from), place(transition.to)))
            .collect();
        let owner = self.owner_at(points.late);
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner))?;
        self.emit_moves(plan.moves());
        Ok(())
    }

    fn emit_transitions(&mut self, point: Point) -> Result<(), String> {
        let copies: Vec<_> = self
            .allocation
            .transitions
            .iter()
            .filter(|transition| transition.at == point)
            .map(|transition| ParallelCopy::between(place(transition.from), place(transition.to)))
            .collect();
        let owner = self.owner_at(point);
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner))?;
        self.emit_moves(plan.moves());
        Ok(())
    }

    fn block_at(&self, point: Point) -> BlockId {
        self.liveness
            .blocks
            .iter()
            .find(|layout| {
                layout.entry.index() <= point.index() && point.index() <= layout.terminator.index()
            })
            .expect("every allocation point belongs to a block")
            .block
    }

    fn owner_at(&self, point: Point) -> FunctionId {
        self.selected.blocks[self.block_at(point).index()].owner
    }

    fn is_unique_constant(&self, value: VReg) -> bool {
        let Some((definition_id, definition)) = self
            .selected
            .instructions
            .iter()
            .enumerate()
            .find(|(_, instruction)| instruction.result == Some(value))
        else {
            return false;
        };
        let Immediate::Integer(integer) = definition.immediate else {
            return false;
        };
        let Some(block) = self.selected.blocks.iter().find(|block| {
            self.selected.order[block.instructions.range()]
                .iter()
                .any(|instruction| instruction.index() == definition_id)
        }) else {
            return false;
        };
        self.selected.order[block.instructions.range()]
            .iter()
            .filter(|instruction| {
                let instruction = self.selected.instructions[instruction.index()];
                instruction.opcode == Opcode::Constant
                    && instruction.immediate == Immediate::Integer(integer)
            })
            .count()
            == 1
            && self
                .selected
                .operands
                .iter()
                .filter(|&&operand| operand == value)
                .count()
                == 1
    }

    fn is_branch_only_result(&self, points: &InstPoints, result: VReg) -> bool {
        let block = self.selected.blocks[self.block_at(points.late).index()];
        let is_last = self.selected.order[block.instructions.range()]
            .last()
            .is_some_and(|&instruction| instruction == points.instruction);
        let is_condition =
            matches!(block.terminator, Terminator::Branch { condition, .. } if condition == result);
        let uses = self
            .selected
            .operands
            .iter()
            .filter(|&&operand| operand == result)
            .count()
            + self
                .selected
                .blocks
                .iter()
                .filter(|block| {
                    matches!(block.terminator, Terminator::Branch { condition, .. } if condition == result)
                })
                .count();
        is_last && is_condition && uses == 1
    }

    fn spill_slots(&self, owner: FunctionId) -> u32 {
        self.allocation.spill_slots[owner.index()]
    }

    fn copy_temporary(&self, owner: FunctionId) -> Option<Place> {
        (self.spill_slots(owner) > 0).then(|| Place::Frame(FrameSlot::at(0)))
    }

    fn emit_moves(&mut self, moves: &[CopyMove]) {
        for movement in moves {
            let CopySource::Place(source) = movement.source();
            match (source, movement.destination()) {
                (Place::Register(src), Place::Register(dst)) if src != dst => {
                    self.mov_reg(dst, src, RegisterWidth::Word);
                }
                (Place::Frame(src), Place::Register(dst)) => {
                    self.asm.load_slot(dst, src);
                    self.forget(dst);
                }
                (Place::Register(src), Place::Frame(dst)) => self.asm.store_slot(src, dst),
                (Place::Frame(src), Place::Frame(dst)) if src != dst => {
                    self.asm.load_slot(COPY_SCRATCH, src);
                    self.forget(COPY_SCRATCH);
                    self.asm.store_slot(COPY_SCRATCH, dst);
                }
                _ => {}
            }
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one verified expansion per selected x86 opcode"
    )]
    fn emit_instruction(&mut self, points: &InstPoints) -> Result<(), String> {
        let inst = self.selected.instructions[points.instruction.index()];
        let uses = &self.allocation.operand_locations[points.instruction.index()];
        let reg = |at: usize| match uses[at] {
            Location::Register(reg) => Ok(reg),
            Location::Spill(_) => Err("x86 allocated instruction operand is spilled".to_owned()),
        };
        let result_reg = inst
            .result
            .map(|value| match self.location(points.late, value)? {
                Location::Register(reg) => Ok(reg),
                Location::Spill(_) => Err("x86 allocated instruction result is spilled".to_owned()),
            })
            .transpose()?;
        let result =
            || result_reg.ok_or_else(|| "x86 instruction has no result register".to_owned());
        if !matches!(inst.opcode, Opcode::Constant | Opcode::DataAddress)
            && let Some(reg) = result_reg
        {
            self.forget(reg);
        }
        match (inst.opcode, inst.immediate) {
            (Opcode::Constant, Immediate::Integer(value)) => {
                self.materialize(result()?, value);
            }
            (Opcode::DataAddress, Immediate::Data(data)) => {
                self.load_data_address(result()?, data);
            }
            (Opcode::Add | Opcode::Subtract, Immediate::Bits(bits)) => {
                let op = if inst.opcode == Opcode::Add {
                    Alu::Add
                } else {
                    Alu::Subtract
                };
                let source = self.selected.operands[inst.operands.range()][1];
                let source_reg = reg(1)?;
                if self.is_unique_constant(source)
                    && self.asm.fold_alu_immediate(op, result()?, source_reg, bits)
                {
                    self.forget(source_reg);
                } else {
                    self.asm.alu(op, result()?, source_reg, bits);
                }
            }
            (Opcode::Multiply, Immediate::Bits(_)) => {
                self.asm.multiply();
                self.forget(Reg::Rdx);
            }
            (Opcode::Divide | Opcode::Modulo, Immediate::Bits(_)) => {
                self.emit_division(inst.opcode == Opcode::Modulo);
            }
            (Opcode::Equal | Opcode::Below, Immediate::Bits(bits)) => {
                let source = self.selected.operands[inst.operands.range()][1];
                let source_reg = reg(1)?;
                if self.is_unique_constant(source)
                    && self
                        .asm
                        .fold_alu_immediate(Alu::Compare, reg(0)?, source_reg, bits)
                {
                    self.forget(source_reg);
                } else {
                    self.asm.alu(Alu::Compare, reg(0)?, source_reg, bits);
                }
                let condition = if inst.opcode == Opcode::Equal {
                    Condition::Equal
                } else {
                    Condition::Below
                };
                let result = result()?;
                if self.is_branch_only_result(points, inst.result.expect("a compared result")) {
                    self.pending_condition =
                        Some((inst.result.expect("a compared result"), condition));
                } else {
                    self.asm.set_if(condition, result);
                }
            }
            (Opcode::Load, Immediate::Memory { width, offset }) => self.asm.load(
                memory_width(width),
                result()?,
                reg(0)?,
                displacement(offset)?,
            ),
            (Opcode::Store, Immediate::Memory { width, offset }) => {
                self.asm
                    .store(memory_width(width), reg(1)?, reg(0)?, displacement(offset)?);
            }
            (Opcode::Convert, Immediate::Bits(bits)) => {
                let input = self.selected.operands[inst.operands.range()][0];
                if bits < self.selected.widths[input.index()] {
                    self.asm.narrow(result()?, bits);
                }
            }
            (Opcode::Shift, Immediate::Shift { up, by, bits }) => self.asm.shift(
                if up {
                    ShiftDirection::Left
                } else {
                    ShiftDirection::Right
                },
                result()?,
                by,
                bits,
            ),
            (Opcode::Call, Immediate::Function(function)) => {
                let target = self
                    .function_labels
                    .get(function.index())
                    .and_then(|label| *label)
                    .ok_or_else(|| format!("x86 call has no body for {function:?}"))?;
                self.asm.call(target);
                self.forget_call_clobbers();
            }
            (Opcode::Write, Immediate::None) => {
                self.materialize(Reg::Rax, SYS_WRITE);
                debug_assert_eq!(SYS_WRITE, STDOUT);
                self.mov_reg(Reg::Rdi, Reg::Rax, RegisterWidth::Low32);
                self.asm.syscall();
                self.forget_call_clobbers();
            }
            (Opcode::Exit, Immediate::None) => {
                self.asm.omit_redundant_exit_narrow();
                if let Some(epilogue) = self.exit_epilogue {
                    if Some(self.block_at(points.late)) != self.final_block {
                        self.asm.jump(epilogue);
                    }
                } else {
                    self.materialize(Reg::Rax, SYS_EXIT);
                    self.asm.syscall();
                    self.forget_call_clobbers();
                }
            }
            (Opcode::Grow, Immediate::None) => {
                self.materialize(Reg::Rax, SYS_MMAP);
                self.materialize(Reg::Rdi, 0);
                self.materialize(Reg::Rdx, PROT_READ_WRITE);
                self.materialize(Reg::R10, MAP_PRIVATE_ANONYMOUS);
                self.materialize(Reg::R8, u64::MAX);
                self.materialize(Reg::R9, 0);
                self.asm.syscall();
                self.forget_call_clobbers();
            }
            (Opcode::ArgumentCount, Immediate::None) => {
                let dst = result()?;
                if self.argument_count_in_rbx {
                    self.mov_reg(dst, Reg::Rbx, RegisterWidth::Word);
                } else {
                    let owner = self.owner_at(points.late);
                    let displacement = self
                        .spill_slots(owner)
                        .checked_mul(8)
                        .ok_or_else(|| "x86 entry frame displacement overflows".to_owned())?;
                    self.asm.load_stack(dst, displacement);
                    self.forget(dst);
                }
            }
            _ => return Err("x86 selected opcode has an invalid late expansion".to_owned()),
        }
        Ok(())
    }

    fn materialize(&mut self, dst: Reg, value: u64) {
        let known = Known::Integer(value);
        if self.known[dst.index()] == Some(known) {
            return;
        }
        let source =
            self.known.iter().enumerate().find_map(|(at, &held)| {
                (held == Some(known)).then(|| Reg::from_index(at)).flatten()
            });
        if value != 0
            && let Some(source) = source
        {
            self.mov_reg(
                dst,
                source,
                if u32::try_from(value).is_ok() {
                    RegisterWidth::Low32
                } else {
                    RegisterWidth::Word
                },
            );
        } else {
            materialize(&mut self.asm, dst, value);
            self.known[dst.index()] = Some(known);
        }
    }

    fn load_data_address(&mut self, dst: Reg, data: DataId) {
        let known = Known::Data(data);
        if self.known[dst.index()] == Some(known) {
            return;
        }
        if let Some(source) =
            self.known.iter().enumerate().find_map(|(at, &held)| {
                (held == Some(known)).then(|| Reg::from_index(at)).flatten()
            })
        {
            self.mov_reg(dst, source, RegisterWidth::Word);
        } else {
            self.asm.load_data_address(dst, data);
            self.known[dst.index()] = Some(known);
        }
    }

    fn mov_reg(&mut self, dst: Reg, src: Reg, width: RegisterWidth) {
        self.asm.mov_reg(dst, src, width);
        self.known[dst.index()] = match (width, self.known[src.index()]) {
            (RegisterWidth::Word, known) => known,
            (RegisterWidth::Low32, Some(Known::Integer(value))) if u32::try_from(value).is_ok() => {
                Some(Known::Integer(value))
            }
            _ => None,
        };
    }

    fn forget(&mut self, reg: Reg) {
        self.known[reg.index()] = None;
    }

    fn forget_call_clobbers(&mut self) {
        for reg in [
            Reg::Rax,
            Reg::Rcx,
            Reg::Rdx,
            Reg::Rsi,
            Reg::Rdi,
            Reg::R8,
            Reg::R9,
            Reg::R10,
            Reg::R11,
        ] {
            self.forget(reg);
        }
    }

    fn emit_division(&mut self, modulo: bool) {
        let zero = self.asm.label();
        let end = self.asm.label();
        self.asm.alu(Alu::Test, Reg::Rcx, Reg::Rcx, 64);
        self.asm.jump_if(Condition::Equal, zero);
        self.asm.xor_self(Reg::Rdx);
        self.asm.divide();
        if modulo {
            self.asm.mov_reg(Reg::Rax, Reg::Rdx, RegisterWidth::Word);
        }
        self.asm.jump(end);
        self.asm.bind(zero);
        if !modulo {
            self.asm.xor_self(Reg::Rax);
        }
        self.asm.bind(end);
        self.forget(Reg::Rax);
        self.forget(Reg::Rdx);
    }

    #[expect(
        clippy::too_many_lines,
        reason = "each CFG exit form emits its edge transfers and control operation"
    )]
    fn emit_terminator(
        &mut self,
        layout: &BlockPoints,
        terminator: Terminator,
        next: Option<BlockId>,
        entry: FunctionId,
    ) -> Result<(), String> {
        match terminator {
            Terminator::Jump { target, .. } => {
                self.emit_edge(layout.block, target)?;
                if Some(target) != next {
                    self.asm.jump(self.block_labels[target.index()]);
                }
            }
            Terminator::Branch {
                condition,
                then_target,
                else_target,
                ..
            } => {
                let (when_true, when_false) = if let Some((pending, condition_code)) =
                    self.pending_condition.take()
                    && pending == condition
                {
                    (condition_code, inverse(condition_code))
                } else {
                    let condition = match self.location(layout.terminator, condition)? {
                        Location::Register(reg) => reg,
                        Location::Spill(_) => {
                            return Err("x86 branch condition is spilled".to_owned());
                        }
                    };
                    self.asm.alu(Alu::Test, condition, condition, 64);
                    (Condition::NotEqual, Condition::Equal)
                };
                let edges_are_empty = self.edge_moves(layout.block, then_target)?.is_empty()
                    && self.edge_moves(layout.block, else_target)?.is_empty();
                if Some(then_target) == next && edges_are_empty {
                    self.asm
                        .jump_if(when_false, self.block_labels[else_target.index()]);
                } else if Some(else_target) == next && edges_are_empty {
                    self.asm
                        .jump_if(when_true, self.block_labels[then_target.index()]);
                } else if Some(then_target) == next {
                    let then_path = self.asm.label();
                    self.asm.jump_if(when_true, then_path);
                    self.emit_edge(layout.block, else_target)?;
                    self.asm.jump(self.block_labels[else_target.index()]);
                    self.asm.bind(then_path);
                    self.emit_edge(layout.block, then_target)?;
                } else if Some(else_target) == next {
                    let else_path = self.asm.label();
                    self.asm.jump_if(when_false, else_path);
                    self.emit_edge(layout.block, then_target)?;
                    self.asm.jump(self.block_labels[then_target.index()]);
                    self.asm.bind(else_path);
                    self.emit_edge(layout.block, else_target)?;
                } else {
                    let otherwise = self.asm.label();
                    self.asm.jump_if(when_false, otherwise);
                    self.emit_edge(layout.block, then_target)?;
                    self.asm.jump(self.block_labels[then_target.index()]);
                    self.asm.bind(otherwise);
                    self.emit_edge(layout.block, else_target)?;
                    self.asm.jump(self.block_labels[else_target.index()]);
                }
            }
            Terminator::Return { values } => {
                let owner = self.selected.blocks[layout.block.index()].owner;
                if owner == entry {
                    if values.is_empty() {
                        self.materialize(Reg::Rdi, 0);
                    } else {
                        self.asm.omit_redundant_exit_narrow();
                    }
                    if let Some(epilogue) = self.exit_epilogue {
                        if Some(layout.block) != self.final_block {
                            self.asm.jump(epilogue);
                        }
                    } else {
                        self.materialize(Reg::Rax, SYS_EXIT);
                        self.asm.syscall();
                    }
                } else {
                    let spill_slots = self.spill_slots(owner);
                    if spill_slots > 0 {
                        self.asm.close_frame(spill_slots);
                    }
                    self.asm.ret();
                }
            }
            Terminator::Halt => {}
        }
        Ok(())
    }

    fn edge_moves(&self, from: BlockId, target: BlockId) -> Result<&[CopyMove], String> {
        self.allocation
            .edge_moves
            .iter()
            .find(|edge| edge.from == from && edge.target == target)
            .map(|edge| edge.moves.as_slice())
            .ok_or_else(|| {
                format!(
                    "x86 b{} has no move plan to b{}",
                    from.index(),
                    target.index()
                )
            })
    }

    fn emit_edge(&mut self, from: BlockId, target: BlockId) -> Result<(), String> {
        let moves = self.edge_moves(from, target)?.to_vec();
        self.emit_moves(&moves);
        Ok(())
    }

    fn location(&self, point: Point, value: VReg) -> Result<Location, String> {
        self.allocation
            .segments
            .iter()
            .find(|segment| {
                segment.value == value
                    && segment.start.index() <= point.index()
                    && point.index() < segment.end.index()
            })
            .map(|segment| segment.location)
            .ok_or_else(|| format!("x86 v{} has no allocated segment", value.index()))
    }
}

const fn inverse(condition: Condition) -> Condition {
    match condition {
        Condition::Equal => Condition::NotEqual,
        Condition::NotEqual => Condition::Equal,
        Condition::Below => Condition::NotBelow,
        Condition::NotBelow => Condition::Below,
    }
}

const fn transition_before_instruction(transition: Transition, requirements: Requirements) -> bool {
    match (transition.from, transition.to) {
        (_, Location::Spill(_)) => true,
        (Location::Spill(_), Location::Register(_)) => false,
        (Location::Register(source), Location::Register(_)) => {
            requirements.effects.clobbers.contains(source) || requirements.scratch.contains(source)
        }
    }
}

fn materialize(asm: &mut AllocatedBuilder, dst: Reg, value: u64) {
    if value == 0 {
        asm.xor_self(dst);
    } else if let Ok(small) = i8::try_from(value.cast_signed()) {
        asm.push_imm8(small);
        asm.pop(dst);
    } else if let Ok(unsigned) = u32::try_from(value) {
        asm.mov_imm32(dst, unsigned);
    } else if let Ok(signed) = i32::try_from(value.cast_signed()) {
        asm.mov_sext_imm32(dst, signed);
    } else {
        asm.mov_imm64(dst, value);
    }
}

const fn memory_width(width: Width) -> MemoryWidth {
    match width {
        Width::Byte => MemoryWidth::Byte,
        Width::Word => MemoryWidth::Word,
    }
}

fn displacement(offset: Offset) -> Result<i32, String> {
    match offset {
        Offset::Bytes(bytes) => Ok(bytes),
        Offset::Words(words) => words
            .checked_mul(8)
            .ok_or_else(|| "x86 memory displacement overflows 32 bits".to_owned()),
    }
}
