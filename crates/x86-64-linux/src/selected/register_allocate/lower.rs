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
use crate::selected::{BlockId, Immediate, InstId, Opcode, Selected, Terminator, VReg};
use faun_core::codegen::registers::SpillSlot;
use faun_core::ir::{DataId, FunctionId, Offset, Width};

const SYS_READ: u64 = 0;
const SYS_WRITE: u64 = 1;
const SYS_CLOSE: u64 = 3;
const SYS_OPENAT2: u64 = 437;
/// A name is read from where the program runs.
const AT_FDCWD: u64 = (-100i64).cast_unsigned();
/// A name reaching above where it is read from, by `..`, from the root, or
/// through a link, is refused.
const RESOLVE_BENEATH: i8 = 0x08;
/// How many bytes `openat2`'s `how` is: three words.
const OPEN_HOW_BYTES: u64 = 24;
const SYS_MMAP: u64 = 9;
const SYS_RT_SIGACTION: u64 = 13;
/// Writing to a pipe nobody reads raises it, which ends the program unless
/// it is ignored.
const SIGPIPE: u64 = 13;
/// What `rt_sigaction` reads the signal set's size as: one word.
const SIGSET_BYTES: u64 = 8;
const SYS_EXIT: u64 = 60;
const STDIN: u64 = 0;
const STDOUT: u64 = 1;
const PROT_READ_WRITE: u64 = 0x3;
const MAP_PRIVATE_ANONYMOUS: u64 = 0x22;
pub(super) const COPY_SCRATCH: Reg = Reg::R11;
/// What a function keeps for whatever called it: a call leaves these alone.
pub(crate) const CALLEE_SAVED: [Reg; 5] = [Reg::R12, Reg::R13, Reg::R14, Reg::R15, Reg::Rbp];

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
    known: [Option<Known>; 32],
    argument_count_in_rbx: bool,
    pending_condition: Option<(VReg, Condition)>,
    exit_epilogue: Option<Label>,
    final_block: Option<BlockId>,
    uses: Uses,
    /// The registers each function keeps for its caller: those a call
    /// leaves alone that it writes, put back before it returns.
    saved: Vec<Vec<Reg>>,
    frames: Vec<Frame>,
}

/// The outgoing call area starts at rsp, followed by allocator spill slots
/// and saved registers. Incoming values lie above this frame and the return
/// address. No call area overlaps a live spill or its caller's incoming area.
#[derive(Clone, Copy, Default)]
struct Frame {
    outgoing: u32,
    words: u32,
}

/// Where each value is defined and how often it is read, gathered once so
/// that asking of one value costs nothing like the whole program.
struct Uses {
    /// The instruction defining each value.
    definitions: Vec<Option<InstId>>,
    /// The block listing each instruction.
    blocks: Vec<Option<BlockId>>,
    /// How many operands read each value.
    operands: Vec<u32>,
    /// How many branches test each value.
    branches: Vec<u32>,
}

impl Uses {
    fn new(selected: &Selected) -> Self {
        let mut uses = Self {
            definitions: vec![None; selected.widths.len()],
            blocks: vec![None; selected.instructions.len()],
            operands: vec![0; selected.widths.len()],
            branches: vec![0; selected.widths.len()],
        };
        for (at, instruction) in selected.instructions.iter().enumerate() {
            if let Some(result) = instruction.result {
                uses.definitions[result.index()].get_or_insert_with(|| InstId::at(at));
            }
        }
        for (id, block) in selected.blocks.iter_enumerated() {
            for &instruction in &selected.order[block.instructions.range()] {
                uses.blocks[instruction.index()].get_or_insert(id);
            }
            if let Terminator::Branch { condition, .. } = block.terminator {
                uses.branches[condition.index()] += 1;
            }
        }
        for &operand in &selected.operands {
            uses.operands[operand.index()] += 1;
        }
        uses
    }
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
            known: [None; 32],
            argument_count_in_rbx: false,
            pending_condition: None,
            exit_epilogue: None,
            final_block: None,
            uses: Uses::new(selected),
            saved: Vec::new(),
            frames: Vec::new(),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one ordered lowering walk over allocated blocks"
    )]
    fn run(mut self, entry: FunctionId) -> Result<Allocated, String> {
        self.configure_program(entry);
        self.saved = self.kept_for_callers(entry);
        self.frames = self.layout_frames()?;
        self.ignore_broken_pipes();
        for (at, layout) in self.liveness.blocks.iter().enumerate() {
            let block = self.selected.blocks[layout.block];
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
                self.enter_function(function.source, entry);
                let frame = self.frame(function.source);
                if frame > 0 {
                    self.asm.open_frame(frame);
                }
                self.keep_for_caller(function.source, true);
            }
            self.emit_stores(layout.entry);
            for points in &layout.instructions {
                self.emit_instruction_setup(points)?;
                self.emit_late_transitions(points, true)?;
                self.emit_instruction(points)?;
                self.emit_late_transitions(points, false)?;
                self.emit_stores(points.late);
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

    /// Whether the program writes to a descriptor, which may be a pipe.
    fn writes(&self) -> bool {
        self.liveness.blocks.iter().any(|layout| {
            layout.instructions.iter().any(|points| {
                matches!(
                    self.selected.instructions[points.instruction].opcode,
                    Opcode::Write | Opcode::WriteFd
                )
            })
        })
    }

    /// Before anything else runs in a program that writes, ignore `SIGPIPE`,
    /// so a write to a pipe nobody reads answers `EPIPE` as a value, as it
    /// does on every other target, rather than ending the program from
    /// inside the write. A program that never writes pays nothing.
    /// `rt_sigaction` reads the kernel's `struct sigaction` from the stack:
    /// the handler, `SIG_IGN`, then flags, restorer and mask, all nought.
    /// Nothing is live yet, and the stack is as the kernel left it once the
    /// four words are popped. A program that starts another must restore the
    /// default in the child, which inherits the disposition.
    fn ignore_broken_pipes(&mut self) {
        if !self.writes() {
            return;
        }
        // Nought is also where no old action is to be written.
        self.materialize(Reg::Rdx, 0);
        for _ in 0..3 {
            self.asm.push_reg(Reg::Rdx);
        }
        self.asm.push_imm8(1);
        self.asm.mov_reg(Reg::Rsi, Reg::Rsp, RegisterWidth::Word);
        self.materialize(Reg::Rdi, SIGPIPE);
        self.materialize(Reg::R10, SIGSET_BYTES);
        self.materialize(Reg::Rax, SYS_RT_SIGACTION);
        self.asm.syscall();
        for _ in 0..4 {
            self.asm.pop(Reg::Rcx);
        }
        self.known.fill(None);
    }

    fn enter_function(&mut self, function: FunctionId, entry: FunctionId) {
        if function == entry && self.argument_count_in_rbx {
            self.asm.load_stack(Reg::Rbx, 0);
        }
    }

    fn configure_program(&mut self, entry: FunctionId) {
        self.argument_count_in_rbx = self.liveness.blocks.iter().any(|layout| {
            self.selected.blocks[layout.block].owner != entry
                && layout.instructions.iter().any(|points| {
                    self.selected.instructions[points.instruction].opcode == Opcode::ArgumentCount
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
        let inst = self.selected.instructions[points.instruction];
        let before = Point::at(
            points
                .early
                .index()
                .checked_sub(1)
                .ok_or_else(|| "x86 instruction has no incoming point".to_owned())?,
        )?;
        let mut copies: Vec<_> = self
            .allocation
            .transitions_at(points.early)
            .iter()
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
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner, &copies))?;
        self.emit_moves(plan.moves(), owner);
        Ok(())
    }

    fn emit_late_transitions(&mut self, points: &InstPoints, before: bool) -> Result<(), String> {
        let copies: Vec<_> = self
            .allocation
            .transitions_at(points.late)
            .iter()
            .filter(|transition| transition_before_instruction(**transition) == before)
            .map(|transition| ParallelCopy::between(place(transition.from), place(transition.to)))
            .collect();
        let owner = self.owner_at(points.late);
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner, &copies))?;
        self.emit_moves(plan.moves(), owner);
        Ok(())
    }

    fn emit_transitions(&mut self, point: Point) -> Result<(), String> {
        let copies: Vec<_> = self
            .allocation
            .transitions_at(point)
            .iter()
            .map(|transition| ParallelCopy::between(place(transition.from), place(transition.to)))
            .collect();
        let owner = self.owner_at(point);
        let plan = parallel_copy::plan(&copies, self.copy_temporary(owner, &copies))?;
        self.emit_moves(plan.moves(), owner);
        Ok(())
    }

    /// The block holding `point`: blocks take consecutive runs of points in
    /// order, so it is the last block beginning at or before it.
    fn block_at(&self, point: Point) -> BlockId {
        let after = self
            .liveness
            .blocks
            .partition_point(|layout| layout.entry.index() <= point.index());
        self.liveness.blocks[after - 1].block
    }

    fn owner_at(&self, point: Point) -> FunctionId {
        self.selected.blocks[self.block_at(point)].owner
    }

    /// How many bits `value` can take: what its class says, or fewer where
    /// it was moved down from something narrower than that.
    fn held_width(&self, value: VReg) -> u16 {
        let width = self.selected.widths[value.index()];
        let Some(definition) = self.uses.definitions[value.index()] else {
            return width;
        };
        let definition = self.selected.instructions[definition];
        match definition.immediate {
            Immediate::Shift { up: false, by, .. } => {
                let moved = self.selected.operands[definition.operands.range()][0];
                width.min(self.selected.widths[moved.index()].saturating_sub(u16::from(by)))
            }
            _ => width,
        }
    }

    /// Whether `value` is nought, and nothing but one comparison reads it.
    fn is_only_nought(&self, value: VReg) -> bool {
        self.uses.definitions[value.index()].is_some_and(|definition| {
            self.selected.instructions[definition].immediate == Immediate::Integer(0)
        }) && self.uses.operands[value.index()] == 1
    }

    fn is_unique_constant(&self, value: VReg) -> bool {
        let Some(definition_id) = self.uses.definitions[value.index()] else {
            return false;
        };
        let definition = self.selected.instructions[definition_id];
        let Immediate::Integer(integer) = definition.immediate else {
            return false;
        };
        let Some(block) = self.uses.blocks[definition_id.index()] else {
            return false;
        };
        let block = self.selected.blocks[block];
        self.selected.order[block.instructions.range()]
            .iter()
            .filter(|&&instruction| {
                let instruction = self.selected.instructions[instruction];
                instruction.opcode == Opcode::Constant
                    && instruction.immediate == Immediate::Integer(integer)
            })
            .count()
            == 1
            && self.uses.operands[value.index()] == 1
    }

    fn is_branch_only_result(&self, points: &InstPoints, result: VReg) -> bool {
        let block = self.selected.blocks[self.block_at(points.late)];
        let is_last = self.selected.order[block.instructions.range()]
            .last()
            .is_some_and(|&instruction| instruction == points.instruction);
        let is_condition =
            matches!(block.terminator, Terminator::Branch { condition, .. } if condition == result);
        let uses = self.uses.operands[result.index()] + self.uses.branches[result.index()];
        is_last && is_condition && uses == 1
    }

    /// Lay out each function once, checking every frame-relative access
    /// before emitting anything. A caller reuses one outgoing area for all
    /// its calls; recursion gets a separate area in each activation.
    fn layout_frames(&self) -> Result<Vec<Frame>, String> {
        let mut frames = vec![Frame::default(); self.allocation.spill_slots.len()];
        let mut incoming = vec![0u32; frames.len()];
        for block in &self.selected.blocks {
            for &id in &self.selected.order[block.instructions.range()] {
                let inst = self.selected.instructions[id];
                let Immediate::Slot(slot) = inst.immediate else {
                    continue;
                };
                let count = slot.checked_add(1).ok_or("x86 call area is too large")?;
                let area = match inst.opcode {
                    Opcode::LoadOutgoing | Opcode::StoreOutgoing => {
                        &mut frames[block.owner.index()].outgoing
                    }
                    Opcode::LoadIncoming | Opcode::StoreIncoming => {
                        &mut incoming[block.owner.index()]
                    }
                    _ => unreachable!("a verified stack access"),
                };
                *area = (*area).max(count);
            }
        }
        for (owner, frame) in frames.iter_mut().enumerate() {
            let words = u64::from(frame.outgoing)
                + u64::from(self.allocation.spill_slots[owner])
                + u64::try_from(self.saved[owner].len()).expect("a few registers");
            // The return address is one word above the local frame. Check
            // the incoming area too, not just the sub rsp immediate.
            if (words + 1 + u64::from(incoming[owner])) * 8 > i32::MAX.cast_unsigned().into() {
                return Err("x86 stack frame is too large".to_owned());
            }
            frame.words = u32::try_from(words).expect("a checked frame");
        }
        Ok(frames)
    }

    fn frame(&self, owner: FunctionId) -> u32 {
        self.frames[owner.index()].words
    }

    fn local_slot(&self, owner: FunctionId, slot: FrameSlot) -> FrameSlot {
        FrameSlot::at(self.frames[owner.index()].outgoing + slot.number())
    }

    /// Put what `owner` keeps for its caller in its frame, on entering, or
    /// back, on leaving.
    fn keep_for_caller(&mut self, owner: FunctionId, entering: bool) {
        let first = self.spill_slots(owner);
        let saved = self.saved.get(owner.index()).cloned().unwrap_or_default();
        for (at, reg) in (first..).zip(saved) {
            if entering {
                self.asm
                    .store_slot(reg, self.local_slot(owner, FrameSlot::at(at)));
            } else {
                self.asm
                    .load_slot(reg, self.local_slot(owner, FrameSlot::at(at)));
                self.forget(reg);
            }
        }
    }

    /// For each function but the entry, which never returns, the registers
    /// a call leaves alone that its allocation puts anything in.
    fn kept_for_callers(&self, entry: FunctionId) -> Vec<Vec<Reg>> {
        let mut saved: Vec<Vec<Reg>> = vec![Vec::new(); self.allocation.spill_slots.len()];
        for segment in &self.allocation.segments {
            let Location::Register(reg) = segment.location else {
                continue;
            };
            let owner = self.owner_at(segment.start);
            if owner != entry && CALLEE_SAVED.contains(&reg) && !saved[owner.index()].contains(&reg)
            {
                saved[owner.index()].push(reg);
            }
        }
        saved
    }

    fn spill_slots(&self, owner: FunctionId) -> u32 {
        self.allocation.spill_slots[owner.index()]
    }

    /// Where the allocation breaks a cycle among `copies`: see
    /// [`parallel_copy::temporary`].
    fn copy_temporary(&self, owner: FunctionId, copies: &[ParallelCopy]) -> Option<Place> {
        match parallel_copy::temporary(copies, Some(COPY_SCRATCH)) {
            Place::Frame(_) if self.spill_slots(owner) == 0 => None,
            temporary => Some(temporary),
        }
    }

    /// Write each value made at `point` that ever waits in memory there.
    fn emit_stores(&mut self, point: Point) {
        let owner = self.owner_at(point);
        let stores: Vec<_> = self.allocation.stores_at(point).collect();
        for (reg, SpillSlot(slot)) in stores {
            self.asm
                .store_slot(reg, self.local_slot(owner, FrameSlot::at(slot)));
        }
    }

    fn emit_moves(&mut self, moves: &[CopyMove], owner: FunctionId) {
        self.emit_moves_keeping(moves, &[], owner);
    }

    /// The moves, but for those into memory a value was written to where it
    /// was made, which already hold it -- other than into `defining`, the
    /// slots of the parameters an edge hands values to.
    fn emit_moves_keeping(
        &mut self,
        moves: &[CopyMove],
        defining: &[FrameSlot],
        owner: FunctionId,
    ) {
        for movement in moves {
            let CopySource::Place(source) = movement.source();
            match (source, movement.destination()) {
                (Place::Register(_), Place::Frame(dst))
                    if Allocation::elides(dst) && !defining.contains(&dst) => {}
                (Place::Register(src), Place::Register(dst)) if src != dst => {
                    self.mov_reg(dst, src, RegisterWidth::Word);
                }
                (Place::Frame(src), Place::Register(dst)) => {
                    self.asm.load_slot(dst, self.local_slot(owner, src));
                    self.forget(dst);
                }
                (Place::Register(src), Place::Frame(dst)) => {
                    self.asm.store_slot(src, self.local_slot(owner, dst));
                }
                (Place::Frame(src), Place::Frame(dst)) if src != dst => {
                    self.asm
                        .load_slot(COPY_SCRATCH, self.local_slot(owner, src));
                    self.forget(COPY_SCRATCH);
                    self.asm
                        .store_slot(COPY_SCRATCH, self.local_slot(owner, dst));
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
        let inst = self.selected.instructions[points.instruction];
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
            (
                Opcode::Add | Opcode::Subtract | Opcode::And | Opcode::Or | Opcode::Xor,
                Immediate::Bits(bits),
            ) => {
                let op = match inst.opcode {
                    Opcode::Add => Alu::Add,
                    Opcode::Subtract => Alu::Subtract,
                    Opcode::And => Alu::And,
                    Opcode::Or => Alu::Or,
                    _ => Alu::Xor,
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
            (Opcode::Monus, Immediate::Bits(bits)) => {
                let source = self.selected.operands[inst.operands.range()][1];
                let source_reg = reg(1)?;
                if self.is_unique_constant(source)
                    && self
                        .asm
                        .fold_alu_immediate(Alu::Subtract, result()?, source_reg, bits)
                {
                    self.forget(source_reg);
                } else {
                    self.asm.alu(Alu::Subtract, result()?, source_reg, bits);
                }
                // Nothing borrowed means the difference stands.
                let kept = self.asm.label();
                self.asm.jump_if(Condition::NotBelow, kept);
                self.asm.xor_self(result()?);
                self.asm.bind(kept);
            }
            (Opcode::ShiftUp | Opcode::ShiftDown, Immediate::Bits(_)) => {
                let direction = if inst.opcode == Opcode::ShiftUp {
                    ShiftDirection::Left
                } else {
                    ShiftDirection::Right
                };
                self.asm.shift_by_count(direction, result()?);
            }
            (Opcode::Multiply, Immediate::Bits(_)) => {
                self.asm.multiply(result()?, reg(1)?);
            }
            (Opcode::Float, Immediate::Float(float)) => {
                let right = if float.operation.arity() == 2 {
                    Some(reg(1)?)
                } else {
                    None
                };
                self.asm.float(float, result()?, reg(0)?, right);
            }
            (Opcode::Divide | Opcode::Modulo, Immediate::Bits(_)) => {
                self.emit_division(inst.opcode == Opcode::Modulo);
            }
            (Opcode::Equal | Opcode::Below, Immediate::Bits(bits)) => {
                let source = self.selected.operands[inst.operands.range()][1];
                let source_reg = reg(1)?;
                // Nought read here alone was just written, or the fold
                // finds nothing to take back; the fold forgets the register.
                if (self.is_unique_constant(source) || self.is_only_nought(source))
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
            (
                Opcode::LoadIncoming
                | Opcode::LoadOutgoing
                | Opcode::StoreIncoming
                | Opcode::StoreOutgoing,
                Immediate::Slot(slot),
            ) => {
                let owner = self.owner_at(points.late);
                let incoming = matches!(inst.opcode, Opcode::LoadIncoming | Opcode::StoreIncoming);
                let slot = FrameSlot::at(slot + if incoming { self.frame(owner) + 1 } else { 0 });
                if matches!(inst.opcode, Opcode::LoadIncoming | Opcode::LoadOutgoing) {
                    self.asm.load_slot(result()?, slot);
                } else {
                    self.asm.store_slot(reg(0)?, slot);
                }
            }
            (Opcode::Convert, Immediate::Bits(bits)) => {
                let input = self.selected.operands[inst.operands.range()][0];
                if bits < self.held_width(input) {
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
            (Opcode::WriteFd | Opcode::ReadFd | Opcode::CloseFd, Immediate::None) => {
                let call = match inst.opcode {
                    Opcode::WriteFd => SYS_WRITE,
                    Opcode::ReadFd => SYS_READ,
                    _ => SYS_CLOSE,
                };
                self.materialize(Reg::Rax, call);
                self.asm.syscall();
                self.forget_call_clobbers();
                // The count, or `-errno`, is where the kernel left it.
                let dst = result()?;
                debug_assert_eq!(dst, Reg::Rax);
                self.forget(dst);
            }
            (Opcode::OpenAt, Immediate::None) => {
                // `openat2`'s `how`, on the stack: the flags, the mode a
                // file it makes is given, and that the name resolves
                // beneath where the program runs. Each is pushed before
                // anything is written, so wherever they were held is read
                // as it was.
                self.asm.push_imm8(RESOLVE_BENEATH);
                self.asm.push_reg(reg(3)?);
                self.asm.push_reg(reg(2)?);
                self.asm.mov_reg(Reg::Rdx, Reg::Rsp, RegisterWidth::Word);
                self.materialize(Reg::Rdi, AT_FDCWD);
                self.materialize(Reg::R10, OPEN_HOW_BYTES);
                self.materialize(Reg::Rax, SYS_OPENAT2);
                self.asm.syscall();
                self.forget_call_clobbers();
                for _ in 0..3 {
                    self.asm.pop(Reg::Rcx);
                }
                let dst = result()?;
                debug_assert_eq!(dst, Reg::Rax);
                self.forget(dst);
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
                        .frame(owner)
                        .checked_mul(8)
                        .ok_or_else(|| "x86 entry frame displacement overflows".to_owned())?;
                    self.asm.load_stack(dst, displacement);
                    self.forget(dst);
                }
            }
            (Opcode::ArgumentVector, Immediate::None) => {
                // The count lies just above the entry's frame, and the
                // addresses just above the count.
                let dst = result()?;
                let owner = self.owner_at(points.late);
                let displacement = self
                    .frame(owner)
                    .checked_mul(8)
                    .and_then(|bytes| bytes.checked_add(8))
                    .ok_or_else(|| "x86 entry frame displacement overflows".to_owned())?;
                self.mov_reg(dst, Reg::Rsp, RegisterWidth::Word);
                self.materialize(Reg::Rcx, u64::from(displacement));
                self.asm.alu(Alu::Add, dst, Reg::Rcx, 64);
                self.forget(dst);
            }
            (Opcode::ReadByte, Immediate::None) => {
                let dst = result()?;
                debug_assert_eq!(dst, Reg::Rdx);
                self.materialize(Reg::Rax, SYS_READ);
                self.materialize(Reg::Rdi, STDIN);
                self.materialize(Reg::Rdx, 1);
                self.asm.push_imm8(0);
                self.asm.mov_reg(Reg::Rsi, Reg::Rsp, RegisterWidth::Word);
                self.asm.syscall();
                self.forget_call_clobbers();
                self.asm.pop(dst);
                self.materialize(Reg::Rcx, 1);
                self.asm.alu(Alu::Compare, Reg::Rax, Reg::Rcx, 64);
                self.asm.set_if(Condition::Equal, Reg::Rax);
                self.asm.alu(Alu::Add, dst, Reg::Rax, 64);
                self.forget(dst);
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
        self.known.fill(None);
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
                let owner = self.selected.blocks[layout.block].owner;
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
                    self.keep_for_caller(owner, false);
                    let frame = self.frame(owner);
                    if frame > 0 {
                        self.asm.close_frame(frame);
                    }
                    self.asm.ret();
                }
            }
            Terminator::Halt => {}
        }
        Ok(())
    }

    fn edge_moves(&self, from: BlockId, target: BlockId) -> Result<&[CopyMove], String> {
        let edges = &self.allocation.edge_moves;
        edges[edges.partition_point(|edge| edge.from < from)..]
            .iter()
            .take_while(|edge| edge.from == from)
            .find(|edge| edge.target == target)
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
        let entry = self.liveness.blocks[target.index()].entry;
        let block = self.selected.blocks[target];
        let defining: Vec<_> = self.selected.block_params[block.params.range()]
            .iter()
            .filter_map(|&param| match self.location(entry, param) {
                Ok(Location::Spill(SpillSlot(slot))) => Some(FrameSlot::at(slot)),
                _ => None,
            })
            .collect();
        self.emit_moves_keeping(&moves, &defining, self.selected.blocks[from].owner);
        Ok(())
    }

    fn location(&self, point: Point, value: VReg) -> Result<Location, String> {
        self.allocation
            .location(point, value)
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

/// A value leaves a register before the instruction may write it, into
/// memory or a register the instruction leaves alone; one comes back from
/// memory only after.
const fn transition_before_instruction(transition: Transition) -> bool {
    matches!(transition.from, Location::Register(_))
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
        Width::Bits16 => MemoryWidth::Bits16,
        Width::Bits32 => MemoryWidth::Bits32,
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
