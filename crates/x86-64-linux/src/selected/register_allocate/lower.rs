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
use faun_core::targets::Favour;

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
const SYS_SIGALTSTACK: u64 = 131;
/// What the kernel raises for an address the program may not touch, such
/// as one past the end of its stack.
const SIGSEGV: u64 = 11;
/// `sa_flags`: hand the handler where the fault was, run it on the stack
/// `sigaltstack` names, and return through `sa_restorer`, which x86-64
/// insists on even for a handler that never returns.
const SA_SIGINFO_ONSTACK_RESTORER: u64 = 0x4 | 0x0800_0000 | 0x0400_0000;
/// The stack a fault is handled on: room for the frame the kernel writes,
/// which holds every register state the processor saves, and for the
/// handler's two words.
const SIGNAL_STACK_BYTES: u32 = 16 * 1024;
/// Where `siginfo_t` holds the address that faulted, and where `ucontext_t`
/// holds the `rsp` it faulted at.
const SIGINFO_ADDRESS: i32 = 16;
const UCONTEXT_RSP: i32 = 160;
/// How far a fault may lie above the stack pointer and still be the stack
/// running out, as a power of two: a frame's slots lie above where `rsp`
/// was moved to.
const STACK_FAULT_REACH_BITS: u8 = 16;
/// What a program whose stack ran out says, and the status it ends with:
/// the one after the heap's, two.
const STACK_OVERFLOW_MESSAGE: &[u8; 16] = b"stack overflow\n\0";
const STACK_OVERFLOW_STATUS: u64 = 3;
const SYS_EXIT: u64 = 60;
const STDIN: u64 = 0;
const STDOUT: u64 = 1;
const STDERR: u64 = 2;
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
    (entry, favour, frame_pointers): (FunctionId, Favour, bool),
) -> Result<Allocated, String> {
    let mut lowering = Lowering::new(selected, liveness, allocation);
    lowering.frame_pointers = frame_pointers;
    lowering.run(entry, favour)
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
    /// Whether each function but the entry pushes `rbp` where it starts and
    /// points it at what it pushed, so a profiler can walk the stack from
    /// frame to frame. The entry, which never returns, pushes nothing: Linux
    /// starts a program with `rbp` nought, which ends the chain, and the
    /// entry never holds anything else there.
    frame_pointers: bool,
    /// How many bytes the program's start leaves on the stack above the
    /// entry's frame, below the count of arguments.
    started: u32,
    pending_condition: Option<(VReg, Condition)>,
    exit_epilogue: Option<Label>,
    final_block: Option<BlockId>,
    uses: Uses,
    /// The registers each function keeps for its caller: those a call
    /// leaves alone that it writes, put back before it returns.
    saved: Vec<Vec<Reg>>,
    frames: Vec<Frame>,
    /// Whether each block runs with its function's frame open: see
    /// [`Lowering::open_blocks`].
    opened: Vec<bool>,
}

/// The outgoing call area starts at rsp, followed by allocator spill slots
/// and saved registers. Incoming values lie above this frame and the return
/// address. No call area overlaps a live spill or its caller's incoming area.
#[derive(Clone, Copy, Default)]
struct Frame {
    outgoing: u32,
    words: u32,
    /// How many words of arguments it reads from its caller's frame.
    incoming: u32,
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
            frame_pointers: false,
            started: 0,
            pending_condition: None,
            exit_epilogue: None,
            final_block: None,
            uses: Uses::new(selected),
            saved: Vec::new(),
            opened: Vec::new(),
            frames: Vec::new(),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one ordered lowering walk over allocated blocks"
    )]
    fn run(mut self, entry: FunctionId, favour: Favour) -> Result<Allocated, String> {
        self.configure_program(entry);
        self.saved = self.kept_for_callers(entry);
        self.frames = self.layout_frames()?;
        // Favouring size, every function opens its frame where it starts:
        // shrink-wrapped, it opens and closes it on each way into and out of
        // the blocks needing it, more code than once at its start.
        self.opened = match favour {
            Favour::Speed => self.open_blocks(entry),
            Favour::Size => vec![true; self.selected.blocks.len()],
        };
        self.report_stack_overflow();
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
                let label = self.block_labels[layout.block.index()];
                self.asm.starts(function.source, label);
                self.enter_function(function.source, entry);
                if self.opened[layout.block.index()] {
                    self.open_frame(function.source);
                }
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
        self.uses_any(&[Opcode::Write, Opcode::WriteFd])
    }

    /// Whether any instruction is one of `opcodes`.
    fn uses_any(&self, opcodes: &[Opcode]) -> bool {
        self.liveness.blocks.iter().any(|layout| {
            layout.instructions.iter().any(|points| {
                opcodes.contains(&self.selected.instructions[points.instruction].opcode)
            })
        })
    }

    /// Before anything else runs in a program that writes, ignore `SIGPIPE`,
    /// so a write to a pipe nobody reads answers `EPIPE` as a value, as it
    /// does on every other target, rather than ending the program from
    /// inside the write. A program that never writes pays nothing.
    /// `rt_sigaction` reads the kernel's `struct sigaction` from the stack:
    /// the handler, `SIG_IGN`, then flags, restorer and mask, all nought.
    /// Nothing is live yet, and the stack is as the start left it once the
    /// four words are popped, which matters only to a program reading what
    /// the kernel left there: the arguments. One that does not leaves the
    /// words where they are, still sixteen-byte aligned. A program that
    /// starts another must restore the default in the child, which inherits
    /// the disposition.
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
        if self.argument_count_in_rbx
            || self.uses_any(&[Opcode::ArgumentCount, Opcode::ArgumentVector])
        {
            for _ in 0..4 {
                self.asm.pop(Reg::Rcx);
            }
        }
        self.known.fill(None);
    }

    /// Whether some function can call itself, directly or through others,
    /// so that how deep calls go rests on what the program is handed. Every
    /// function calling nothing is taken away, then every caller that leaves
    /// calling nothing, until none does; what stands at the end calls round.
    fn recurses(&self) -> bool {
        let count = self.function_labels.len();
        let mut calls = vec![0usize; count];
        let mut callers = vec![Vec::new(); count];
        for block in &self.selected.blocks {
            for &id in &self.selected.order[block.instructions.range()] {
                let inst = self.selected.instructions[id];
                if let (Opcode::Call, Immediate::Function(callee)) = (inst.opcode, inst.immediate) {
                    calls[block.owner.index()] += 1;
                    callers[callee.index()].push(block.owner.index());
                }
            }
        }
        let mut leaves: Vec<usize> = (0..count).filter(|&at| calls[at] == 0).collect();
        let mut taken = 0;
        while let Some(leaf) = leaves.pop() {
            taken += 1;
            for &caller in &callers[leaf] {
                calls[caller] -= 1;
                if calls[caller] == 0 {
                    leaves.push(caller);
                }
            }
        }
        taken < count
    }

    /// Before anything else runs in a program whose calls can go round,
    /// have a fault at the end of the stack say `stack overflow` on
    /// standard error and end the program with status 3, rather than end it
    /// with `SIGSEGV` and nothing said. A program whose calls cannot go round
    /// pays nothing, and one that can pays nothing until the fault.
    ///
    /// The fault is handled on a stack of its own, since the program's has
    /// no room left: the top of the program's own, which calls going deep
    /// reach last. `sigaltstack` reads the kernel's `stack_t` from the
    /// stack: where it starts, flags, and its size. `push rsp` pushes where
    /// the stack was before it, so the handler's stack starts at the flags
    /// and holds them and the size, which nothing reads again. The
    /// program's stack goes on below, sixteen-byte aligned as it was.
    ///
    /// Then `rt_sigaction` reads the handler, flags, restorer and mask from
    /// the stack too. The handler is written just after a call that steps
    /// over it, so the call pushes the handler's address. The restorer is
    /// never reached, as the handler never returns.
    fn report_stack_overflow(&mut self) {
        if !self.recurses() {
            return;
        }
        // The handler's stack, then the `stack_t` naming it.
        self.asm.open_frame(SIGNAL_STACK_BYTES / 8 - 1);
        self.materialize(Reg::Rax, u64::from(SIGNAL_STACK_BYTES));
        self.asm.push_reg(Reg::Rax);
        // Nought is the flags, and where no old stack is to be written.
        self.materialize(Reg::Rsi, 0);
        self.asm.push_reg(Reg::Rsi);
        self.asm.push_reg(Reg::Rsp);
        self.asm.mov_reg(Reg::Rdi, Reg::Rsp, RegisterWidth::Word);
        self.materialize(Reg::Rax, SYS_SIGALTSTACK);
        self.asm.syscall();
        self.forget_call_clobbers();

        // The mask and the restorer are the nought `rsi` still holds, which
        // `syscall` leaves alone.
        self.asm.push_reg(Reg::Rsi);
        self.asm.push_reg(Reg::Rsi);
        self.materialize(Reg::Rax, SA_SIGINFO_ONSTACK_RESTORER);
        self.asm.push_reg(Reg::Rax);
        let install = self.asm.label();
        self.asm.call(install);
        self.handle_stack_fault();
        self.asm.bind(install);
        self.known.fill(None);
        self.asm.mov_reg(Reg::Rsi, Reg::Rsp, RegisterWidth::Word);
        self.materialize(Reg::Rdi, SIGSEGV);
        // Nought is also where no old action is to be written.
        self.materialize(Reg::Rdx, 0);
        self.materialize(Reg::R10, SIGSET_BYTES);
        self.materialize(Reg::Rax, SYS_RT_SIGACTION);
        self.asm.syscall();
        self.known.fill(None);
        // What was opened, the three words of `stack_t`, then the action's
        // four.
        self.started = SIGNAL_STACK_BYTES - 8 + 3 * 8 + 4 * 8;
    }

    /// The handler, run with the `siginfo_t` in `rsi` and the `ucontext_t`
    /// in `rdx`. A fault where the stack ends lies just below the `rsp` it
    /// faulted at, where a call or push writes, or a little above it, in a
    /// frame just opened. Any other fault is no fault of the stack, and
    /// says nothing: the handler faults in turn, with `SIGSEGV` held back
    /// while it runs, so the kernel ends the program with it as before.
    fn handle_stack_fault(&mut self) {
        self.known.fill(None);
        let other = self.asm.label();
        self.asm
            .load(MemoryWidth::Word, Reg::Rax, Reg::Rsi, SIGINFO_ADDRESS);
        self.asm
            .load(MemoryWidth::Word, Reg::Rcx, Reg::Rdx, UCONTEXT_RSP);
        self.asm.alu(Alu::Subtract, Reg::Rax, Reg::Rcx, 64);
        self.asm.alu_immediate(Alu::Add, Reg::Rax, 8, 64);
        self.asm
            .shift(ShiftDirection::Right, Reg::Rax, STACK_FAULT_REACH_BITS, 64);
        self.asm.jump_if(Condition::NotEqual, other);
        let (first, second) = STACK_OVERFLOW_MESSAGE.split_at(8);
        for word in [second, first] {
            let word = u64::from_le_bytes(word.try_into().expect("eight bytes"));
            self.materialize(Reg::Rax, word);
            self.asm.push_reg(Reg::Rax);
        }
        self.asm.mov_reg(Reg::Rsi, Reg::Rsp, RegisterWidth::Word);
        self.materialize(Reg::Rdi, STDERR);
        let length = STACK_OVERFLOW_MESSAGE.len() - 1;
        self.materialize(Reg::Rdx, u64::try_from(length).expect("a short message"));
        self.materialize(Reg::Rax, SYS_WRITE);
        self.asm.syscall();
        self.forget_call_clobbers();
        self.materialize(Reg::Rdi, STACK_OVERFLOW_STATUS);
        self.materialize(Reg::Rax, SYS_EXIT);
        self.asm.syscall();
        self.asm.bind(other);
        self.asm.halt();
    }

    fn enter_function(&mut self, function: FunctionId, entry: FunctionId) {
        if function == entry && self.argument_count_in_rbx {
            self.asm.load_stack(Reg::Rbx, self.started);
        }
        if self.frame_pointers && function != entry {
            self.asm.push_reg(Reg::Rbp);
            self.asm.mov_reg(Reg::Rbp, Reg::Rsp, RegisterWidth::Word);
        }
    }

    /// Words between a function's frame and the arguments its caller left:
    /// the return address, and the caller's `rbp` where frames are chained.
    const fn above_frame(&self) -> u32 {
        if self.frame_pointers { 2 } else { 1 }
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
            // The return address, and a chained frame pointer, are above the
            // local frame. Check the incoming area too, not just the sub rsp
            // immediate.
            if (words + u64::from(self.above_frame()) + u64::from(incoming[owner])) * 8
                > i32::MAX.cast_unsigned().into()
            {
                return Err("x86 stack frame is too large".to_owned());
            }
            frame.words = u32::try_from(words).expect("a checked frame");
            frame.incoming = incoming[owner];
        }
        Ok(frames)
    }

    fn frame(&self, owner: FunctionId) -> u32 {
        self.frames[owner.index()].words
    }

    /// Whether the function starting at `label` may be jumped to in place
    /// of a return: it reads no arguments from its caller's frame, which a
    /// jump leaves as the caller's caller's.
    fn callable_in_tail(&self, label: Label) -> bool {
        self.function_labels
            .iter()
            .position(|&start| start == Some(label))
            .is_some_and(|function| self.frames[function].incoming == 0)
    }

    fn local_slot(&self, owner: FunctionId, slot: FrameSlot) -> FrameSlot {
        FrameSlot::at(self.frames[owner.index()].outgoing + slot.number())
    }

    /// Put back what `owner` keeps for its caller, and give up its frame.
    fn close_frame(&mut self, owner: FunctionId) {
        self.keep_for_caller(owner, false);
        let frame = self.frame(owner);
        if frame > 0 {
            self.asm.close_frame(frame);
        }
    }

    /// Make room for `owner`'s frame, and keep there what it keeps for its
    /// caller.
    fn open_frame(&mut self, owner: FunctionId) {
        let frame = self.frame(owner);
        if frame > 0 {
            self.asm.open_frame(frame);
        }
        self.keep_for_caller(owner, true);
    }

    /// Which blocks run with their function's frame open.
    ///
    /// A block touches the frame where a value lives in memory or in a
    /// register a call leaves alone during it, where it writes a value to
    /// memory, where it reads or writes the stack around a call, or where
    /// the way out of it writes memory. A block from which no such block
    /// can be reached runs without the frame. Any other block that one
    /// touching the frame reaches runs with it, and so does each touching
    /// it. The rest run without it. A way from a block without the frame to
    /// one with it opens the frame, and a way from one with it to one
    /// without closes it, after the way's moves: so a function whose early
    /// way out touches nothing returns from there without saving what it
    /// keeps for its caller, or making room it never uses, and a way out
    /// that one touching the frame shares closes it before going on. The
    /// entry, which never returns, and a function with no frame open it at
    /// once, as before.
    fn open_blocks(&self, entry: FunctionId) -> Vec<bool> {
        let blocks = &self.liveness.blocks;
        let needs = self.needing_frame(entry);
        // Whether no block needing the frame can be reached from each, as
        // the largest set closed under going on.
        let mut free: Vec<bool> = needs.iter().map(|&needed| !needed).collect();
        let mut changed = true;
        while changed {
            changed = false;
            for layout in blocks.iter().rev() {
                let at = layout.block.index();
                if free[at]
                    && successors(self.selected.blocks[layout.block].terminator)
                        .into_iter()
                        .flatten()
                        .any(|target| !free[target.index()])
                {
                    free[at] = false;
                    changed = true;
                }
            }
        }
        let mut opened = needs;
        let mut pending: Vec<_> = (0..opened.len()).filter(|&at| opened[at]).collect();
        while let Some(at) = pending.pop() {
            for target in successors(self.selected.blocks[BlockId::at(at)].terminator)
                .into_iter()
                .flatten()
            {
                if !opened[target.index()] && !free[target.index()] {
                    opened[target.index()] = true;
                    pending.push(target.index());
                }
            }
        }
        opened
    }

    /// Which blocks touch the frame, as [`Self::open_blocks`] says, or are
    /// in a function that opens it at once.
    fn needing_frame(&self, entry: FunctionId) -> Vec<bool> {
        let touching = self.points_touching_frame();
        let mut needs = vec![false; self.selected.blocks.len()];
        for layout in &self.liveness.blocks {
            let block = self.selected.blocks[layout.block];
            let (first, last) = (layout.entry.index(), layout.terminator.index());
            needs[layout.block.index()] = block.owner == entry
                || self.frame(block.owner) == 0
                || touching[last + 1] > touching[first]
                || self.selected.order[block.instructions.range()]
                    .iter()
                    .any(|&id| self.selected.instructions[id].opcode.reaches_the_stack())
                || successors(block.terminator)
                    .into_iter()
                    .flatten()
                    .any(|target| self.edge_touches_frame(layout.block, target));
        }
        needs
    }

    /// How many points before each touch the frame: where a value in memory
    /// or in a register a call leaves alone is live, or a value is stored.
    fn points_touching_frame(&self) -> Vec<u32> {
        let points = self
            .liveness
            .blocks
            .last()
            .map_or(0, |layout| layout.terminator.index() + 1);
        // How many values touching the frame are live from each point on,
        // and then whether any is, at each point.
        let mut touched = vec![0i64; points + 1];
        for segment in &self.allocation.segments {
            let frame = match segment.location {
                Location::Spill(_) => true,
                Location::Register(reg) => CALLEE_SAVED.contains(&reg),
            };
            if frame {
                touched[segment.start.index()] += 1;
                touched[segment.end.index().min(points)] -= 1;
            }
        }
        let mut live = 0;
        let mut before = vec![0u32; points + 1];
        for at in 0..points {
            live += touched[at];
            let stored = self
                .allocation
                .stores_at(Point::at(at).expect("a point"))
                .next()
                .is_some();
            before[at + 1] = before[at] + u32::from(live > 0 || stored);
        }
        before
    }

    /// Whether the moves on the way from `from` to `target` read or write
    /// memory.
    fn edge_touches_frame(&self, from: BlockId, target: BlockId) -> bool {
        self.edge_moves(from, target).is_ok_and(|moves| {
            moves.iter().any(|movement| {
                let CopySource::Place(source) = movement.source();
                matches!(source, Place::Frame(_))
                    || matches!(movement.destination(), Place::Frame(_))
            })
        })
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
            (Opcode::Multiply, Immediate::Bits(bits)) => {
                let source = self.selected.operands[inst.operands.range()][1];
                let source_reg = reg(1)?;
                if self.is_unique_constant(source)
                    && self
                        .asm
                        .fold_multiply_immediate(result()?, source_reg, bits)
                {
                    self.forget(source_reg);
                } else {
                    self.asm.multiply(result()?, source_reg);
                }
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
                let slot = FrameSlot::at(
                    slot + if incoming {
                        self.frame(owner) + self.above_frame()
                    } else {
                        0
                    },
                );
                if matches!(inst.opcode, Opcode::LoadIncoming | Opcode::LoadOutgoing) {
                    self.asm.load_slot(result()?, slot);
                } else {
                    self.asm.store_slot(reg(0)?, slot);
                }
            }
            (Opcode::Convert, Immediate::None) => {}
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
                        .and_then(|bytes| bytes.checked_add(self.started))
                        .ok_or_else(|| "x86 entry frame displacement overflows".to_owned())?;
                    self.asm.load_stack(dst, displacement);
                    self.forget(dst);
                }
            }
            (Opcode::ArgumentVector, Immediate::None) => {
                // The count lies just above the entry's frame and what the
                // start left, and the addresses just above the count.
                let dst = result()?;
                let owner = self.owner_at(points.late);
                let displacement = self
                    .frame(owner)
                    .checked_mul(8)
                    .and_then(|bytes| bytes.checked_add(self.started + 8))
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
                let edges_are_empty = self.edge_is_empty(layout.block, then_target)?
                    && self.edge_is_empty(layout.block, else_target)?;
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
                    // A call whose answer is the answer, made last, is a
                    // jump once the frame is gone: what it calls returns
                    // to this function's caller.
                    let tail = self
                        .asm
                        .last_call()
                        .filter(|&callee| self.callable_in_tail(callee));
                    if tail.is_some() {
                        self.asm.take_last_call();
                    }
                    if self.opened[layout.block.index()] {
                        self.close_frame(owner);
                    }
                    if self.frame_pointers {
                        self.asm.pop(Reg::Rbp);
                    }
                    match tail {
                        Some(callee) => self.asm.jump(callee),
                        None => self.asm.ret(),
                    }
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

    /// Whether the way from `from` to `target` writes nothing of its own.
    fn edge_is_empty(&self, from: BlockId, target: BlockId) -> Result<bool, String> {
        Ok(self.edge_moves(from, target)?.is_empty()
            && self.opened[from.index()] == self.opened[target.index()])
    }

    /// Whether the way from `from` to `target` opens the frame: `from` runs
    /// without it, and `target` with it.
    fn opens(&self, from: BlockId, target: BlockId) -> bool {
        !self.opened[from.index()] && self.opened[target.index()]
    }

    fn emit_edge(&mut self, from: BlockId, target: BlockId) -> Result<(), String> {
        if self.opens(from, target) {
            self.open_frame(self.selected.blocks[from].owner);
        }
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
        let owner = self.selected.blocks[from].owner;
        self.emit_moves_keeping(&moves, &defining, owner);
        if self.opened[from.index()] && !self.opened[target.index()] {
            self.close_frame(owner);
        }
        Ok(())
    }

    fn location(&self, point: Point, value: VReg) -> Result<Location, String> {
        self.allocation
            .location(point, value)
            .ok_or_else(|| format!("x86 v{} has no allocated segment", value.index()))
    }
}

/// The blocks a block may go on to.
const fn successors(terminator: Terminator) -> [Option<BlockId>; 2] {
    match terminator {
        Terminator::Jump { target, .. } => [Some(target), None],
        Terminator::Branch {
            then_target,
            else_target,
            ..
        } => [Some(then_target), Some(else_target)],
        Terminator::Return { .. } | Terminator::Halt => [None, None],
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
