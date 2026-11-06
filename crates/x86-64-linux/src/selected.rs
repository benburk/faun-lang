//! Selected x86-64 SSA instructions and control-flow.
//!
//! This target-owned phase turns structured machine-IR regions into ordinary
//! target blocks and edges. Source value identity remains virtual-register
//! identity until segmented allocation lowers the CFG to
//! [`super::machine::Allocated`].

mod register_allocate;

use super::machine::Reg;
use crate::{ARG_COUNT, WORD_BITS};
use faun_core::index::{Pool, Range};
use faun_core::ir::{
    Binary, Class, DataId, Exit, FunctionId, Offset, Op as SourceOp, Program, RegionId, Relation,
    Terminator as SourceTerminator, ValueId, Width,
};

pub(crate) use faun_core::codegen::registers::{BlockId, InstId, Role, Timing, VReg};

/// Where an operand of one of these instructions must be.
pub(crate) type Constraint = faun_core::codegen::registers::Constraint<Reg>;
pub(crate) type OperandSpec = faun_core::codegen::registers::OperandSpec<Reg>;

/// A value's virtual register is its number.
fn vreg(value: ValueId) -> VReg {
    VReg::at(value.index())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Access {
    None,
    Read,
    Write,
    ReadWrite,
    Unknown,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct RegSet(u32);

impl RegSet {
    #[expect(
        clippy::as_conversions,
        reason = "register discriminants are bit indices"
    )]
    const fn of(regs: &[Reg]) -> Self {
        let mut bits = 0;
        let mut at = 0;
        while at < regs.len() {
            bits |= 1 << (regs[at] as u8);
            at += 1;
        }
        Self(bits)
    }

    #[expect(
        clippy::as_conversions,
        reason = "register discriminants are bit indices"
    )]
    pub(crate) const fn contains(self, reg: Reg) -> bool {
        self.0 & (1 << (reg as u8)) != 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Effects {
    pub memory: Access,
    pub flags: Access,
    pub control: bool,
    pub clobbers: RegSet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expansion {
    Single,
    Optional,
    Sequence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Requirements {
    pub expansion: Expansion,
    pub scratch: RegSet,
    pub effects: Effects,
}

impl Effects {
    const PURE: Self = Self {
        memory: Access::None,
        flags: Access::None,
        control: false,
        clobbers: RegSet(0),
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Opcode {
    Constant,
    DataAddress,
    Add,
    Subtract,
    /// Saturating subtraction at its operands' width: a subtraction, and a
    /// zero where it borrowed.
    Monus,
    Multiply,
    Divide,
    Modulo,
    And,
    Or,
    Xor,
    /// Moved up or down by the distance in `rcx`, below the word.
    ShiftUp,
    ShiftDown,
    Equal,
    Below,
    Load,
    Store,
    Convert,
    Shift,
    Call,
    /// Read a stack argument from the caller's outgoing area.
    LoadIncoming,
    /// Write a stack result to the caller's outgoing area.
    StoreIncoming,
    /// Read a stack result after a call.
    LoadOutgoing,
    /// Write a stack argument before a call.
    StoreOutgoing,
    Write,
    /// Bytes where they lie to what a descriptor names, or from it to where
    /// they are to lie: how many moved, or `-errno`.
    WriteFd,
    ReadFd,
    /// A name, ended by a nought byte, opened beneath where the program
    /// runs: the descriptor, or `-errno`.
    OpenAt,
    /// A descriptor given up: nought, or `-errno`.
    CloseFd,
    Exit,
    Grow,
    ArgumentCount,
    /// Where the arguments' addresses lie: just past the count.
    ArgumentVector,
    ReadByte,
    /// IEEE 754 arithmetic on scalar patterns allocated to XMM registers.
    Float,
}

impl Opcode {
    /// Whether it reads or writes the stack around a call: the arguments
    /// a call hands on it, or those its function was handed there.
    pub(crate) const fn reaches_the_stack(self) -> bool {
        matches!(
            self,
            Self::LoadOutgoing | Self::StoreOutgoing | Self::LoadIncoming | Self::StoreIncoming
        )
    }

    /// Whether it is worked out where its first operand was, whichever
    /// register that is.
    const fn in_place(self) -> bool {
        matches!(
            self,
            Self::Add
                | Self::Multiply
                | Self::Subtract
                | Self::And
                | Self::Or
                | Self::Xor
                | Self::ShiftUp
                | Self::ShiftDown
                | Self::Monus
                | Self::Convert
                | Self::Shift
        )
    }

    /// Which register each operand is handed in, for a call the kernel
    /// answers, where the operand is read there.
    const fn syscall_operand(self, at: usize) -> Option<Reg> {
        match (self, at) {
            (Self::Write | Self::OpenAt, 0) | (Self::WriteFd | Self::ReadFd, 1) => Some(Reg::Rsi),
            (Self::Write, 1) | (Self::WriteFd | Self::ReadFd, 2) => Some(Reg::Rdx),
            (Self::WriteFd | Self::ReadFd | Self::CloseFd, 0) => Some(Reg::Rdi),
            _ => None,
        }
    }

    /// Where what it answers is left.
    const fn answered_in(self) -> Constraint {
        match self {
            Self::Divide
            | Self::Modulo
            | Self::Call
            | Self::WriteFd
            | Self::ReadFd
            | Self::OpenAt
            | Self::CloseFd
            | Self::Grow => Constraint::Fixed(Reg::Rax),
            Self::ReadByte => Constraint::Fixed(Reg::Rdx),
            _ => Constraint::Any,
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one centralized expansion, scratch, and effect declaration per selected opcode"
    )]
    pub(crate) const fn requirements(self) -> Requirements {
        let arithmetic = Effects {
            flags: Access::Write,
            ..Effects::PURE
        };
        let call = Effects {
            memory: Access::Unknown,
            flags: Access::Unknown,
            control: true,
            clobbers: RegSet::of(&[
                Reg::Rax,
                Reg::Rcx,
                Reg::Rdx,
                Reg::Rsi,
                Reg::Rdi,
                Reg::R8,
                Reg::R9,
                Reg::R10,
                Reg::R11,
                Reg::Xmm0,
                Reg::Xmm1,
                Reg::Xmm2,
                Reg::Xmm3,
                Reg::Xmm4,
                Reg::Xmm5,
                Reg::Xmm6,
                Reg::Xmm7,
                Reg::Xmm8,
                Reg::Xmm9,
                Reg::Xmm10,
                Reg::Xmm11,
                Reg::Xmm12,
                Reg::Xmm13,
                Reg::Xmm14,
                Reg::Xmm15,
            ]),
        };
        let effects = match self {
            // A small constant may use push/pop, so the selected contract
            // exposes possible stack traffic even when other recipes need one
            // instruction.
            Self::Constant => Effects {
                memory: Access::ReadWrite,
                ..Effects::PURE
            },
            Self::DataAddress
            | Self::Convert
            | Self::ArgumentCount
            // Comparison and setcc are one atomic selected pseudo. Their
            // internal flags do not escape the pseudo.
            | Self::Equal
            | Self::Below
            // SSE arithmetic leaves the flags as they were.
            | Self::Float => Effects::PURE,
            Self::Add
            | Self::Multiply
            | Self::Subtract
            | Self::Monus
            | Self::And
            | Self::Or
            | Self::Xor
            | Self::ShiftUp
            | Self::ShiftDown
            | Self::Shift => arithmetic,
            Self::ArgumentVector => Effects {
                clobbers: RegSet::of(&[Reg::Rcx]),
                ..arithmetic
            },
            Self::Divide | Self::Modulo => Effects {
                clobbers: RegSet::of(&[Reg::Rdx]),
                ..arithmetic
            },
            Self::Load | Self::LoadIncoming | Self::LoadOutgoing => Effects {
                memory: Access::Read,
                ..Effects::PURE
            },
            Self::Store | Self::StoreIncoming | Self::StoreOutgoing => Effects {
                memory: Access::Write,
                ..Effects::PURE
            },
            Self::Call => call,
            Self::Write
            | Self::WriteFd
            | Self::ReadFd
            | Self::OpenAt
            | Self::CloseFd
            | Self::Exit
            | Self::Grow
            | Self::ReadByte => {
                let scratch = match self {
                    Self::Write => RegSet::of(&[Reg::Rax, Reg::Rdi]),
                    Self::OpenAt => RegSet::of(&[Reg::Rdi, Reg::Rdx, Reg::R10]),
                    Self::Exit => RegSet::of(&[Reg::Rax]),
                    Self::Grow => RegSet::of(&[Reg::Rdi, Reg::Rdx, Reg::R10, Reg::R8, Reg::R9]),
                    Self::ReadByte => RegSet::of(&[Reg::Rax, Reg::Rcx, Reg::Rdi, Reg::Rsi]),
                    _ => RegSet(0),
                };
                Effects {
                    memory: Access::Unknown,
                    flags: Access::Unknown,
                    control: true,
                    clobbers: RegSet(
                        scratch.0 | RegSet::of(&[Reg::Rax, Reg::Rcx, Reg::R11]).0,
                    ),
                }
            }
        };
        let expansion = match self {
            Self::Convert => Expansion::Optional,
            Self::Constant
            | Self::Divide
            | Self::Modulo
            | Self::Equal
            | Self::Below
            | Self::Write
            | Self::WriteFd
            | Self::ReadFd
            | Self::OpenAt
            | Self::CloseFd
            | Self::Exit
            | Self::Grow
            | Self::ReadByte
            | Self::ArgumentVector
            | Self::Float => Expansion::Sequence,
            _ => Expansion::Single,
        };
        let scratch = match self {
            Self::Divide | Self::Modulo => RegSet::of(&[Reg::Rdx]),
            Self::Write => RegSet::of(&[Reg::Rax, Reg::Rdi]),
            Self::OpenAt => RegSet::of(&[Reg::Rdi, Reg::Rdx, Reg::R10]),
            Self::Exit => RegSet::of(&[Reg::Rax]),
            Self::Grow => RegSet::of(&[Reg::Rdi, Reg::Rdx, Reg::R10, Reg::R8, Reg::R9]),
            Self::ReadByte => RegSet::of(&[Reg::Rax, Reg::Rcx, Reg::Rdi, Reg::Rsi]),
            Self::ArgumentVector => RegSet::of(&[Reg::Rcx]),
            _ => RegSet(0),
        };
        Requirements {
            expansion,
            scratch,
            effects,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Immediate {
    None,
    Integer(u64),
    Data(DataId),
    Bits(u16),
    Memory {
        width: Width,
        offset: Offset,
    },
    Shift {
        up: bool,
        by: u8,
        bits: u16,
    },
    Function(FunctionId),
    Float(faun_core::float::Float),
    /// A word slot in a call's area: overflow arguments, then overflow results.
    Slot(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Inst {
    opcode: Opcode,
    result: Option<VReg>,
    operands: Range,
    immediate: Immediate,
}

const GPRS: faun_core::codegen::RegSet = faun_core::codegen::RegSet(0xFFFF);
const XMMS: faun_core::codegen::RegSet = faun_core::codegen::RegSet(0xFFFF_0000);
const SCALARS: faun_core::codegen::RegSet = faun_core::codegen::RegSet(0xFFFF_FFFF);

impl Inst {
    fn operand_spec(self, at: usize) -> Option<OperandSpec> {
        let def = usize::from(self.result.is_some());
        if at < def {
            return Some(OperandSpec {
                role: Role::Def,
                timing: Timing::Late,
                constraint: self.opcode.answered_in(),
                allowed: self.allowed(true, 0),
            });
        }
        let use_at = at.checked_sub(def)?;
        let constraint = match self.opcode {
            Opcode::Float
                if use_at == 0
                    && matches!(self.immediate, Immediate::Float(float) if float.operation.arity() == 2) =>
            {
                Constraint::Tied(0)
            }
            op if op.in_place() && use_at == 0 => Constraint::Tied(0),
            Opcode::Divide | Opcode::Modulo if use_at == 0 => Constraint::Fixed(Reg::Rax),
            Opcode::ShiftUp | Opcode::ShiftDown | Opcode::Divide | Opcode::Modulo
                if use_at == 1 =>
            {
                Constraint::Fixed(Reg::Rcx)
            }
            Opcode::Call => abi_register(use_at).map(Constraint::Fixed)?,
            Opcode::Grow if use_at == 0 => Constraint::Fixed(Reg::Rsi),
            op if let Some(reg) = op.syscall_operand(use_at) => Constraint::Fixed(reg),
            Opcode::Exit if use_at == 0 => Constraint::Fixed(Reg::Rdi),
            _ => Constraint::Any,
        };
        Some(OperandSpec {
            role: Role::Use,
            timing: Timing::Early,
            constraint,
            allowed: self.allowed(false, use_at),
        })
    }

    fn allowed(self, result: bool, use_at: usize) -> faun_core::codegen::RegSet {
        match self.opcode {
            Opcode::Float => XMMS,
            // Every scalar already fits a word: this conversion emits no
            // instruction and must not force an otherwise floating chain
            // through the integer bank.
            Opcode::Convert if self.immediate == Immediate::Bits(64) => SCALARS,
            Opcode::Load
                if result
                    && matches!(
                        self.immediate,
                        Immediate::Memory {
                            width: Width::Word | Width::Bits32,
                            ..
                        }
                    ) =>
            {
                SCALARS
            }
            Opcode::Store
                if !result
                    && use_at == 1
                    && matches!(
                        self.immediate,
                        Immediate::Memory {
                            width: Width::Word | Width::Bits32,
                            ..
                        }
                    ) =>
            {
                SCALARS
            }
            Opcode::LoadIncoming
            | Opcode::LoadOutgoing
            | Opcode::StoreIncoming
            | Opcode::StoreOutgoing => SCALARS,
            _ => GPRS,
        }
    }
}

const fn abi_register(at: usize) -> Option<Reg> {
    match at {
        0 => Some(Reg::Rdi),
        1 => Some(Reg::Rsi),
        2 => Some(Reg::Rdx),
        3 => Some(Reg::Rcx),
        4 => Some(Reg::R8),
        5 => Some(Reg::R9),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Terminator {
    Jump {
        target: BlockId,
        args: Range,
    },
    Branch {
        condition: VReg,
        then_target: BlockId,
        then_args: Range,
        else_target: BlockId,
        else_args: Range,
    },
    Return {
        values: Range,
    },
    Halt,
}

impl Terminator {
    fn return_operand_spec(self, at: usize) -> Option<OperandSpec> {
        match self {
            Self::Return { values } if at < values.len() => Some(OperandSpec {
                role: Role::Use,
                timing: Timing::Early,
                constraint: Constraint::Fixed(Reg::Rax),
                allowed: GPRS,
            }),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Block {
    owner: FunctionId,
    params: Range,
    instructions: Range,
    terminator: Terminator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Function {
    source: FunctionId,
    entry: BlockId,
    stack_params: usize,
    stack_results: usize,
}

#[derive(Clone, Debug)]
struct Definition {
    owner: FunctionId,
    block: BlockId,
    position: Option<usize>,
    description: String,
}

#[derive(Debug)]
struct Dominators {
    immediate: Vec<Option<BlockId>>,
}

impl Dominators {
    fn contains(&self, dominator: BlockId, block: BlockId) -> bool {
        let mut cursor = block;
        loop {
            if cursor == dominator {
                return true;
            }
            let Some(parent) = self.immediate[cursor.index()] else {
                return false;
            };
            if parent == cursor {
                return false;
            }
            cursor = parent;
        }
    }
}

#[derive(Debug)]
pub(crate) struct Selected {
    widths: Vec<u16>,
    operands: Vec<VReg>,
    instructions: Pool<InstId, Inst>,
    order: Vec<InstId>,
    block_params: Vec<VReg>,
    block_param_specs: Vec<OperandSpec>,
    blocks: Pool<BlockId, Block>,
    functions: Vec<Function>,
}

impl Selected {
    #[expect(
        clippy::too_many_lines,
        reason = "the phase boundary verifies all flat pools in one pass"
    )]
    fn verify(&self) -> Result<(), String> {
        if self.widths.iter().any(|&width| width > WORD_BITS) {
            return Err("x86 selected value is wider than 64 bits".to_owned());
        }
        let mut definitions = vec![None; self.widths.len()];
        let mut instruction_owners = vec![0_u8; self.instructions.len()];
        for function in &self.functions {
            let entry = self
                .blocks
                .get(function.entry)
                .ok_or_else(|| format!("x86 function {:?} has no entry block", function.source))?;
            if entry.owner != function.source {
                return Err(format!(
                    "x86 function {:?} has a foreign entry block",
                    function.source
                ));
            }
            for (at, spec) in self.block_param_specs[entry.params.range()]
                .iter()
                .enumerate()
            {
                if spec.constraint
                    != Constraint::Fixed(
                        abi_register(at).ok_or_else(|| {
                            "x86 entry block has more than six parameters".to_owned()
                        })?,
                    )
                {
                    return Err(format!(
                        "x86 function {:?} parameter {at} lacks its ABI register",
                        function.source
                    ));
                }
            }
        }
        for (at, block) in self.blocks.iter().enumerate() {
            let block_id = BlockId::at(at);
            if !self
                .functions
                .iter()
                .any(|function| function.source == block.owner)
            {
                return Err(format!("x86 block b{at} has no owning function"));
            }
            Self::verify_range(block.params, self.block_params.len(), "block parameters")?;
            Self::verify_range(
                block.params,
                self.block_param_specs.len(),
                "block parameter constraints",
            )?;
            for spec in &self.block_param_specs[block.params.range()] {
                if spec.role != Role::Def || spec.timing != Timing::Late {
                    return Err(format!(
                        "x86 block b{at} has an invalid parameter constraint"
                    ));
                }
            }
            Self::verify_range(block.instructions, self.order.len(), "block instructions")?;
            for &param in &self.block_params[block.params.range()] {
                define(
                    &mut definitions,
                    param,
                    Definition {
                        owner: block.owner,
                        block: block_id,
                        position: None,
                        description: format!("block b{at}"),
                    },
                )?;
            }
            for (position, &instruction) in
                self.order[block.instructions.range()].iter().enumerate()
            {
                let Some(owners) = instruction_owners.get_mut(instruction.index()) else {
                    return Err(format!("x86 block b{at} refers to an unknown instruction"));
                };
                *owners = owners
                    .checked_add(1)
                    .ok_or_else(|| "x86 instruction has too many owners".to_owned())?;
                let inst = self.instructions[instruction];
                self.verify_inst(
                    inst,
                    &mut definitions,
                    instruction,
                    block.owner,
                    block_id,
                    position,
                )?;
            }
            self.verify_terminator(block.owner, block.terminator)?;
        }
        for (at, inst) in self.instructions.iter().enumerate() {
            if instruction_owners[at] != 1 {
                return Err(format!(
                    "x86 instruction i{at} belongs to {} blocks",
                    instruction_owners[at]
                ));
            }
            self.verify_inst_shape(*inst, InstId::at(at))?;
        }
        self.verify_stack_calls()?;
        let dominators = self.dominators()?;
        for (id, block) in self.blocks.iter_enumerated() {
            self.verify_uses(block.owner, block.terminator, &definitions, id, &dominators)?;
        }
        Ok(())
    }

    /// Verify each call's contiguous stores/call/loads sequence, and the
    /// entry loads and return stores against the owning function's layout.
    /// Slot bounds alone would admit missing, overlapping or unwritten values.
    #[expect(
        clippy::too_many_lines,
        reason = "one walk verifies both sides of each stack call"
    )]
    fn verify_stack_calls(&self) -> Result<(), String> {
        for (id, block) in self.blocks.iter_enumerated() {
            let owner = self
                .functions
                .iter()
                .find(|f| f.source == block.owner)
                .expect("a verified block owner");
            let (mut arguments, mut returns) = (0usize, 0usize);
            let mut results = 0..0;
            let incoming = if id == owner.entry {
                owner.stack_params
            } else {
                0
            };
            let instructions = &self.order[block.instructions.range()];
            if instructions.len() < incoming {
                return Err("x86 stack parameters are missing".to_owned());
            }
            for (at, &instruction) in instructions.iter().enumerate() {
                let inst = self.instructions[instruction];
                if at < incoming {
                    if inst.opcode != Opcode::LoadIncoming || inst.immediate != stack_slot(at)? {
                        return Err("x86 stack parameter has the wrong slot".to_owned());
                    }
                    continue;
                }
                if let Some(slot) = results.next() {
                    if inst.opcode != Opcode::LoadOutgoing || inst.immediate != stack_slot(slot)? {
                        return Err("x86 stack call result has the wrong slot".to_owned());
                    }
                    continue;
                }
                if arguments > 0 && !matches!(inst.opcode, Opcode::StoreOutgoing | Opcode::Call) {
                    return Err("x86 stack arguments are not followed by their call".to_owned());
                }
                if returns > 0 && inst.opcode != Opcode::StoreIncoming {
                    return Err("x86 stack results are not followed by their return".to_owned());
                }
                match (inst.opcode, inst.immediate) {
                    (Opcode::StoreOutgoing, slot) if slot == stack_slot(arguments)? => {
                        arguments += 1;
                    }
                    (Opcode::StoreIncoming, slot)
                        if slot == stack_slot(owner.stack_params + returns)? =>
                    {
                        returns += 1;
                    }
                    (Opcode::Call, Immediate::Function(function)) => {
                        let callee = self
                            .functions
                            .iter()
                            .find(|f| f.source == function)
                            .ok_or("x86 stack call has no callee")?;
                        if function == self.functions[0].source {
                            return Err("x86 cannot call the logical entry".to_owned());
                        }
                        if arguments != callee.stack_params {
                            return Err(
                                "x86 stack call has the wrong number of arguments".to_owned()
                            );
                        }
                        results = arguments..arguments + callee.stack_results;
                        arguments = 0;
                    }
                    (
                        Opcode::LoadIncoming
                        | Opcode::LoadOutgoing
                        | Opcode::StoreIncoming
                        | Opcode::StoreOutgoing,
                        _,
                    ) => {
                        return Err("x86 stack access is outside its call sequence".to_owned());
                    }
                    _ => {}
                }
            }
            let expected = if matches!(block.terminator, Terminator::Return { .. }) {
                owner.stack_results
            } else {
                0
            };
            if arguments != 0 || !results.is_empty() || returns != expected {
                return Err("x86 stack call or return is incomplete".to_owned());
            }
        }
        Ok(())
    }

    fn verify_range(range: Range, len: usize, what: &str) -> Result<(), String> {
        if range.range().end > len {
            return Err(format!("x86 {what} range is outside its pool"));
        }
        Ok(())
    }

    fn verify_inst(
        &self,
        inst: Inst,
        definitions: &mut [Option<Definition>],
        id: InstId,
        owner: FunctionId,
        block: BlockId,
        position: usize,
    ) -> Result<(), String> {
        Self::verify_range(inst.operands, self.operands.len(), "operand")?;
        if let Some(result) = inst.result {
            define(
                definitions,
                result,
                Definition {
                    owner,
                    block,
                    position: Some(position),
                    description: format!("instruction i{}", id.index()),
                },
            )?;
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "selected instruction shape, constraints, and effects are verified together"
    )]
    fn verify_inst_shape(&self, inst: Inst, id: InstId) -> Result<(), String> {
        let uses = self.operands[inst.operands.range()].len();
        let expected = match inst.opcode {
            Opcode::Constant
            | Opcode::DataAddress
            | Opcode::ArgumentCount
            | Opcode::ArgumentVector
            | Opcode::ReadByte
            | Opcode::LoadIncoming
            | Opcode::LoadOutgoing => 0,
            Opcode::Load
            | Opcode::Convert
            | Opcode::Shift
            | Opcode::Exit
            | Opcode::Grow
            | Opcode::CloseFd
            | Opcode::StoreIncoming
            | Opcode::StoreOutgoing => 1,
            Opcode::Float => match inst.immediate {
                Immediate::Float(float) => float.operation.arity(),
                _ => usize::MAX,
            },
            Opcode::Add
            | Opcode::Subtract
            | Opcode::And
            | Opcode::Or
            | Opcode::Xor
            | Opcode::ShiftUp
            | Opcode::ShiftDown
            | Opcode::Monus
            | Opcode::Multiply
            | Opcode::Divide
            | Opcode::Modulo
            | Opcode::Equal
            | Opcode::Below
            | Opcode::Store
            | Opcode::Write => 2,
            Opcode::WriteFd | Opcode::ReadFd => 3,
            Opcode::OpenAt => 4,
            Opcode::Call => uses,
        };
        if uses != expected {
            return Err(format!(
                "x86 instruction i{} has {uses} uses, expected {expected}",
                id.index()
            ));
        }
        let result_is_valid = match inst.opcode {
            Opcode::Store
            | Opcode::Write
            | Opcode::Exit
            | Opcode::StoreIncoming
            | Opcode::StoreOutgoing => inst.result.is_none(),
            Opcode::Call => true,
            _ => inst.result.is_some(),
        };
        if !result_is_valid {
            return Err(format!(
                "x86 instruction i{} has the wrong result arity",
                id.index()
            ));
        }
        verify_immediate(inst, id)?;
        self.verify_inst_widths(inst, id)?;
        verify_effects(inst.opcode, id)?;
        let operands = uses + usize::from(inst.result.is_some());
        for at in 0..operands {
            let spec = inst.operand_spec(at).ok_or_else(|| {
                format!(
                    "x86 instruction i{} has no constraint for operand {at}",
                    id.index()
                )
            })?;
            if let Constraint::Tied(other) = spec.constraint
                && usize::from(other) >= operands
            {
                return Err(format!(
                    "x86 instruction i{} has an invalid tie",
                    id.index()
                ));
            }
        }
        Ok(())
    }

    fn verify_inst_widths(&self, inst: Inst, id: InstId) -> Result<(), String> {
        let declared = match inst.immediate {
            Immediate::Bits(bits) | Immediate::Shift { bits, .. } => Some(bits),
            _ => None,
        };
        if matches!(inst.immediate, Immediate::Shift { bits: 0, .. })
            || declared.is_some_and(|bits| bits > WORD_BITS)
        {
            return Err(format!(
                "x86 instruction i{} has an unsupported width",
                id.index()
            ));
        }
        let represented = match inst.opcode {
            // A monus works at its operands' width, where the borrow is.
            Opcode::Equal | Opcode::Below | Opcode::Monus => self
                .operands
                .get(inst.operands.range().start)
                .map(|&value| self.width(value))
                .transpose()?,
            op if op.in_place()
                || matches!(op, Opcode::Multiply | Opcode::Divide | Opcode::Modulo) =>
            {
                inst.result.map(|value| self.width(value)).transpose()?
            }
            _ => None,
        };
        if let (Some(declared), Some(represented)) = (declared, represented)
            && declared != represented
        {
            return Err(format!(
                "x86 instruction i{} declares {declared} bits for a {represented}-bit value",
                id.index()
            ));
        }
        Ok(())
    }

    fn verify_terminator(&self, owner: FunctionId, terminator: Terminator) -> Result<(), String> {
        match terminator {
            Terminator::Jump { target, args } => self.verify_edge(owner, target, args),
            Terminator::Branch {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                self.verify_edge(owner, then_target, then_args)?;
                self.verify_edge(owner, else_target, else_args)
            }
            Terminator::Return { values } => {
                Self::verify_range(values, self.operands.len(), "return")?;
                if values.len() > 1 {
                    return Err("x86 return has more than one value".to_owned());
                }
                for at in 0..values.len() {
                    let spec = terminator
                        .return_operand_spec(at)
                        .ok_or_else(|| format!("x86 return value {at} has no ABI constraint"))?;
                    if spec.constraint != Constraint::Fixed(Reg::Rax) {
                        return Err(format!("x86 return value {at} is not in rax"));
                    }
                }
                Ok(())
            }
            Terminator::Halt => Ok(()),
        }
    }

    fn verify_edge(&self, owner: FunctionId, target: BlockId, args: Range) -> Result<(), String> {
        Self::verify_range(args, self.operands.len(), "edge argument")?;
        let target = self
            .blocks
            .get(target)
            .ok_or_else(|| "x86 edge refers to an unknown block".to_owned())?;
        if target.owner != owner {
            return Err("x86 edge crosses a function boundary".to_owned());
        }
        if args.len() != target.params.len() {
            return Err(format!(
                "x86 edge supplies {} values to {} parameters",
                args.len(),
                target.params.len()
            ));
        }
        for (&argument, &parameter) in self.operands[args.range()]
            .iter()
            .zip(&self.block_params[target.params.range()])
        {
            if self.width(argument)? > self.width(parameter)? {
                return Err("x86 edge argument does not fit its parameter".to_owned());
            }
        }
        Ok(())
    }

    fn dominators(&self) -> Result<Dominators, String> {
        let predecessors = self.predecessors();
        let mut immediate = vec![None; self.blocks.len()];
        for function in &self.functions {
            let (rpo, roots) = self.reverse_postorder(*function);
            let mut order = vec![None; self.blocks.len()];
            for (at, &block) in rpo.iter().enumerate() {
                order[block.index()] = Some(at);
            }
            for &root in &roots {
                immediate[root.index()] = Some(root);
            }
            loop {
                let mut changed = false;
                for &block in &rpo {
                    if roots.contains(&block) {
                        continue;
                    }
                    let mut incoming = predecessors[block.index()]
                        .iter()
                        .copied()
                        .filter(|predecessor| immediate[predecessor.index()].is_some());
                    let first = incoming.next().ok_or_else(|| {
                        format!("x86 block b{} has no reachable predecessor", block.index())
                    })?;
                    let dominator = incoming.fold(first, |held, predecessor| {
                        intersect_dominators(held, predecessor, &immediate, &order)
                    });
                    if immediate[block.index()] != Some(dominator) {
                        immediate[block.index()] = Some(dominator);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
        }
        Ok(Dominators { immediate })
    }

    fn predecessors(&self) -> Vec<Vec<BlockId>> {
        let mut predecessors = vec![Vec::new(); self.blocks.len()];
        for (id, block) in self.blocks.iter_enumerated() {
            for target in successors(block.terminator).into_iter().flatten() {
                predecessors[target.index()].push(id);
            }
        }
        predecessors
    }

    fn reverse_postorder(&self, function: Function) -> (Vec<BlockId>, Vec<BlockId>) {
        let mut seen = vec![false; self.blocks.len()];
        let mut roots = Vec::new();
        let mut rpo = Vec::new();
        let candidates = std::iter::once(function.entry).chain(
            self.blocks
                .iter_enumerated()
                .filter(|(_, block)| block.owner == function.source)
                .map(|(id, _)| id),
        );
        for root in candidates {
            if seen[root.index()] {
                continue;
            }
            roots.push(root);
            let mut stack = vec![(root, false)];
            let mut postorder = Vec::new();
            while let Some((block, expanded)) = stack.pop() {
                if expanded {
                    postorder.push(block);
                    continue;
                }
                if seen[block.index()] {
                    continue;
                }
                seen[block.index()] = true;
                stack.push((block, true));
                for successor in successors(self.blocks[block].terminator)
                    .into_iter()
                    .flatten()
                {
                    if !seen[successor.index()] {
                        stack.push((successor, false));
                    }
                }
            }
            postorder.reverse();
            rpo.extend(postorder);
        }
        (rpo, roots)
    }

    fn width(&self, value: VReg) -> Result<u16, String> {
        self.widths
            .get(value.index())
            .copied()
            .ok_or_else(|| format!("x86 refers to unknown v{}", value.index()))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "all instruction and terminator use forms are checked in one walk"
    )]
    fn verify_uses(
        &self,
        owner: FunctionId,
        terminator: Terminator,
        definitions: &[Option<Definition>],
        block: BlockId,
        dominators: &Dominators,
    ) -> Result<(), String> {
        let check = |value: VReg, position: usize| {
            let definition = definitions
                .get(value.index())
                .and_then(Option::as_ref)
                .ok_or_else(|| {
                    format!(
                        "x86 block b{} uses undefined v{}",
                        block.index(),
                        value.index()
                    )
                })?;
            if definition.owner != owner {
                return Err(format!(
                    "x86 block b{} uses v{} from another function",
                    block.index(),
                    value.index()
                ));
            }
            let dominates = if definition.block == block {
                definition.position.is_none_or(|defined| defined < position)
            } else {
                dominators.contains(definition.block, block)
            };
            if !dominates {
                return Err(format!(
                    "x86 {} does not dominate the use of v{} in b{}",
                    definition.description,
                    value.index(),
                    block.index()
                ));
            }
            Ok(())
        };
        for (position, inst) in self.blocks[block].instructions.range().enumerate() {
            let id = self.order[inst];
            for &value in &self.operands[self.instructions[id].operands.range()] {
                check(value, position)?;
            }
        }
        let after_instructions = self.blocks[block].instructions.len();
        match terminator {
            Terminator::Jump { args, .. } => {
                for &value in &self.operands[args.range()] {
                    check(value, after_instructions)?;
                }
            }
            Terminator::Branch {
                condition,
                then_args,
                else_args,
                ..
            } => {
                check(condition, after_instructions)?;
                for &value in self.operands[then_args.range()]
                    .iter()
                    .chain(&self.operands[else_args.range()])
                {
                    check(value, after_instructions)?;
                }
            }
            Terminator::Return { values } => {
                for &value in &self.operands[values.range()] {
                    check(value, after_instructions)?;
                }
            }
            Terminator::Halt => {}
        }
        Ok(())
    }
}

fn intersect_dominators(
    mut left: BlockId,
    mut right: BlockId,
    immediate: &[Option<BlockId>],
    order: &[Option<usize>],
) -> BlockId {
    while left != right {
        while order[left.index()] > order[right.index()] {
            left = immediate[left.index()].expect("a processed dominator");
        }
        while order[right.index()] > order[left.index()] {
            right = immediate[right.index()].expect("a processed dominator");
        }
    }
    left
}

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

fn define(
    definitions: &mut [Option<Definition>],
    value: VReg,
    definition: Definition,
) -> Result<(), String> {
    let Some(held) = definitions.get_mut(value.index()) else {
        return Err(format!("x86 defines unknown v{}", value.index()));
    };
    if let Some(first) = held {
        return Err(format!(
            "x86 v{} is defined by {} and {}",
            value.index(),
            first.description,
            definition.description
        ));
    }
    *held = Some(definition);
    Ok(())
}

#[expect(
    clippy::too_many_lines,
    reason = "one exhaustive arm per opcode, so a new one cannot go unchecked"
)]
fn verify_effects(opcode: Opcode, id: InstId) -> Result<(), String> {
    let requirements = opcode.requirements();
    let effects = requirements.effects;
    let scratch_is_clobbered = requirements.scratch.0 & !effects.clobbers.0 == 0;
    let valid = scratch_is_clobbered
        && match opcode {
            Opcode::Constant => {
                requirements.expansion == Expansion::Sequence && effects.memory == Access::ReadWrite
            }
            Opcode::Load | Opcode::LoadIncoming | Opcode::LoadOutgoing => {
                effects.memory == Access::Read
            }
            Opcode::Store | Opcode::StoreIncoming | Opcode::StoreOutgoing => {
                effects.memory == Access::Write
            }
            Opcode::Call
            | Opcode::Write
            | Opcode::WriteFd
            | Opcode::ReadFd
            | Opcode::OpenAt
            | Opcode::CloseFd
            | Opcode::Exit
            | Opcode::Grow
            | Opcode::ReadByte => {
                effects.control
                    && effects.memory == Access::Unknown
                    && effects.clobbers.contains(Reg::Rax)
                    && effects.clobbers.contains(Reg::R11)
            }
            Opcode::Add
            | Opcode::Subtract
            | Opcode::And
            | Opcode::Or
            | Opcode::Xor
            | Opcode::ShiftUp
            | Opcode::ShiftDown
            | Opcode::Monus
            | Opcode::Multiply
            | Opcode::Divide
            | Opcode::Modulo
            | Opcode::Shift
            | Opcode::ArgumentVector => effects.flags == Access::Write,
            Opcode::DataAddress
            | Opcode::Equal
            | Opcode::Below
            | Opcode::Convert
            | Opcode::ArgumentCount
            | Opcode::Float => effects == Effects::PURE,
        };
    if valid {
        Ok(())
    } else {
        Err(format!(
            "x86 instruction i{} has an inconsistent effect declaration",
            id.index()
        ))
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one accepted immediate per opcode, in the order they are declared"
)]
fn verify_immediate(inst: Inst, id: InstId) -> Result<(), String> {
    let valid = matches!(
        (inst.opcode, inst.immediate),
        (Opcode::Constant, Immediate::Integer(_))
            | (Opcode::DataAddress, Immediate::Data(_))
            | (
                Opcode::Add
                    | Opcode::Subtract
                    | Opcode::And
                    | Opcode::Or
                    | Opcode::Xor
                    | Opcode::ShiftUp
                    | Opcode::ShiftDown
                    | Opcode::Monus
                    | Opcode::Multiply
                    | Opcode::Divide
                    | Opcode::Modulo
                    | Opcode::Equal
                    | Opcode::Below
                    | Opcode::Convert,
                Immediate::Bits(_)
            )
            | (Opcode::Load | Opcode::Store, Immediate::Memory { .. })
            | (Opcode::Shift, Immediate::Shift { .. })
            | (Opcode::Call, Immediate::Function(_))
            | (Opcode::Float, Immediate::Float(_))
            | (
                Opcode::LoadIncoming
                    | Opcode::LoadOutgoing
                    | Opcode::StoreIncoming
                    | Opcode::StoreOutgoing,
                Immediate::Slot(_)
            )
            | (
                Opcode::Write
                    | Opcode::WriteFd
                    | Opcode::ReadFd
                    | Opcode::OpenAt
                    | Opcode::CloseFd
                    | Opcode::Exit
                    | Opcode::Grow
                    | Opcode::ArgumentCount
                    | Opcode::ArgumentVector
                    | Opcode::ReadByte
                    // A conversion that takes nothing off.
                    | Opcode::Convert,
                Immediate::None
            )
    );
    if valid {
        Ok(())
    } else {
        Err(format!(
            "x86 instruction i{} has an immediate for another opcode",
            id.index()
        ))
    }
}

#[derive(Debug)]
struct BlockDraft {
    owner: FunctionId,
    params: Vec<VReg>,
    param_specs: Vec<OperandSpec>,
    instructions: Vec<InstId>,
    terminator: Option<Terminator>,
}

#[derive(Clone, Copy)]
struct Flow {
    join: Option<BlockId>,
    repeat: Option<BlockId>,
    leave: Option<BlockId>,
}

struct Selector<'a> {
    source: &'a Program,
    widths: Vec<u16>,
    /// Conversions an enclosing comparison has already bounded.
    whole: Vec<bool>,
    operands: Vec<VReg>,
    instructions: Pool<InstId, Inst>,
    blocks: Pool<BlockId, BlockDraft>,
    functions: Vec<Function>,
}

#[cfg(test)]
pub(crate) fn select_and_allocate(source: &Program) -> Result<crate::machine::Allocated, String> {
    select_and_allocate_favouring(source, faun_core::targets::Favour::Speed)
}

/// [`select_and_allocate`], favouring speed or size where they pull apart.
pub(crate) fn select_and_allocate_favouring(
    source: &Program,
    favour: faun_core::targets::Favour,
) -> Result<crate::machine::Allocated, String> {
    let selected = select(source)?;
    register_allocate::allocate(&selected, source.entry(), favour)
}

#[expect(
    clippy::too_many_lines,
    reason = "selection initializes value classes and each function entry"
)]
pub(crate) fn select(source: &Program) -> Result<Selected, String> {
    let mut widths = Vec::with_capacity(source.values_count());
    for at in 0..source.values_count() {
        let class = source.class(ValueId::at(at));
        if class == Class::Natural {
            return Err("x86 selection received an arbitrary-precision value".to_owned());
        }
        widths.push(class.bits(WORD_BITS));
    }
    let mut selector = Selector {
        source,
        widths,
        whole: faun_core::ir::conversions_taking_nothing(source),
        operands: Vec::new(),
        instructions: Pool::default(),
        blocks: Pool::default(),
        functions: Vec::new(),
    };
    let entry = source.entry();
    let rest = (0..source.functions().len())
        .map(FunctionId::at)
        .filter(|&id| id != entry);
    for source_id in std::iter::once(entry).chain(rest) {
        let function = source.function(source_id);
        let Some(body) = function.body() else {
            continue;
        };
        let params = source.values(source.region(body).params);
        let entry = selector.function_entry(source_id, source_id == entry, params)?;
        selector.functions.push(Function {
            source: source_id,
            entry,
            stack_params: params.len().saturating_sub(ARG_COUNT),
            stack_results: function.returns.classes().len().saturating_sub(1),
        });
        selector.region(
            source_id,
            body,
            entry,
            Flow {
                join: None,
                repeat: None,
                leave: None,
            },
        )?;
    }
    selector.finish()
}

impl Selector<'_> {
    fn function_entry(
        &mut self,
        owner: FunctionId,
        program_entry: bool,
        params: &[ValueId],
    ) -> Result<BlockId, String> {
        if program_entry {
            let block = self.block(owner, &[]);
            // The count, then where the arguments' addresses lie.
            for (&value, opcode) in params
                .iter()
                .zip([Opcode::ArgumentCount, Opcode::ArgumentVector])
            {
                self.emit(block, opcode, Some(value), &[], Immediate::None);
            }
            return Ok(block);
        }
        let registers = params.len().min(ARG_COUNT);
        let block = self.block(owner, &params[..registers]);
        for (at, spec) in self.blocks[block].param_specs.iter_mut().enumerate() {
            spec.constraint =
                Constraint::Fixed(abi_register(at).ok_or_else(|| {
                    "x86 function has more than six selected parameters".to_owned()
                })?);
        }
        for (slot, &value) in params[registers..].iter().enumerate() {
            self.emit(
                block,
                Opcode::LoadIncoming,
                Some(value),
                &[],
                stack_slot(slot)?,
            );
        }
        Ok(block)
    }

    fn finish(self) -> Result<Selected, String> {
        let mut order = Vec::new();
        let mut block_params = Vec::new();
        let mut block_param_specs = Vec::new();
        let mut blocks = Pool::default();
        for (at, block) in self.blocks.into_iter().enumerate() {
            let params = append(&mut block_params, &block.params);
            let specs = append(&mut block_param_specs, &block.param_specs);
            assert_eq!(
                params, specs,
                "block parameter values and specs stay parallel"
            );
            let instructions = append(&mut order, &block.instructions);
            let terminator = block
                .terminator
                .ok_or_else(|| format!("x86 block b{at} has no terminator"))?;
            blocks.push(Block {
                owner: block.owner,
                params,
                instructions,
                terminator,
            });
        }
        let selected = Selected {
            widths: self.widths,
            operands: self.operands,
            instructions: self.instructions,
            order,
            block_params,
            block_param_specs,
            blocks,
            functions: self.functions,
        };
        selected.verify()?;
        Ok(selected)
    }

    fn block(&mut self, owner: FunctionId, params: &[ValueId]) -> BlockId {
        self.blocks.push(BlockDraft {
            owner,
            params: params.iter().copied().map(vreg).collect(),
            param_specs: vec![
                OperandSpec {
                    role: Role::Def,
                    timing: Timing::Late,
                    constraint: Constraint::Any,
                    allowed: SCALARS,
                };
                params.len()
            ],
            instructions: Vec::new(),
            terminator: None,
        })
    }

    fn result_block(&mut self, owner: FunctionId, results: &[ValueId]) -> BlockId {
        self.block(owner, results)
    }

    fn emit(
        &mut self,
        block: BlockId,
        opcode: Opcode,
        result: Option<ValueId>,
        operands: &[ValueId],
        immediate: Immediate,
    ) {
        let operands: Vec<_> = operands.iter().copied().map(vreg).collect();
        let operands = append(&mut self.operands, &operands);
        let id = self.instructions.push(Inst {
            opcode,
            result: result.map(vreg),
            operands,
            immediate,
        });
        self.blocks[block].instructions.push(id);
    }

    fn terminate(&mut self, block: BlockId, terminator: Terminator) {
        let held = &mut self.blocks[block].terminator;
        assert!(held.is_none(), "an x86 block is terminated once");
        *held = Some(terminator);
    }

    fn edge_args(&mut self, values: &[ValueId]) -> Range {
        let values: Vec<_> = values.iter().copied().map(vreg).collect();
        append(&mut self.operands, &values)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one selection arm per machine-IR operation"
    )]
    fn region(
        &mut self,
        owner: FunctionId,
        region: RegionId,
        mut block: BlockId,
        flow: Flow,
    ) -> Result<(), String> {
        let source = self.source;
        for (op, results) in source.walk(region) {
            match *op {
                SourceOp::NaturalConstant(_) => {
                    return Err("x86 selection received an arbitrary-precision constant".to_owned());
                }
                SourceOp::Cell { .. }
                | SourceOp::CellTag { .. }
                | SourceOp::CellField { .. }
                | SourceOp::BufferEmpty { .. }
                | SourceOp::BufferKnown { .. }
                | SourceOp::BufferPush { .. }
                | SourceOp::BufferAppend { .. }
                | SourceOp::BufferReplace { .. }
                | SourceOp::BufferPrepend { .. }
                | SourceOp::BufferExtend { .. }
                | SourceOp::BufferRoom { .. }
                | SourceOp::BufferAt { .. }
                | SourceOp::Keep { .. }
                | SourceOp::BufferField { .. } => {
                    return Err("x86 selection received an abstract cell operation".to_owned());
                }
                SourceOp::Constant { value } => self.emit(
                    block,
                    Opcode::Constant,
                    results.first().copied(),
                    &[],
                    Immediate::Integer(value),
                ),
                SourceOp::AddressOf(data) => self.emit(
                    block,
                    Opcode::DataAddress,
                    results.first().copied(),
                    &[],
                    Immediate::Data(data),
                ),
                SourceOp::Binary { op, left, right } => {
                    // A monus of what can be no less than what it takes
                    // away never borrows, so it is the difference.
                    let borrows = || {
                        let least = source.class(left).facts().map_or(0, |facts| facts.low);
                        source
                            .class(right)
                            .facts()
                            .and_then(|facts| facts.high)
                            .is_none_or(|most| most > least)
                    };
                    let opcode = match op {
                        Binary::Add => Opcode::Add,
                        Binary::Sub => Opcode::Subtract,
                        Binary::Monus if !borrows() => Opcode::Subtract,
                        Binary::Monus => Opcode::Monus,
                        Binary::Mul => Opcode::Multiply,
                        Binary::Div => Opcode::Divide,
                        Binary::Mod => Opcode::Modulo,
                        Binary::And => Opcode::And,
                        Binary::Or => Opcode::Or,
                        Binary::Xor => Opcode::Xor,
                        Binary::ShiftUp => Opcode::ShiftUp,
                        Binary::ShiftDown => Opcode::ShiftDown,
                    };
                    // A monus answers no more than its left operand, and is
                    // worked out as wide as that is.
                    let width = if opcode == Opcode::Monus {
                        left
                    } else {
                        results[0]
                    };
                    self.emit(
                        block,
                        opcode,
                        results.first().copied(),
                        &[left, right],
                        Immediate::Bits(source.class(width).bits(WORD_BITS)),
                    );
                }
                SourceOp::Compare {
                    relation,
                    left,
                    right,
                } => {
                    let opcode = match relation {
                        Relation::Equal => Opcode::Equal,
                        Relation::Less => Opcode::Below,
                    };
                    self.emit(
                        block,
                        opcode,
                        results.first().copied(),
                        &[left, right],
                        Immediate::Bits(source.class(left).bits(WORD_BITS)),
                    );
                }
                SourceOp::Load {
                    width,
                    address,
                    offset,
                } => self.emit(
                    block,
                    Opcode::Load,
                    results.first().copied(),
                    &[address],
                    Immediate::Memory { width, offset },
                ),
                SourceOp::Store {
                    width,
                    address,
                    offset,
                    value,
                } => self.emit(
                    block,
                    Opcode::Store,
                    None,
                    &[address, value],
                    Immediate::Memory { width, offset },
                ),
                SourceOp::Convert { value } => {
                    // A value an enclosing comparison has already put below
                    // what the conversion keeps loses nothing to it, so the
                    // conversion says no width to take it to.
                    let kept = if self.whole[results[0].index()] {
                        Immediate::None
                    } else {
                        Immediate::Bits(source.class(results[0]).bits(WORD_BITS))
                    };
                    self.emit(
                        block,
                        Opcode::Convert,
                        results.first().copied(),
                        &[value],
                        kept,
                    );
                }
                SourceOp::Shift {
                    direction,
                    value,
                    by,
                } => self.emit(
                    block,
                    Opcode::Shift,
                    results.first().copied(),
                    &[value],
                    Immediate::Shift {
                        up: matches!(direction, faun_core::ir::Direction::Up),
                        by: u8::try_from(by).map_err(|_| "x86 shift distance exceeds 255")?,
                        bits: source.class(results[0]).bits(WORD_BITS),
                    },
                ),
                SourceOp::Float { float, operands } => {
                    let operands = source.values(operands).to_vec();
                    self.emit(
                        block,
                        Opcode::Float,
                        results.first().copied(),
                        &operands,
                        Immediate::Float(float),
                    );
                }
                SourceOp::Call { function, args } => {
                    let callee = source.function(function);
                    let opcode = if let Some(symbol) = callee.external() {
                        match source.name(symbol) {
                            "write!" => Opcode::Write,
                            "write_fd!" => Opcode::WriteFd,
                            "read_fd!" => Opcode::ReadFd,
                            "open_at!" => Opcode::OpenAt,
                            "fd_close!" => Opcode::CloseFd,
                            "exit!" => Opcode::Exit,
                            "grow" => Opcode::Grow,
                            "read_byte!" => Opcode::ReadByte,
                            other => return Err(format!("x86 has no selected call for `{other}`")),
                        }
                    } else {
                        Opcode::Call
                    };
                    let args = source.values(args);
                    if opcode == Opcode::Call {
                        let registers = args.len().min(ARG_COUNT);
                        for (slot, &value) in args[registers..].iter().enumerate() {
                            self.emit(
                                block,
                                Opcode::StoreOutgoing,
                                None,
                                &[value],
                                stack_slot(slot)?,
                            );
                        }
                        self.emit(
                            block,
                            opcode,
                            results.first().copied(),
                            &args[..registers],
                            Immediate::Function(function),
                        );
                        for (at, &value) in results.iter().skip(1).enumerate() {
                            let slot = args.len() - registers + at;
                            self.emit(
                                block,
                                Opcode::LoadOutgoing,
                                Some(value),
                                &[],
                                stack_slot(slot)?,
                            );
                        }
                    } else {
                        self.emit(
                            block,
                            opcode,
                            results.first().copied(),
                            args,
                            Immediate::None,
                        );
                    }
                }
                SourceOp::If {
                    condition,
                    then_region,
                    else_region,
                } => {
                    let then_params = source.values(source.region(then_region).params);
                    let else_params = source.values(source.region(else_region).params);
                    if !then_params.is_empty() || !else_params.is_empty() {
                        return Err("x86 if-arm parameters have no incoming values".to_owned());
                    }
                    let then_target = self.block(owner, then_params);
                    let else_target = self.block(owner, else_params);
                    let join = self.result_block(owner, results);
                    self.terminate(
                        block,
                        Terminator::Branch {
                            condition: vreg(condition),
                            then_target,
                            then_args: Range::EMPTY,
                            else_target,
                            else_args: Range::EMPTY,
                        },
                    );
                    self.region(
                        owner,
                        then_region,
                        then_target,
                        Flow {
                            join: Some(join),
                            ..flow
                        },
                    )?;
                    self.region(
                        owner,
                        else_region,
                        else_target,
                        Flow {
                            join: Some(join),
                            ..flow
                        },
                    )?;
                    block = join;
                }
                SourceOp::Loop { initial, body } => {
                    let head = self.block(owner, source.values(source.region(body).params));
                    let exit = self.result_block(owner, results);
                    let args = self.edge_args(source.values(initial));
                    self.terminate(block, Terminator::Jump { target: head, args });
                    self.region(
                        owner,
                        body,
                        head,
                        Flow {
                            join: None,
                            repeat: Some(head),
                            leave: Some(exit),
                        },
                    )?;
                    block = exit;
                }
            }
        }
        if let Some(terminator) = source.region(region).terminator {
            self.source_terminator(block, terminator, flow)
        } else {
            self.terminate(block, Terminator::Halt);
            Ok(())
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one exhaustive selection of region transfers and stack results"
    )]
    fn source_terminator(
        &mut self,
        block: BlockId,
        terminator: SourceTerminator,
        flow: Flow,
    ) -> Result<(), String> {
        let values = self.source.values(terminator.values);
        match terminator.exit {
            Exit::Yield => {
                let target = flow
                    .join
                    .ok_or_else(|| "x86 yield has no selected join".to_owned())?;
                let args = self.edge_args(values);
                self.terminate(block, Terminator::Jump { target, args });
            }
            Exit::Continue => {
                let target = flow
                    .repeat
                    .ok_or_else(|| "x86 continue has no selected loop".to_owned())?;
                let args = self.edge_args(values);
                self.terminate(block, Terminator::Jump { target, args });
            }
            Exit::Break => {
                let target = flow
                    .leave
                    .ok_or_else(|| "x86 break has no selected loop".to_owned())?;
                let args = self.edge_args(values);
                self.terminate(block, Terminator::Jump { target, args });
            }
            Exit::Return => {
                let owner = self.blocks[block].owner;
                let arguments = self
                    .source
                    .function(owner)
                    .params
                    .len()
                    .saturating_sub(ARG_COUNT);
                for (at, &value) in values.iter().skip(1).enumerate() {
                    self.emit(
                        block,
                        Opcode::StoreIncoming,
                        None,
                        &[value],
                        stack_slot(arguments + at)?,
                    );
                }
                let values = self.edge_args(&values[..values.len().min(1)]);
                self.terminate(block, Terminator::Return { values });
            }
        }
        Ok(())
    }
}

/// Keep call areas within a signed x86 stack displacement. Frame layout
/// checks the combined outgoing area, spills and saved registers later.
fn stack_slot(slot: usize) -> Result<Immediate, String> {
    let slot = u32::try_from(slot).map_err(|_| "x86 call area is too large")?;
    if slot >= i32::MAX.cast_unsigned() / 8 {
        return Err("x86 call area is too large".to_owned());
    }
    Ok(Immediate::Slot(slot))
}

fn append<T: Clone>(pool: &mut Vec<T>, values: &[T]) -> Range {
    let range = Range::of(pool.len(), values.len());
    pool.extend_from_slice(values);
    range
}

#[cfg(test)]
mod tests {
    use super::*;
    use faun_core::ir::validate;

    #[test]
    fn selected_allocation_lowers_to_an_encodable_symbolic_sequence() {
        let program = faun_core::programs::carries_a_total_into_an_arm(3);
        let allocated = select_and_allocate(&program).unwrap();
        let code = crate::encode::encode(&allocated);
        assert!(!code.bytes.is_empty());
    }

    #[test]
    fn call_splits_store_before_the_call_and_reload_after_it() {
        let (mut program, main) = Program::new("main");
        let helper = program.declare("helper", &[], &[Class::Word]);
        program.define(helper, |builder, _| {
            let answer = builder.constant(Class::Word, 3);
            builder.ret(&[answer]);
        });
        // More values live across the call than a call leaves registers
        // for, so some wait in memory.
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let across: Vec<_> = (0..8)
                .map(|at| {
                    let other = builder.constant(Class::Word, at);
                    builder.binary(Binary::Add, one, other)
                })
                .collect();
            let mut sum = builder.call_one(helper, &[]);
            for value in across {
                sum = builder.binary(Binary::Add, sum, value);
            }
            builder.ret(&[sum]);
        });

        let allocated = select_and_allocate(&program).unwrap();
        let instructions = allocated.instructions();
        let call = instructions
            .iter()
            .position(|inst| matches!(inst, crate::machine::Inst::Call { .. }))
            .unwrap();
        assert!(
            instructions[..call]
                .iter()
                .any(|inst| matches!(inst, crate::machine::Inst::StoreFrame { .. }))
        );
        assert!(
            instructions[call + 1..]
                .iter()
                .any(|inst| matches!(inst, crate::machine::Inst::LoadFrame { .. }))
        );
    }

    #[test]
    fn structured_regions_become_blocks_with_parallel_edge_arguments() {
        let program = faun_core::programs::carries_a_total_into_an_arm(3);
        validate(&program).unwrap();
        let selected = select(&program).unwrap();
        assert!(selected.blocks.len() > program.functions().len());
        assert!(selected.blocks.iter().any(|block| {
            matches!(block.terminator, Terminator::Jump { args, .. } if !args.is_empty())
        }));
    }

    #[test]
    fn function_boundaries_name_the_system_v_registers() {
        let program = faun_core::programs::abi::function(2, 1);
        let selected = select(&program).unwrap();
        let function = selected
            .functions
            .iter()
            .find(|function| selected.blocks[function.entry].params.len() == 2)
            .unwrap();
        let entry = selected.blocks[function.entry];
        let specs = &selected.block_param_specs[entry.params.range()];
        assert_eq!(specs[0].constraint, Constraint::Fixed(Reg::Rdi));
        assert_eq!(specs[1].constraint, Constraint::Fixed(Reg::Rsi));
        let returned = selected.blocks.iter().find_map(|block| {
            (block.owner == function.source)
                .then_some(block.terminator)
                .and_then(|terminator| terminator.return_operand_spec(0))
        });
        assert_eq!(returned.unwrap().constraint, Constraint::Fixed(Reg::Rax));
    }

    #[test]
    fn verifier_rejects_a_use_not_dominated_by_its_definition() {
        let program = faun_core::programs::carries_a_total_into_an_arm(3);
        let mut selected = select(&program).unwrap();
        let inst = selected
            .instructions
            .iter()
            .copied()
            .find(|inst| inst.result.is_some() && !inst.operands.is_empty())
            .unwrap();
        selected.operands[inst.operands.range().start] = inst.result.unwrap();
        assert!(selected.verify().unwrap_err().contains("does not dominate"));
    }

    #[test]
    fn call_constraints_name_the_system_v_argument_registers() {
        let inst = Inst {
            opcode: Opcode::Call,
            result: Some(VReg::at(2)),
            operands: Range::of(0, 2),
            immediate: Immediate::Function(FunctionId::at(0)),
        };
        assert_eq!(
            inst.operand_spec(0).unwrap().constraint,
            Constraint::Fixed(Reg::Rax)
        );
        assert_eq!(
            inst.operand_spec(1).unwrap().constraint,
            Constraint::Fixed(Reg::Rdi)
        );
        assert_eq!(
            inst.operand_spec(2).unwrap().constraint,
            Constraint::Fixed(Reg::Rsi)
        );
    }

    #[test]
    fn calls_declare_hidden_clobbers_and_memory_effects() {
        let requirements = Opcode::Call.requirements();
        assert_eq!(requirements.expansion, Expansion::Single);
        assert_eq!(requirements.effects.memory, Access::Unknown);
        assert!(requirements.effects.control);
        assert!(requirements.effects.clobbers.contains(Reg::R11));

        let write = Opcode::Write.requirements();
        assert!(write.effects.clobbers.contains(Reg::Rcx));
        assert!(write.effects.clobbers.contains(Reg::R11));
        assert!(!write.effects.clobbers.contains(Reg::Rsi));
        assert!(!write.effects.clobbers.contains(Reg::Rdx));
    }

    #[test]
    fn division_declares_its_expansion_and_scratch_register() {
        let requirements = Opcode::Divide.requirements();
        assert_eq!(requirements.expansion, Expansion::Sequence);
        assert!(requirements.scratch.contains(Reg::Rdx));
        assert!(requirements.effects.clobbers.contains(Reg::Rdx));
    }

    #[test]
    fn verifier_rejects_wrong_stack_slots_on_both_sides_of_a_call() {
        for opcode in [
            Opcode::LoadIncoming,
            Opcode::StoreIncoming,
            Opcode::LoadOutgoing,
            Opcode::StoreOutgoing,
        ] {
            let mut selected = select(&faun_core::programs::abi::function(8, 3)).unwrap();
            let inst = selected
                .instructions
                .iter_mut()
                .find(|inst| inst.opcode == opcode)
                .unwrap();
            inst.immediate = Immediate::Slot(99);
            let error = selected.verify().unwrap_err();
            assert!(error.contains("stack"), "{opcode:?}: {error}");
        }
    }

    #[test]
    fn verifier_rejects_incomplete_stack_call_sequences() {
        for results in [false, true] {
            let mut selected = select(&faun_core::programs::abi::function(8, 3)).unwrap();
            let function = &mut selected.functions[1];
            if results {
                function.stack_results += 1;
            } else {
                function.stack_params += 1;
            }
            assert!(selected.verify().unwrap_err().contains("stack"));
        }
    }

    #[test]
    fn verifier_rejects_calls_to_the_logical_entry() {
        let mut selected = select(&faun_core::programs::abi::function(0, 1)).unwrap();
        let entry = selected.functions[0].source;
        let call = selected
            .instructions
            .iter_mut()
            .find(|inst| inst.opcode == Opcode::Call)
            .unwrap();
        call.immediate = Immediate::Function(entry);
        assert!(selected.verify().unwrap_err().contains("logical entry"));
    }

    #[test]
    fn multiplication_needs_no_fixed_registers_or_high_half_scratch() {
        let inst = Inst {
            opcode: Opcode::Multiply,
            result: Some(VReg::at(2)),
            operands: Range::of(0, 2),
            immediate: Immediate::Bits(64),
        };
        assert_eq!(inst.operand_spec(0).unwrap().constraint, Constraint::Any);
        assert_eq!(
            inst.operand_spec(1).unwrap().constraint,
            Constraint::Tied(0)
        );
        assert_eq!(inst.operand_spec(2).unwrap().constraint, Constraint::Any);
        let requirements = inst.opcode.requirements();
        assert_eq!(requirements.scratch, RegSet::default());
        assert_eq!(requirements.effects.clobbers, RegSet::default());
    }
}
