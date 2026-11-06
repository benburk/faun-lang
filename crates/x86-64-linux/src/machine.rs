//! The allocated x86-64 instruction sequence between lowering and encoding.
//!
//! It is deliberately local to this target. Instructions name allocated
//! physical registers, while labels, frame slots, and data references remain
//! symbolic until encoding.

use faun_core::ir::{DataId, FunctionId};
use faun_core::targets::code::Code;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    /// Reserved for the process argument count.
    Rbx = 3,
    /// Named for target adapters that use temporary stack storage.
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
    Xmm0 = 16,
    Xmm1 = 17,
    Xmm2 = 18,
    Xmm3 = 19,
    Xmm4 = 20,
    Xmm5 = 21,
    Xmm6 = 22,
    Xmm7 = 23,
    Xmm8 = 24,
    Xmm9 = 25,
    Xmm10 = 26,
    Xmm11 = 27,
    Xmm12 = 28,
    Xmm13 = 29,
    Xmm14 = 30,
    Xmm15 = 31,
}

impl From<Reg> for u8 {
    #[expect(clippy::as_conversions, reason = "reading a repr(u8) discriminant")]
    fn from(reg: Reg) -> Self {
        reg as Self
    }
}

impl Reg {
    pub(crate) fn index(self) -> usize {
        usize::from(u8::from(self))
    }

    pub(crate) const fn from_index(index: usize) -> Option<Self> {
        match index {
            0 => Some(Self::Rax),
            1 => Some(Self::Rcx),
            2 => Some(Self::Rdx),
            3 => Some(Self::Rbx),
            4 => Some(Self::Rsp),
            5 => Some(Self::Rbp),
            6 => Some(Self::Rsi),
            7 => Some(Self::Rdi),
            8 => Some(Self::R8),
            9 => Some(Self::R9),
            10 => Some(Self::R10),
            11 => Some(Self::R11),
            12 => Some(Self::R12),
            13 => Some(Self::R13),
            14 => Some(Self::R14),
            15 => Some(Self::R15),
            16 => Some(Self::Xmm0),
            17 => Some(Self::Xmm1),
            18 => Some(Self::Xmm2),
            19 => Some(Self::Xmm3),
            20 => Some(Self::Xmm4),
            21 => Some(Self::Xmm5),
            22 => Some(Self::Xmm6),
            23 => Some(Self::Xmm7),
            24 => Some(Self::Xmm8),
            25 => Some(Self::Xmm9),
            26 => Some(Self::Xmm10),
            27 => Some(Self::Xmm11),
            28 => Some(Self::Xmm12),
            29 => Some(Self::Xmm13),
            30 => Some(Self::Xmm14),
            31 => Some(Self::Xmm15),
            _ => None,
        }
    }

    pub(crate) fn is_xmm(self) -> bool {
        u8::from(self) >= 16
    }

    pub(super) fn low(self) -> u8 {
        u8::from(self) & 7
    }

    pub(super) fn extended(self) -> bool {
        u8::from(self) & 8 != 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Alu {
    Add,
    Subtract,
    And,
    Or,
    Xor,
    Compare,
    Test,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Condition {
    Equal,
    NotEqual,
    Below,
    NotBelow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemoryWidth {
    Byte,
    Bits16,
    Bits32,
    Word,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RegisterWidth {
    Low32,
    Word,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ShiftDirection {
    Left,
    Right,
}

pub(crate) use faun_core::targets::code::Label;

/// A function-local frame slot, eight bytes here. Its byte offset is
/// assigned only when the instruction is encoded.
pub(crate) use faun_core::codegen::FrameSlot;

/// Where a frame slot lies, eight bytes a slot.
pub(crate) trait SlotOffset {
    fn checked_offset(self) -> Option<u32>;

    fn offset(self) -> u32
    where
        Self: Sized,
    {
        self.checked_offset().expect("a verified x86 frame slot")
    }
}

impl SlotOffset for FrameSlot {
    fn checked_offset(self) -> Option<u32> {
        self.number().checked_mul(8)
    }
}

impl faun_core::codegen::Register for Reg {
    fn number(self) -> u8 {
        u8::from(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Inst {
    XorSelf {
        dst: Reg,
    },
    Move {
        dst: Reg,
        src: Reg,
        width: RegisterWidth,
    },
    PushImmediate(i8),
    PushRegister {
        src: Reg,
    },
    Pop {
        dst: Reg,
    },
    MoveImmediate32 {
        dst: Reg,
        value: u32,
    },
    MoveSignExtendedImmediate32 {
        dst: Reg,
        value: i32,
    },
    MoveImmediate64 {
        dst: Reg,
        value: u64,
    },
    Load {
        width: MemoryWidth,
        dst: Reg,
        base: Reg,
        displacement: i32,
    },
    Store {
        width: MemoryWidth,
        src: Reg,
        base: Reg,
        displacement: i32,
    },
    Narrow {
        dst: Reg,
        bits: u16,
    },
    Shift {
        direction: ShiftDirection,
        dst: Reg,
        by: u8,
        bits: u16,
    },
    /// `dst` moved by the distance in `cl`, at a word's width.
    ShiftByCount {
        direction: ShiftDirection,
        dst: Reg,
    },
    /// The low word of a product; signed and unsigned multiplication agree
    /// on these bits, and no instruction reads a high half.
    Multiply {
        dst: Reg,
        src: Reg,
    },
    /// `src` times a number known before the program runs, in `dst`.
    MultiplyImmediate {
        dst: Reg,
        src: Reg,
        immediate: i32,
        bits: u16,
    },
    /// `src` times three, five or nine, plus a number known before the
    /// program runs, in `dst`: one address worked out and never read, and
    /// the flags left as they were.
    Scale {
        dst: Reg,
        src: Reg,
        times: u8,
        plus: i32,
        bits: u16,
    },
    Divide,
    /// Scalar SSE2 over allocated XMM registers. Binary operations tie
    /// their result to the left input; sqrt has independent operands.
    Float {
        float: faun_core::float::Float,
        dst: Reg,
        left: Reg,
        right: Option<Reg>,
    },
    Syscall,
    /// `hlt`, which a program may not run: the processor faults, and the
    /// kernel ends the program with `SIGSEGV`.
    Halt,
    LoadStack {
        dst: Reg,
        displacement: u32,
    },
    LoadStackNarrow {
        dst: Reg,
        displacement: u32,
        bits: u16,
    },
    LoadFrame {
        dst: Reg,
        slot: FrameSlot,
    },
    StoreFrame {
        src: Reg,
        slot: FrameSlot,
    },
    OpenFrame {
        slots: u32,
    },
    CloseFrame {
        slots: u32,
    },
    Alu {
        op: Alu,
        dst: Reg,
        src: Reg,
        bits: u16,
    },
    AluImmediate {
        op: Alu,
        dst: Reg,
        immediate: i32,
        bits: u16,
    },
    SetIf {
        condition: Condition,
        dst: Reg,
    },
    LoadDataAddress {
        dst: Reg,
        data: DataId,
    },
    Call {
        target: Label,
    },
    Return,
    Jump {
        condition: Option<Condition>,
        target: Label,
    },
}

impl Inst {
    /// Reject a wrong-bank operand before its encoding could silently name
    /// an unrelated physical register with the same instruction bit fields.
    #[expect(
        clippy::too_many_lines,
        reason = "exhaustive bank contract for the physical instruction vocabulary"
    )]
    fn valid_banks(self) -> bool {
        match self {
            Self::Float {
                float,
                dst,
                left,
                right,
            } => {
                dst.is_xmm()
                    && left.is_xmm()
                    && right.is_none_or(Reg::is_xmm)
                    && (float.operation.arity() == 2) == right.is_some()
                    && (right.is_none() || dst == left)
            }
            Self::Load {
                width, dst, base, ..
            } => {
                !base.is_xmm()
                    && (!dst.is_xmm() || matches!(width, MemoryWidth::Bits32 | MemoryWidth::Word))
            }
            Self::Store {
                width, src, base, ..
            } => {
                !base.is_xmm()
                    && (!src.is_xmm() || matches!(width, MemoryWidth::Bits32 | MemoryWidth::Word))
            }
            Self::XorSelf { dst }
            | Self::Pop { dst }
            | Self::MoveImmediate32 { dst, .. }
            | Self::MoveSignExtendedImmediate32 { dst, .. }
            | Self::MoveImmediate64 { dst, .. }
            | Self::Narrow { dst, .. }
            | Self::Shift { dst, .. }
            | Self::ShiftByCount { dst, .. }
            | Self::LoadStackNarrow { dst, .. }
            | Self::AluImmediate { dst, .. }
            | Self::SetIf { dst, .. }
            | Self::LoadDataAddress { dst, .. } => !dst.is_xmm(),
            Self::PushRegister { src } => !src.is_xmm(),
            Self::Multiply { dst, src }
            | Self::MultiplyImmediate { dst, src, .. }
            | Self::Alu { dst, src, .. } => !dst.is_xmm() && !src.is_xmm(),
            // `rsp` names no scaled index.
            Self::Scale { dst, src, .. } => !dst.is_xmm() && !src.is_xmm() && src != Reg::Rsp,
            Self::Move { .. }
            | Self::LoadStack { .. }
            | Self::LoadFrame { .. }
            | Self::StoreFrame { .. }
            | Self::OpenFrame { .. }
            | Self::CloseFrame { .. }
            | Self::PushImmediate(_)
            | Self::Divide
            | Self::Syscall
            | Self::Halt
            | Self::Call { .. }
            | Self::Return
            | Self::Jump { .. } => true,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Allocated {
    /// Every label bound, which finishing the builder checked.
    code: Code<Inst>,
    /// Each function and the label its code starts at, in the order laid
    /// out.
    functions: Vec<(FunctionId, Label)>,
}

impl Allocated {
    /// Each function and the instruction its code starts at, in the order
    /// laid out.
    pub(super) fn functions(&self) -> impl Iterator<Item = (FunctionId, usize)> + '_ {
        self.functions
            .iter()
            .map(|&(function, label)| (function, self.label_position(label)))
    }

    pub(super) fn instructions(&self) -> &[Inst] {
        self.code.insts()
    }

    pub(super) fn label_position(&self, label: Label) -> usize {
        self.code
            .position(label)
            .expect("finishing checked every label is bound")
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one local validity check per allocated instruction family"
    )]
    fn verify(&self) -> Result<(), String> {
        for (at, inst) in self.instructions().iter().enumerate() {
            if !inst.valid_banks() {
                return Err(format!("x86 instruction {at} has invalid register banks"));
            }
            match *inst {
                Inst::Call { target } | Inst::Jump { target, .. }
                    if target.index() >= self.code.labels().len() =>
                {
                    return Err(format!("x86 instruction {at} refers to an unknown label"));
                }
                Inst::Narrow { bits, .. }
                | Inst::Alu { bits, .. }
                | Inst::AluImmediate { bits, .. }
                    if bits > 64 =>
                {
                    return Err(format!("x86 instruction {at} has unsupported width {bits}"));
                }
                Inst::Shift { bits, .. } if bits == 0 || bits > 64 => {
                    return Err(format!("x86 instruction {at} has unsupported width {bits}"));
                }
                Inst::LoadStackNarrow { bits, .. } if !matches!(bits, 8 | 16) => {
                    return Err(format!(
                        "x86 instruction {at} has unsupported stack-load width {bits}"
                    ));
                }
                Inst::OpenFrame { slots } | Inst::CloseFrame { slots } if slots == 0 => {
                    return Err(format!(
                        "x86 instruction {at} has an empty frame adjustment"
                    ));
                }
                Inst::OpenFrame { slots } | Inst::CloseFrame { slots }
                    if slots.checked_mul(8).is_none() =>
                {
                    return Err(format!("x86 instruction {at} has a frame over 4 GiB"));
                }
                Inst::LoadFrame { slot, .. } | Inst::StoreFrame { slot, .. }
                    if slot.checked_offset().is_none() =>
                {
                    return Err(format!(
                        "x86 instruction {at} refers past the 4 GiB frame limit"
                    ));
                }
                _ => {}
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub(crate) struct AllocatedBuilder {
    code: Code<Inst>,
    functions: Vec<(FunctionId, Label)>,
}

impl AllocatedBuilder {
    pub(crate) fn label(&mut self) -> Label {
        self.code.label()
    }

    /// # Panics
    ///
    /// If the label is already bound, or was made by another builder.
    pub(crate) fn bind(&mut self, label: Label) {
        self.code.bind(label);
    }

    /// Say that `function`'s code starts at `label`.
    pub(crate) fn starts(&mut self, function: FunctionId, label: Label) {
        self.functions.push((function, label));
    }

    pub(crate) fn finish(self) -> Result<Allocated, String> {
        if let Some((label, _)) = self.code.labels().find(|(_, position)| position.is_none()) {
            return Err(format!("x86 label l{} is not bound", label.index()));
        }
        let mut code = self.code;
        crate::jumps::thread(&mut code);
        let program = Allocated {
            code,
            functions: self.functions,
        };
        program.verify()?;
        Ok(program)
    }

    fn push(&mut self, inst: Inst) {
        self.code.push(inst);
    }

    pub(crate) fn xor_self(&mut self, dst: Reg) {
        self.push(Inst::XorSelf { dst });
    }

    pub(crate) fn mov_reg(&mut self, dst: Reg, src: Reg, width: RegisterWidth) {
        self.push(Inst::Move { dst, src, width });
    }

    pub(crate) fn push_imm8(&mut self, value: i8) {
        self.push(Inst::PushImmediate(value));
    }

    pub(crate) fn push_reg(&mut self, src: Reg) {
        self.push(Inst::PushRegister { src });
    }

    pub(crate) fn pop(&mut self, dst: Reg) {
        self.push(Inst::Pop { dst });
    }

    pub(crate) fn mov_imm32(&mut self, dst: Reg, value: u32) {
        self.push(Inst::MoveImmediate32 { dst, value });
    }

    pub(crate) fn mov_sext_imm32(&mut self, dst: Reg, value: i32) {
        self.push(Inst::MoveSignExtendedImmediate32 { dst, value });
    }

    pub(crate) fn mov_imm64(&mut self, dst: Reg, value: u64) {
        self.push(Inst::MoveImmediate64 { dst, value });
    }

    pub(crate) fn load(&mut self, width: MemoryWidth, dst: Reg, base: Reg, displacement: i32) {
        self.push(Inst::Load {
            width,
            dst,
            base,
            displacement,
        });
    }

    pub(crate) fn store(&mut self, width: MemoryWidth, src: Reg, base: Reg, displacement: i32) {
        self.push(Inst::Store {
            width,
            src,
            base,
            displacement,
        });
    }

    pub(crate) fn narrow(&mut self, dst: Reg, bits: u16) {
        let len = self.code.insts().len();
        if matches!(bits, 8 | 16)
            && !self.code.labelled_from(len)
            && let Some(Inst::LoadStack {
                dst: loaded,
                displacement,
            }) = self.code.insts().last().copied()
            && loaded == dst
        {
            *self.code.insts_mut().last_mut().expect("the matched load") = Inst::LoadStackNarrow {
                dst,
                displacement,
                bits,
            };
            return;
        }
        self.push(Inst::Narrow { dst, bits });
    }

    pub(crate) fn shift(&mut self, direction: ShiftDirection, dst: Reg, by: u8, bits: u16) {
        self.push(Inst::Shift {
            direction,
            dst,
            by,
            bits,
        });
    }

    pub(crate) fn shift_by_count(&mut self, direction: ShiftDirection, dst: Reg) {
        self.push(Inst::ShiftByCount { direction, dst });
    }

    pub(crate) fn multiply(&mut self, dst: Reg, src: Reg) {
        self.push(Inst::Multiply { dst, src });
    }

    /// `dst` times what was just written into `src` as a constant, taking
    /// the constant back into the instruction. Answers whether it could.
    pub(crate) fn fold_multiply_immediate(&mut self, dst: Reg, src: Reg, bits: u16) -> bool {
        let len = self.code.insts().len();
        if self.code.labelled_from(len.saturating_sub(1)) {
            return false;
        }
        let Some((written, immediate)) = written_constant(self.code.insts(), src, bits) else {
            return false;
        };
        for at in (len - written..len).rev() {
            self.code.remove(at);
        }
        self.push(match immediate {
            3 | 5 | 9 => Inst::Scale {
                dst,
                src: dst,
                times: u8::try_from(immediate).expect("a small multiplier"),
                plus: 0,
                bits,
            },
            _ => Inst::MultiplyImmediate {
                dst,
                src: dst,
                immediate,
                bits,
            },
        });
        true
    }

    pub(crate) fn divide(&mut self) {
        self.push(Inst::Divide);
    }

    pub(crate) fn float(
        &mut self,
        float: faun_core::float::Float,
        dst: Reg,
        left: Reg,
        right: Option<Reg>,
    ) {
        self.push(Inst::Float {
            float,
            dst,
            left,
            right,
        });
    }

    pub(crate) fn syscall(&mut self) {
        self.push(Inst::Syscall);
    }

    pub(crate) fn halt(&mut self) {
        self.push(Inst::Halt);
    }

    /// Drop a narrowing to a byte just before the exit, which keeps only
    /// the status's low byte anyway. A narrower one takes more off than the
    /// exit does, so it stays.
    pub(crate) fn omit_redundant_exit_narrow(&mut self) {
        let len = self.code.insts().len();
        match self.code.insts().get(len.saturating_sub(2)..) {
            Some(
                [
                    Inst::Narrow {
                        dst: narrowed,
                        bits,
                    },
                    Inst::Move {
                        dst: Reg::Rdi,
                        src,
                        width: RegisterWidth::Word,
                    },
                ],
            ) if narrowed == src && *bits == 8 => {
                self.code.remove(len - 2);
                let Some(Inst::Move { width, .. }) = self.code.insts_mut().last_mut() else {
                    unreachable!("the matched exit transfer remains last");
                };
                *width = RegisterWidth::Low32;
            }
            _ if matches!(
                self.code.insts().last(),
                Some(Inst::Narrow {
                    dst: Reg::Rdi,
                    bits: 8
                })
            ) =>
            {
                self.code.remove(len - 1);
            }
            _ => {}
        }
    }

    pub(crate) fn load_stack(&mut self, dst: Reg, displacement: u32) {
        self.push(Inst::LoadStack { dst, displacement });
    }

    pub(crate) fn load_slot(&mut self, dst: Reg, slot: FrameSlot) {
        self.push(Inst::LoadFrame { dst, slot });
    }

    pub(crate) fn store_slot(&mut self, src: Reg, slot: FrameSlot) {
        self.push(Inst::StoreFrame { src, slot });
    }

    pub(crate) fn open_frame(&mut self, slots: u32) {
        self.push(Inst::OpenFrame { slots });
    }

    pub(crate) fn close_frame(&mut self, slots: u32) {
        self.push(Inst::CloseFrame { slots });
    }

    pub(crate) fn alu(&mut self, op: Alu, dst: Reg, src: Reg, bits: u16) {
        self.push(Inst::Alu { op, dst, src, bits });
    }

    pub(crate) fn alu_immediate(&mut self, op: Alu, dst: Reg, immediate: i32, bits: u16) {
        self.push(Inst::AluImmediate {
            op,
            dst,
            immediate,
            bits,
        });
    }

    pub(crate) fn fold_alu_immediate(&mut self, op: Alu, dst: Reg, src: Reg, bits: u16) -> bool {
        let len = self.code.insts().len();
        // Nought compared with is a register tested against itself, which
        // sets the same flags as the comparison and takes no immediate. The
        // test stands where the nought was written, so a jump to either
        // lands on it, and it needs nothing the nought held.
        if op == Alu::Compare
            && let Some(&Inst::XorSelf { dst: materialized }) = self.code.insts().last()
            && materialized == src
        {
            self.code.remove(len - 1);
            self.push(Inst::Alu {
                op: Alu::Test,
                dst,
                src: dst,
                bits,
            });
            return true;
        }
        if self.code.labelled_from(len.saturating_sub(1)) {
            return false;
        }
        let Some((written, immediate)) = written_constant(self.code.insts(), src, bits) else {
            return false;
        };
        for at in (len - written..len).rev() {
            self.code.remove(at);
        }
        if op == Alu::Add && self.displace_scale(dst, immediate, bits) {
            return true;
        }
        self.push(Inst::AluImmediate {
            op,
            dst,
            immediate,
            bits,
        });
        true
    }

    /// A number added to a scaled value just written is the scaling's
    /// displacement, where nothing jumps in between the two. Answers whether
    /// it was.
    fn displace_scale(&mut self, dst: Reg, immediate: i32, bits: u16) -> bool {
        let len = self.code.insts().len();
        if len == 0 || self.code.labelled_from(len) {
            return false;
        }
        let Some(Inst::Scale {
            dst: held,
            plus,
            bits: scaled,
            ..
        }) = self.code.insts_mut().last_mut()
        else {
            return false;
        };
        let Some(sum) = plus.checked_add(immediate) else {
            return false;
        };
        if *held != dst || *scaled != bits {
            return false;
        }
        *plus = sum;
        true
    }

    pub(crate) fn set_if(&mut self, condition: Condition, dst: Reg) {
        self.push(Inst::SetIf { condition, dst });
    }

    pub(crate) fn load_data_address(&mut self, dst: Reg, data: DataId) {
        self.push(Inst::LoadDataAddress { dst, data });
    }

    pub(crate) fn call(&mut self, target: Label) {
        self.push(Inst::Call { target });
    }

    pub(crate) fn ret(&mut self) {
        self.push(Inst::Return);
    }

    pub(crate) fn jump(&mut self, target: Label) {
        self.push(Inst::Jump {
            condition: None,
            target,
        });
    }

    pub(crate) fn jump_if(&mut self, condition: Condition, target: Label) {
        self.push(Inst::Jump {
            condition: Some(condition),
            target,
        });
    }
}

/// How many of the last instructions wrote `src` as a constant, and the
/// immediate an operation at `bits` reads as the same value: a byte pushed
/// and popped, or a move whose immediate the operation's own sign-extends to
/// what the move left.
fn written_constant(insts: &[Inst], src: Reg, bits: u16) -> Option<(usize, i32)> {
    match insts {
        [
            ..,
            Inst::PushImmediate(immediate),
            Inst::Pop { dst: materialized },
        ] if *materialized == src => Some((2, i32::from(*immediate))),
        [
            ..,
            Inst::MoveSignExtendedImmediate32 {
                dst: materialized,
                value,
            },
        ] if *materialized == src => Some((1, *value)),
        [
            ..,
            Inst::MoveImmediate32 {
                dst: materialized,
                value,
            },
        ] if *materialized == src && (bits <= 32 || i32::try_from(*value).is_ok()) => {
            Some((1, value.cast_signed()))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unbound_symbolic_label_is_rejected() {
        let mut builder = AllocatedBuilder::default();
        let target = builder.label();
        builder.jump(target);
        let error = builder.finish().unwrap_err();
        assert_eq!(error, "x86 label l0 is not bound");
    }

    #[test]
    fn frame_slots_stay_symbolic_in_the_instruction_sequence() {
        let mut builder = AllocatedBuilder::default();
        let slot = FrameSlot::at(3);
        builder.load_slot(Reg::Rax, slot);
        let program = builder.finish().unwrap();
        assert_eq!(
            program.instructions(),
            &[Inst::LoadFrame {
                dst: Reg::Rax,
                slot
            }]
        );
    }

    #[test]
    fn exit_status_does_not_need_to_be_zero_extended() {
        let mut builder = AllocatedBuilder::default();
        builder.narrow(Reg::Rax, 8);
        builder.mov_reg(Reg::Rdi, Reg::Rax, RegisterWidth::Word);
        builder.omit_redundant_exit_narrow();
        let program = builder.finish().unwrap();
        assert_eq!(
            program.instructions(),
            &[Inst::Move {
                dst: Reg::Rdi,
                src: Reg::Rax,
                width: RegisterWidth::Low32
            }]
        );
    }

    /// A constant moved in as 32 bits the operation sign-extends alike is
    /// its immediate; one moved in zero-extended is only where both agree.
    #[test]
    fn a_moved_constant_folds_where_its_immediate_means_the_same() {
        let mut builder = AllocatedBuilder::default();
        builder.mov_sext_imm32(Reg::Rcx, -4095);
        assert!(builder.fold_alu_immediate(Alu::Compare, Reg::Rax, Reg::Rcx, 64));
        builder.mov_imm32(Reg::Rcx, u32::MAX);
        assert!(!builder.fold_alu_immediate(Alu::Compare, Reg::Rax, Reg::Rcx, 64));
        assert!(builder.fold_alu_immediate(Alu::Compare, Reg::Rax, Reg::Rcx, 32));
        let program = builder.finish().unwrap();
        assert!(matches!(
            program.instructions(),
            [
                Inst::AluImmediate {
                    immediate: -4095,
                    bits: 64,
                    ..
                },
                Inst::AluImmediate {
                    immediate: -1,
                    bits: 32,
                    ..
                },
            ]
        ));
    }

    #[test]
    fn a_tail_rewrite_leaves_alone_what_a_label_enters() {
        let mut builder = AllocatedBuilder::default();
        builder.push_imm8(5);
        builder.pop(Reg::Rcx);
        assert!(builder.fold_alu_immediate(Alu::Add, Reg::Rax, Reg::Rcx, 64));

        let inside = builder.label();
        builder.push_imm8(5);
        builder.bind(inside);
        builder.pop(Reg::Rcx);
        assert!(!builder.fold_alu_immediate(Alu::Add, Reg::Rax, Reg::Rcx, 64));

        let after = builder.label();
        builder.load_stack(Reg::Rax, 8);
        builder.bind(after);
        builder.narrow(Reg::Rax, 8);
        let program = builder.finish().unwrap();
        assert!(matches!(
            program.instructions(),
            [
                Inst::AluImmediate { immediate: 5, .. },
                Inst::PushImmediate(5),
                Inst::Pop { dst: Reg::Rcx },
                Inst::LoadStack { .. },
                Inst::Narrow { .. },
            ]
        ));
    }

    #[test]
    fn an_unencodable_frame_slot_is_a_verification_error() {
        let mut builder = AllocatedBuilder::default();
        builder.load_slot(Reg::Rax, FrameSlot::at(u32::MAX));
        let error = builder.finish().unwrap_err();
        assert!(error.contains("past the 4 GiB frame limit"), "{error}");
    }
}
