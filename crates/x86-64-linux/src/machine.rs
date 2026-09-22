//! The allocated x86-64 instruction sequence between lowering and encoding.
//!
//! It is deliberately local to this target. Instructions name allocated
//! physical registers, while labels, frame slots, and data references remain
//! symbolic until encoding.

use faun_core::ir::DataId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    /// Reserved for the process argument count.
    Rbx = 3,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
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
            6 => Some(Self::Rsi),
            7 => Some(Self::Rdi),
            8 => Some(Self::R8),
            9 => Some(Self::R9),
            10 => Some(Self::R10),
            11 => Some(Self::R11),
            _ => None,
        }
    }

    pub(super) fn low(self) -> u8 {
        u8::from(self) & 7
    }

    pub(super) fn extended(self) -> bool {
        u8::from(self) >= 8
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Alu {
    Add,
    Subtract,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Label(u32);

impl Label {
    fn at(index: usize) -> Self {
        Self(u32::try_from(index).expect("an x86 function within 4G labels"))
    }

    pub(super) fn index(self) -> usize {
        usize::try_from(self.0).expect("a label index that fits")
    }
}

/// A function-local eight-byte frame slot. Its byte offset is assigned only
/// when the instruction is encoded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FrameSlot(u32);

impl FrameSlot {
    pub(crate) const fn at(index: u32) -> Self {
        Self(index)
    }

    pub(crate) const fn number(self) -> u32 {
        self.0
    }

    const fn checked_offset(self) -> Option<u32> {
        self.0.checked_mul(8)
    }

    pub(super) const fn offset(self) -> u32 {
        self.checked_offset().expect("a verified x86 frame slot")
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
    Multiply,
    Divide,
    Syscall,
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

#[derive(Debug)]
pub(crate) struct Allocated {
    instructions: Vec<Inst>,
    labels: Vec<usize>,
}

impl Allocated {
    pub(super) fn instructions(&self) -> &[Inst] {
        &self.instructions
    }

    pub(super) fn label_position(&self, label: Label) -> usize {
        self.labels[label.index()]
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one local validity check per allocated instruction family"
    )]
    fn verify(&self) -> Result<(), String> {
        for (at, inst) in self.instructions.iter().enumerate() {
            match *inst {
                Inst::Call { target } | Inst::Jump { target, .. }
                    if target.index() >= self.labels.len() =>
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
    instructions: Vec<Inst>,
    labels: Vec<Option<usize>>,
}

impl AllocatedBuilder {
    pub(crate) fn label(&mut self) -> Label {
        let label = Label::at(self.labels.len());
        self.labels.push(None);
        label
    }

    pub(crate) fn bind(&mut self, label: Label) {
        let position = self
            .labels
            .get_mut(label.index())
            .expect("a label made by this x86 builder");
        assert!(position.is_none(), "an x86 label may only be bound once");
        *position = Some(self.instructions.len());
    }

    pub(crate) fn finish(self) -> Result<Allocated, String> {
        let instruction_count = self.instructions.len();
        let labels = self
            .labels
            .into_iter()
            .enumerate()
            .map(|(at, position)| {
                let position = position.ok_or_else(|| format!("x86 label l{at} is not bound"))?;
                if position > instruction_count {
                    return Err(format!(
                        "x86 label l{at} is outside the instruction sequence"
                    ));
                }
                Ok(position)
            })
            .collect::<Result<_, _>>()?;
        let program = Allocated {
            instructions: self.instructions,
            labels,
        };
        program.verify()?;
        Ok(program)
    }

    fn push(&mut self, inst: Inst) {
        self.instructions.push(inst);
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
        if matches!(bits, 8 | 16)
            && let Some(Inst::LoadStack {
                dst: loaded,
                displacement,
            }) = self.instructions.last().copied()
            && loaded == dst
        {
            *self.instructions.last_mut().expect("the matched load") = Inst::LoadStackNarrow {
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

    pub(crate) fn multiply(&mut self) {
        self.push(Inst::Multiply);
    }

    pub(crate) fn divide(&mut self) {
        self.push(Inst::Divide);
    }

    pub(crate) fn syscall(&mut self) {
        self.push(Inst::Syscall);
    }

    pub(crate) fn omit_redundant_exit_narrow(&mut self) {
        let len = self.instructions.len();
        match self.instructions.get(len.saturating_sub(2)..) {
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
            ) if narrowed == src && *bits <= 8 => {
                self.instructions.remove(len - 2);
                let Some(Inst::Move { width, .. }) = self.instructions.last_mut() else {
                    unreachable!("the matched exit transfer remains last");
                };
                *width = RegisterWidth::Low32;
            }
            _ if matches!(
                self.instructions.last(),
                Some(Inst::Narrow {
                    dst: Reg::Rdi,
                    bits: 0..=8
                })
            ) =>
            {
                self.instructions.pop();
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

    pub(crate) fn fold_alu_immediate(&mut self, op: Alu, dst: Reg, src: Reg, bits: u16) -> bool {
        let len = self.instructions.len();
        let immediate = match self.instructions.get(len.wrapping_sub(2)..) {
            Some(
                [
                    Inst::PushImmediate(immediate),
                    Inst::Pop { dst: materialized },
                ],
            ) if *materialized == src => i32::from(*immediate),
            _ => return false,
        };
        self.instructions.truncate(len - 2);
        self.push(Inst::AluImmediate {
            op,
            dst,
            immediate,
            bits,
        });
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

    #[test]
    fn an_unencodable_frame_slot_is_a_verification_error() {
        let mut builder = AllocatedBuilder::default();
        builder.load_slot(Reg::Rax, FrameSlot::at(u32::MAX));
        let error = builder.finish().unwrap_err();
        assert!(error.contains("past the 4 GiB frame limit"), "{error}");
    }
}
