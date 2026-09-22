//! Encoding of an already selected x86-64 instruction sequence.
//!
//! Branch widths and data positions are layout facts, so symbolic labels,
//! frame slots, and data references become bytes only here.

use super::machine::{
    Allocated, Alu, Condition, Inst, MemoryWidth, Reg, RegisterWidth, ShiftDirection,
};
use super::{Code, Reloc};
use faun::index::Range;

#[expect(
    clippy::too_many_lines,
    reason = "one exhaustive encoding arm per x86 target instruction"
)]
pub(crate) fn encode(program: &Allocated) -> Code {
    let mut asm = RawEncoder::default();
    let mut positions = Vec::with_capacity(program.instructions().len() + 1);
    let mut branches = Vec::new();
    let mut data_references = Vec::new();

    for inst in program.instructions() {
        positions.push(asm.here());
        match *inst {
            Inst::XorSelf { dst } => asm.xor_self(dst),
            Inst::Move { dst, src, width } => {
                asm.mov_reg(dst, src, width == RegisterWidth::Word);
            }
            Inst::PushImmediate(value) => asm.push_imm8(value),
            Inst::Pop { dst } => asm.pop(dst),
            Inst::MoveImmediate32 { dst, value } => asm.mov_imm32(dst, value),
            Inst::MoveSignExtendedImmediate32 { dst, value } => {
                asm.mov_sext_imm32(dst, value);
            }
            Inst::MoveImmediate64 { dst, value } => asm.mov_imm64(dst, value),
            Inst::Load {
                width,
                dst,
                base,
                displacement,
            } => match width {
                MemoryWidth::Byte => asm.load_byte(dst, base, displacement),
                MemoryWidth::Word => asm.load_word(dst, base, displacement),
            },
            Inst::Store {
                width,
                src,
                base,
                displacement,
            } => match width {
                MemoryWidth::Byte => asm.store_byte(src, base, displacement),
                MemoryWidth::Word => asm.store_word(src, base, displacement),
            },
            Inst::Narrow { bits } => asm.narrow(bits),
            Inst::Shift {
                direction,
                by,
                bits,
            } => asm.shift(direction, by, bits),
            Inst::Multiply => asm.multiply(),
            Inst::Divide => asm.divide(),
            Inst::Syscall => asm.syscall(),
            Inst::LoadStack { dst, displacement } => asm.load_slot(dst, displacement),
            Inst::LoadFrame { dst, slot } => asm.load_slot(dst, slot.offset()),
            Inst::StoreFrame { src, slot } => asm.store_slot(src, slot.offset()),
            Inst::OpenFrame { slots } => asm.open_frame(frame_bytes(slots)),
            Inst::CloseFrame { slots } => asm.close_frame(frame_bytes(slots)),
            Inst::Alu { op, dst, src, bits } => {
                asm.alu_sized(alu_opcode(op), dst, src, bits);
            }
            Inst::SetIf { condition, dst } => asm.set_if(condition_code(condition), dst),
            Inst::LoadDataAddress { dst, data } => {
                let step = asm.lea_rip(dst);
                data_references.push((step, data));
            }
            Inst::Call { target } => {
                let hole = asm.call();
                branches.push((hole, target));
            }
            Inst::Return => asm.ret(),
            Inst::Jump { condition, target } => {
                let hole = match condition {
                    Some(condition) => asm.jump_if(condition_code(condition)),
                    None => asm.jump(),
                };
                branches.push((hole, target));
            }
        }
    }
    positions.push(asm.here());

    for (hole, target) in branches {
        asm.patch(hole, positions[program.label_position(target)]);
    }

    let (bytes, raw_positions) = asm.finish();
    let relocs = data_references
        .into_iter()
        .map(|(step, data)| Reloc {
            // The displacement is the last four bytes of the instruction.
            offset: raw_positions[step + 1] - 4,
            data,
        })
        .collect();
    Code { bytes, relocs }
}

const fn frame_bytes(slots: u32) -> u32 {
    slots.checked_mul(8).expect("an x86 frame below 4 GiB")
}

const fn alu_opcode(op: Alu) -> u8 {
    match op {
        Alu::Add => 0x01,
        Alu::Subtract => 0x29,
        Alu::Compare => 0x39,
        Alu::Test => 0x85,
    }
}

const fn condition_code(condition: Condition) -> u8 {
    match condition {
        Condition::Equal => 0x4,
        Condition::NotEqual => 0x5,
        Condition::Below => 0x2,
    }
}

/// One step the lowering asked for, before anything says where it sits.
///
/// Everything but a jump is the same bytes wherever it lands, so it is kept
/// as the bytes it is. A jump is not: how far it reaches decides whether it
/// spends one byte on the displacement or four, and how far it reaches is
/// not known until everything before it has a width.
enum RawInst {
    Fixed(Range),
    Jump {
        cc: Option<u8>,
        to: Option<usize>,
    },
    /// There is no short form of a call, so this is always a full
    /// displacement and never has to be measured.
    Call {
        to: Option<usize>,
    },
}

impl RawInst {
    /// What it costs, given whether a jump was found to need four bytes.
    fn len(&self, far: bool) -> usize {
        match *self {
            Self::Fixed(bytes) => bytes.len(),
            Self::Call { .. } => 5,
            // `EB cb` against `E9 cd`, and `7x cb` against `0F 8x cd`: the
            // near forms are a byte of opcode and a byte of displacement
            // either way, and only the far ones differ.
            Self::Jump { cc: None, .. } if far => 5,
            Self::Jump { cc: Some(_), .. } if far => 6,
            Self::Jump { .. } => 2,
        }
    }
}

#[derive(Default)]
struct RawEncoder {
    /// The steps, in the order they were asked for.
    insts: Vec<RawInst>,
    /// Every fixed step's bytes, end to end.
    pool: Vec<u8>,
    /// Where the step now being written began, if one is open.
    open: Option<usize>,
}

impl RawEncoder {
    /// Close whatever step was being written, keeping what it wrote.
    fn close(&mut self) {
        if let Some(start) = self.open.take()
            && self.pool.len() > start
        {
            self.insts
                .push(RawInst::Fixed(Range::of(start, self.pool.len() - start)));
        }
    }

    /// Close the step being written and begin another. Every method below
    /// starts with this, which is what makes a step a step.
    fn step(&mut self) {
        self.close();
        self.open = Some(self.pool.len());
    }

    /// Where every step lands, and the bytes they come to.
    ///
    /// A jump spends one byte on its displacement where it reaches and
    /// four where it does not, and shortening one can pull another into
    /// reach. So the widths are settled first, by measuring rather than by
    /// writing anything: every jump starts near, and any found not to
    /// reach is widened and the measuring done again. A jump only ever
    /// widens, so this settles.
    ///
    /// # Panics
    ///
    /// If a jump was never aimed, or reaches further than two gigabytes.
    fn finish(mut self) -> (Vec<u8>, Vec<usize>) {
        self.close();
        let (far, at) = self.settled();
        let mut bytes = Vec::with_capacity(at.last().copied().unwrap_or(0));
        for (id, inst) in self.insts.iter().enumerate() {
            match *inst {
                RawInst::Fixed(held) => bytes.extend_from_slice(&self.pool[held.range()]),
                RawInst::Call { to } => {
                    let to = to.expect("every call is aimed");
                    let from = at[id] + 5;
                    let step = i64::try_from(at[to]).expect("a reachable offset")
                        - i64::try_from(from).expect("a reachable offset");
                    let step = i32::try_from(step).expect("a call within 2 GiB");
                    bytes.push(0xE8);
                    bytes.extend_from_slice(&step.to_le_bytes());
                }
                RawInst::Jump { cc, to } => {
                    let to = to.expect("every jump is aimed");
                    let from = at[id] + inst.len(far[id]);
                    let step = i64::try_from(at[to]).expect("a reachable offset")
                        - i64::try_from(from).expect("a reachable offset");
                    match (cc, far[id]) {
                        (None, false) => bytes.push(0xEB),
                        (None, true) => bytes.push(0xE9),
                        (Some(cc), false) => bytes.push(0x70 | cc),
                        (Some(cc), true) => bytes.extend_from_slice(&[0x0F, 0x80 | cc]),
                    }
                    if far[id] {
                        let step = i32::try_from(step).expect("a jump within 2 GiB");
                        bytes.extend_from_slice(&step.to_le_bytes());
                    } else {
                        let step = i8::try_from(step).expect("a jump that reaches");
                        bytes.push(step.cast_unsigned());
                    }
                }
            }
        }
        (bytes, at)
    }

    /// Which jumps need four bytes of displacement, and where every step
    /// lands once they have them.
    ///
    /// Nothing is written to find out. Every jump starts near, and any
    /// found not to reach is widened and the measuring done again; a jump
    /// only ever widens, so this settles.
    ///
    /// # Panics
    ///
    /// If a jump was never aimed.
    fn settled(&self) -> (Vec<bool>, Vec<usize>) {
        let mut far = vec![false; self.insts.len()];
        loop {
            let at = self.positions(&far);
            let mut again = false;
            for (id, inst) in self.insts.iter().enumerate() {
                let RawInst::Jump { to, .. } = *inst else {
                    continue;
                };
                if far[id] {
                    continue;
                }
                let to = to.expect("every jump is aimed");
                let from = at[id] + inst.len(false);
                let step = i64::try_from(at[to]).expect("a reachable offset")
                    - i64::try_from(from).expect("a reachable offset");
                if i8::try_from(step).is_err() {
                    far[id] = true;
                    again = true;
                }
            }
            if !again {
                return (far, at);
            }
        }
    }

    /// Where each step would land, at the widths it was given.
    fn positions(&self, far: &[bool]) -> Vec<usize> {
        let mut at = Vec::with_capacity(self.insts.len() + 1);
        let mut held = 0;
        for (id, inst) in self.insts.iter().enumerate() {
            at.push(held);
            held += inst.len(far[id]);
        }
        at.push(held);
        at
    }

    /// The shortest zeroing, and it clears all 64 bits despite naming the
    /// 32-bit half.
    fn xor_self(&mut self, dst: Reg) {
        self.step();
        self.rex(false, Some(dst), dst);
        self.emit(&[0x31, modrm(dst, dst)]);
    }

    fn mov_reg(&mut self, dst: Reg, src: Reg, wide: bool) {
        self.step();
        self.rex(wide, Some(src), dst);
        self.emit(&[0x89, modrm(src, dst)]);
    }

    /// Sign-extends to a full 64-bit stack slot.
    fn push_imm8(&mut self, value: i8) {
        self.step();
        self.emit(&[0x6A, value.cast_unsigned()]);
    }

    fn pop(&mut self, dst: Reg) {
        self.step();
        self.rex(false, None, dst);
        self.emit(&[0x58 + dst.low()]);
    }

    /// Zero-extends to 64 bits.
    fn mov_imm32(&mut self, dst: Reg, value: u32) {
        self.step();
        self.rex(false, None, dst);
        self.emit(&[0xB8 + dst.low()]);
        self.emit(&value.to_le_bytes());
    }

    /// Sign-extended to 64 bits, for negative constants.
    fn mov_sext_imm32(&mut self, dst: Reg, value: i32) {
        self.step();
        // ModRM.reg holds the opcode extension /0, not a register.
        self.rex(true, None, dst);
        self.emit(&[0xC7, modrm(Reg::Rax, dst)]);
        self.emit(&value.to_le_bytes());
    }

    /// The only form that carries a full 64-bit value.
    fn mov_imm64(&mut self, dst: Reg, value: u64) {
        self.step();
        self.emit(&[0x48 | u8::from(dst.extended()), 0xB8 + dst.low()]);
        self.emit(&value.to_le_bytes());
    }

    /// `dst = [base + disp]` and its mirror, in whole words. A `ModRM` mod
    /// of 10 takes a 32-bit displacement; rsp and rbp are not addressable
    /// this way, and nothing here asks to be.
    fn load_word(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x8B], dst, base, disp);
    }

    fn store_word(&mut self, src: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x89], src, base, disp);
    }

    /// The low byte, zero-extended on the way in.
    fn load_byte(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x0F, 0xB6], dst, base, disp);
    }

    fn store_byte(&mut self, src: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x88], src, base, disp);
    }

    fn at(&mut self, opcode: &[u8], reg: Reg, base: Reg, disp: i32) {
        self.rex(true, Some(reg), base);
        self.emit(opcode);
        self.emit(&[0x80 | (reg.low() << 3) | base.low()]);
        self.emit(&disp.to_le_bytes());
    }

    /// `rax` explicitly taken modulo two to the `bits`, including odd widths.
    fn narrow(&mut self, bits: u16) {
        self.step();
        match bits {
            0 => self.emit(&[0x31, 0xC0]), // xor eax, eax: modulo one is zero
            8 => self.emit(&[0x48, 0x0F, 0xB6, 0xC0]), // movzx rax, al
            16 => self.emit(&[0x48, 0x0F, 0xB7, 0xC0]), // movzx rax, ax
            32 => self.emit(&[0x89, 0xC0]), // mov eax, eax
            64 => {}
            1..=7 => self.emit(&[0x83, 0xE0, (1u8 << bits) - 1]), // and eax, imm8
            9..=31 => {
                self.emit(&[0x25]); // and eax, imm32, zero extending
                self.emit(&((1u32 << bits) - 1).to_le_bytes());
            }
            33..=63 => {
                let by = u8::try_from(64 - bits).expect("a register shift");
                self.moved(ShiftDirection::Left, by, 64);
                self.moved(ShiftDirection::Right, by, 64);
            }
            other => panic!("no {other}-bit form on this target"),
        }
    }

    /// `rax` with its bits moved `by` places, which is a product or quotient
    /// by a power of two.
    fn shift(&mut self, direction: ShiftDirection, by: u8, bits: u16) {
        self.step();
        self.moved(direction, by, bits);
    }

    /// The bytes of one shift, opening no instruction of its own, so that a
    /// pair of them can stand as the one thing they are written for.
    ///
    /// One place has a form of its own that carries no distance, and it is
    /// the common one: a doubling is a shift by one, and that form is as
    /// short as the addition it stands in for.
    fn moved(&mut self, direction: ShiftDirection, by: u8, bits: u16) {
        let form = match direction {
            ShiftDirection::Left => 0xE0,
            ShiftDirection::Right => 0xE8,
        };
        if bits > 32 {
            self.emit(&[0x48]);
        }
        if by == 1 {
            self.emit(&[0xD1, form]);
        } else {
            self.emit(&[0xC1, form, by]);
        }
    }

    /// Unsigned RDX:RAX = RAX * RCX; both result registers are clobbered.
    fn multiply(&mut self) {
        self.step();
        self.emit(&[0x48, 0xF7, 0xE1]);
    }

    /// Unsigned RAX = RDX:RAX / RCX, RDX = remainder. The caller guards zero.
    fn divide(&mut self) {
        self.step();
        self.emit(&[0x48, 0xF7, 0xF1]);
    }

    fn syscall(&mut self) {
        self.step();
        self.emit(&[0x0F, 0x05]);
    }

    /// A `ModRM` `rm` of 100 means a SIB byte follows; 0x24 is rsp as the
    /// base with no index.
    fn load_slot(&mut self, dst: Reg, disp: u32) {
        self.step();
        self.slot(0x8B, dst, disp);
    }

    fn store_slot(&mut self, src: Reg, disp: u32) {
        self.step();
        self.slot(0x89, src, disp);
    }

    /// The `ModRM` mode says how much displacement follows, so a slot near
    /// the stack pointer costs less to reach than a distant one.
    fn slot(&mut self, opcode: u8, reg: Reg, disp: u32) {
        let mode = match disp {
            0 => 0x00,
            1..=0x7F => 0x40,
            _ => 0x80,
        };
        self.emit(&[0x48 | (u8::from(reg.extended()) << 2), opcode]);
        self.emit(&[mode | (reg.low() << 3) | 4, 0x24]);
        match mode {
            0x00 => {}
            0x40 => self.emit(&[disp.to_le_bytes()[0]]),
            _ => self.emit(&disp.to_le_bytes()),
        }
    }

    fn open_frame(&mut self, bytes: u32) {
        self.step();
        self.adjust_rsp(0xEC, bytes);
    }

    /// `dst = dst op src` at the width a class fixes. The 32-bit form is
    /// the one to reach for: it zero-extends into the whole register, so
    /// nothing has to follow it.
    /// `dst = dst op src`, in the narrowest form that leaves nought above
    /// the bits it answers. The eight- and sixteen-bit forms write only
    /// their own half of the register and are no use for that; the
    /// thirty-two-bit one zero-extends into the whole of it, which is both
    /// shorter than the sixty-four-bit form and what keeps a value holding
    /// nothing above what it needs.
    fn alu_sized(&mut self, opcode: u8, dst: Reg, src: Reg, bits: u16) {
        self.step();
        if bits <= 32 {
            self.rex(false, Some(src), dst);
            self.emit(&[opcode, modrm(src, dst)]);
        } else {
            self.alu(opcode, dst, src);
        }
    }

    /// `dst = dst op src`.
    fn alu(&mut self, opcode: u8, dst: Reg, src: Reg) {
        self.step();
        self.rex(true, Some(src), dst);
        self.emit(&[opcode, modrm(src, dst)]);
    }

    /// `dst = 1` when the flags satisfy `cc`, else 0, zero-extended.
    fn set_if(&mut self, cc: u8, dst: Reg) {
        self.step();
        self.rex_byte(None, dst);
        self.emit(&[0x0F, 0x90 | cc, 0xC0 | dst.low()]);
        self.rex_byte(Some(dst), dst);
        self.emit(&[0x0F, 0xB6, modrm(dst, dst)]);
    }

    /// The displacement is measured from the end of this instruction, and
    /// its offset is returned. `REX.W` is not optional: without it the
    /// address truncates to 32 bits, which ASLR makes fatal.
    /// Answers which step it is. What fills the hole is the layout rather
    /// than [`RawEncoder::patch`], so what a caller keeps is the step, and
    /// where in the file it lands is read off the finished positions.
    fn lea_rip(&mut self, dst: Reg) -> usize {
        self.step();
        self.rex(true, Some(dst), Reg::Rax);
        self.emit(&[0x8D, (dst.low() << 3) | 5]);
        self.emit(&[0; 4]);
        self.insts.len()
    }

    /// Leaves a hole for [`RawEncoder::patch`], like any other displacement.
    /// There is no short form of a call, so this is always a full
    /// displacement.
    fn call(&mut self) -> usize {
        self.close();
        self.insts.push(RawInst::Call { to: None });
        self.insts.len() - 1
    }

    fn ret(&mut self) {
        self.step();
        self.emit(&[0xC3]);
    }

    fn close_frame(&mut self, bytes: u32) {
        self.step();
        self.adjust_rsp(0xC4, bytes);
    }

    /// `sub rsp` or `add rsp`, which differ only in their `ModRM`. The
    /// sign-extended byte form takes three bytes fewer, so a small frame
    /// uses it.
    fn adjust_rsp(&mut self, modrm: u8, bytes: u32) {
        if let Ok(small) = i8::try_from(bytes) {
            self.emit(&[0x48, 0x83, modrm, small.cast_unsigned()]);
        } else {
            self.emit(&[0x48, 0x81, modrm]);
            self.emit(&bytes.to_le_bytes());
        }
    }

    /// Unconditional, or taken when the flags satisfy `cc`. Both answer
    /// which step they are, for saying later where they go.
    fn jump(&mut self) -> usize {
        self.branch(None)
    }

    fn jump_if(&mut self, cc: u8) -> usize {
        self.branch(Some(cc))
    }

    fn branch(&mut self, cc: Option<u8>) -> usize {
        self.close();
        self.insts.push(RawInst::Jump { cc, to: None });
        self.insts.len() - 1
    }

    /// Which step comes next, for aiming a jump at it.
    fn here(&mut self) -> usize {
        self.close();
        self.open = Some(self.pool.len());
        self.insts.len()
    }

    /// Where a jump goes, said once there is something to aim it at.
    ///
    /// # Panics
    ///
    /// If what was handed over is not a jump.
    fn patch(&mut self, jump: usize, target: usize) {
        let (RawInst::Jump { to, .. } | RawInst::Call { to }) = &mut self.insts[jump] else {
            panic!("only a jump or a call goes anywhere");
        };
        *to = Some(target);
    }

    /// `reg` is `None` for the forms with no `ModRM` byte. Omitted entirely
    /// when every bit would be zero.
    fn rex(&mut self, wide: bool, reg: Option<Reg>, rm: Reg) {
        let reg = reg.is_some_and(Reg::extended);
        let bits = (u8::from(wide) << 3) | (u8::from(reg) << 2) | u8::from(rm.extended());
        if bits != 0 {
            self.emit(&[0x40 | bits]);
        }
    }

    fn rex_byte(&mut self, reg: Option<Reg>, rm: Reg) {
        let reg = reg.is_some_and(Reg::extended);
        let bits = (u8::from(reg) << 2) | u8::from(rm.extended());
        if bits != 0 || rm.low() >= 4 {
            self.emit(&[0x40 | bits]);
        }
    }

    fn emit(&mut self, bytes: &[u8]) {
        self.pool.extend_from_slice(bytes);
    }
}

fn modrm(reg: Reg, rm: Reg) -> u8 {
    0xC0 | (reg.low() << 3) | rm.low()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::AllocatedBuilder;

    fn encoded(build: impl FnOnce(&mut AllocatedBuilder)) -> Vec<u8> {
        let mut instructions = AllocatedBuilder::default();
        build(&mut instructions);
        encode(&instructions.finish().unwrap()).bytes
    }

    #[test]
    fn each_form_encodes_to_its_documented_bytes() {
        assert_eq!(encoded(|a| a.xor_self(Reg::Rdi)), [0x31, 0xFF]);
        assert_eq!(encoded(|a| a.pop(Reg::Rdx)), [0x5A]);
        assert_eq!(encoded(|a| a.push_imm8(-5)), [0x6A, 0xFB]);
        assert_eq!(encoded(AllocatedBuilder::multiply), [0x48, 0xF7, 0xE1]);
        assert_eq!(encoded(AllocatedBuilder::divide), [0x48, 0xF7, 0xF1]);
        assert_eq!(encoded(|a| a.narrow(0)), [0x31, 0xC0]);
        assert_eq!(encoded(|a| a.narrow(7)), [0x83, 0xE0, 0x7F]);
        assert_eq!(encoded(|a| a.narrow(9)), [0x25, 0xFF, 0x01, 0x00, 0x00]);
        assert_eq!(encoded(|a| a.narrow(32)), [0x89, 0xC0]);
        assert_eq!(
            encoded(|a| a.mov_reg(Reg::Rdi, Reg::Rax, RegisterWidth::Low32)),
            [0x89, 0xC7]
        );
        assert_eq!(
            encoded(|a| a.mov_reg(Reg::Rdx, Reg::Rax, RegisterWidth::Word)),
            [0x48, 0x89, 0xC2]
        );
        #[rustfmt::skip]
        assert_eq!(encoded(|a| a.mov_sext_imm32(Reg::Rdi, -1)),
            [0x48, 0xC7, 0xC7, 0xFF, 0xFF, 0xFF, 0xFF]);
        #[rustfmt::skip]
        assert_eq!(encoded(|a| a.mov_imm64(Reg::Rdx, 0x7FFF_FFFF_FFFF_FFFF)),
            [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
    }

    #[test]
    fn byte_registers_that_need_rex_never_name_legacy_high_bytes() {
        assert_eq!(
            encoded(|a| a.set_if(Condition::Below, Reg::Rsi)),
            [0x40, 0x0F, 0x92, 0xC6, 0x40, 0x0F, 0xB6, 0xF6]
        );
        assert_eq!(
            encoded(|a| a.set_if(Condition::Below, Reg::R8)),
            [0x41, 0x0F, 0x92, 0xC0, 0x45, 0x0F, 0xB6, 0xC0]
        );
    }

    #[test]
    fn high_registers_carry_rex_b() {
        assert_eq!(encoded(|a| a.pop(Reg::R11)), [0x41, 0x5B]);
        assert_eq!(encoded(|a| a.xor_self(Reg::R11)), [0x45, 0x31, 0xDB]);
    }
}
