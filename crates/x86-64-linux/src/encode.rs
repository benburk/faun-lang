//! Each method appends exactly one step, and a step is one instruction
//! except where a caller asked for something that takes two. Choosing
//! between two encodings of the same value is [`super::lower`]'s job, not
//! this module's.

use faun::index::Range;
use faun::ir::Direction;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    /// Nothing here tracks or clobbers it, which is what makes it somewhere
    /// to keep a value for as long as the program runs.
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

    /// The low three bits, which is all `ModRM` and `+r` have room for.
    fn low(self) -> u8 {
        u8::from(self) & 7
    }

    fn extended(self) -> bool {
        u8::from(self) >= 8
    }
}

/// One step the lowering asked for, before anything says where it sits.
///
/// Everything but a jump is the same bytes wherever it lands, so it is kept
/// as the bytes it is. A jump is not: how far it reaches decides whether it
/// spends one byte on the displacement or four, and how far it reaches is
/// not known until everything before it has a width.
enum Inst {
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

impl Inst {
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
pub(crate) struct Encoder {
    /// The steps, in the order they were asked for.
    insts: Vec<Inst>,
    /// Every fixed step's bytes, end to end.
    pool: Vec<u8>,
    /// Where the step now being written began, if one is open.
    open: Option<usize>,
    /// Whether anything was written to a frame slot, which is what says a
    /// frame was needed at all.
    spilled: bool,
}

impl Encoder {
    /// Close whatever step was being written, keeping what it wrote.
    fn close(&mut self) {
        if let Some(start) = self.open.take()
            && self.pool.len() > start
        {
            self.insts
                .push(Inst::Fixed(Range::of(start, self.pool.len() - start)));
        }
    }

    /// Close the step being written and begin another. Every method below
    /// starts with this, which is what makes a step a step.
    fn step(&mut self) {
        self.close();
        self.open = Some(self.pool.len());
    }

    pub(crate) const fn spilled(&self) -> bool {
        self.spilled
    }

    /// Forget what was written to a frame, so that the next function's
    /// answer is about that function alone.
    pub(crate) const fn forget_spilled(&mut self) {
        self.spilled = false;
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
    pub(crate) fn finish(mut self) -> (Vec<u8>, Vec<usize>) {
        self.close();
        let (far, at) = self.settled();
        let mut bytes = Vec::with_capacity(at.last().copied().unwrap_or(0));
        for (id, inst) in self.insts.iter().enumerate() {
            match *inst {
                Inst::Fixed(held) => bytes.extend_from_slice(&self.pool[held.range()]),
                Inst::Call { to } => {
                    let to = to.expect("every call is aimed");
                    let from = at[id] + 5;
                    let step = i64::try_from(at[to]).expect("a reachable offset")
                        - i64::try_from(from).expect("a reachable offset");
                    let step = i32::try_from(step).expect("a call within 2 GiB");
                    bytes.push(0xE8);
                    bytes.extend_from_slice(&step.to_le_bytes());
                }
                Inst::Jump { cc, to } => {
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
                let Inst::Jump { to, .. } = *inst else {
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
    pub(crate) fn xor_self(&mut self, dst: Reg) {
        self.step();
        self.rex(false, Some(dst), dst);
        self.emit(&[0x31, modrm(dst, dst)]);
    }

    pub(crate) fn mov_reg(&mut self, dst: Reg, src: Reg, wide: bool) {
        self.step();
        self.rex(wide, Some(src), dst);
        self.emit(&[0x89, modrm(src, dst)]);
    }

    /// Sign-extends to a full 64-bit stack slot.
    pub(crate) fn push_imm8(&mut self, value: i8) {
        self.step();
        self.emit(&[0x6A, value.cast_unsigned()]);
    }

    pub(crate) fn pop(&mut self, dst: Reg) {
        self.step();
        self.rex(false, None, dst);
        self.emit(&[0x58 + dst.low()]);
    }

    /// Zero-extends to 64 bits.
    pub(crate) fn mov_imm32(&mut self, dst: Reg, value: u32) {
        self.step();
        self.rex(false, None, dst);
        self.emit(&[0xB8 + dst.low()]);
        self.emit(&value.to_le_bytes());
    }

    /// Sign-extended to 64 bits, for negative constants.
    pub(crate) fn mov_sext_imm32(&mut self, dst: Reg, value: i32) {
        self.step();
        // ModRM.reg holds the opcode extension /0, not a register.
        self.rex(true, None, dst);
        self.emit(&[0xC7, modrm(Reg::Rax, dst)]);
        self.emit(&value.to_le_bytes());
    }

    /// The only form that carries a full 64-bit value.
    pub(crate) fn mov_imm64(&mut self, dst: Reg, value: u64) {
        self.step();
        self.emit(&[0x48 | u8::from(dst.extended()), 0xB8 + dst.low()]);
        self.emit(&value.to_le_bytes());
    }

    /// `dst = [base + disp]` and its mirror, in whole words. A `ModRM` mod
    /// of 10 takes a 32-bit displacement; rsp and rbp are not addressable
    /// this way, and nothing here asks to be.
    pub(crate) fn load_word(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x8B], dst, base, disp);
    }

    pub(crate) fn store_word(&mut self, src: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x89], src, base, disp);
    }

    /// The low byte, zero-extended on the way in.
    pub(crate) fn load_byte(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.step();
        self.at(&[0x0F, 0xB6], dst, base, disp);
    }

    pub(crate) fn store_byte(&mut self, src: Reg, base: Reg, disp: i32) {
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
    pub(crate) fn narrow(&mut self, bits: u16) {
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
                self.moved(Direction::Up, by, 64);
                self.moved(Direction::Down, by, 64);
            }
            other => panic!("no {other}-bit form on this target"),
        }
    }

    /// `rax` with its bits moved `by` places, which is a product or quotient
    /// by a power of two.
    pub(crate) fn shift(&mut self, direction: Direction, by: u8, bits: u16) {
        self.step();
        self.moved(direction, by, bits);
    }

    /// The bytes of one shift, opening no instruction of its own, so that a
    /// pair of them can stand as the one thing they are written for.
    ///
    /// One place has a form of its own that carries no distance, and it is
    /// the common one: a doubling is a shift by one, and that form is as
    /// short as the addition it stands in for.
    fn moved(&mut self, direction: Direction, by: u8, bits: u16) {
        let form = match direction {
            Direction::Up => 0xE0,
            Direction::Down => 0xE8,
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
    pub(crate) fn multiply(&mut self) {
        self.step();
        self.emit(&[0x48, 0xF7, 0xE1]);
    }

    /// Unsigned RAX = RDX:RAX / RCX, RDX = remainder. The caller guards zero.
    pub(crate) fn divide(&mut self) {
        self.step();
        self.emit(&[0x48, 0xF7, 0xF1]);
    }

    pub(crate) fn syscall(&mut self) {
        self.step();
        self.emit(&[0x0F, 0x05]);
    }

    /// A `ModRM` `rm` of 100 means a SIB byte follows; 0x24 is rsp as the
    /// base with no index.
    pub(crate) fn load_slot(&mut self, dst: Reg, disp: u32) {
        self.step();
        self.slot(0x8B, dst, disp);
    }

    pub(crate) fn store_slot(&mut self, src: Reg, disp: u32) {
        self.step();
        self.slot(0x89, src, disp);
    }

    /// The `ModRM` mode says how much displacement follows, so a slot near
    /// the stack pointer costs less to reach than a distant one.
    fn slot(&mut self, opcode: u8, reg: Reg, disp: u32) {
        self.spilled = true;
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

    pub(crate) fn open_frame(&mut self, bytes: u32) {
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
    pub(crate) fn alu_sized(&mut self, opcode: u8, dst: Reg, src: Reg, bits: u16) {
        self.step();
        if bits <= 32 {
            self.rex(false, Some(src), dst);
            self.emit(&[opcode, modrm(src, dst)]);
        } else {
            self.alu(opcode, dst, src);
        }
    }

    /// `dst = dst op src`.
    pub(crate) fn alu(&mut self, opcode: u8, dst: Reg, src: Reg) {
        self.step();
        self.rex(true, Some(src), dst);
        self.emit(&[opcode, modrm(src, dst)]);
    }

    /// `dst = 1` when the flags satisfy `cc`, else 0, zero-extended.
    pub(crate) fn set_if(&mut self, cc: u8, dst: Reg) {
        self.step();
        self.rex(false, None, dst);
        self.emit(&[0x0F, 0x90 | cc, 0xC0 | dst.low()]);
        self.rex(false, Some(dst), dst);
        self.emit(&[0x0F, 0xB6, modrm(dst, dst)]);
    }

    /// The displacement is measured from the end of this instruction, and
    /// its offset is returned. `REX.W` is not optional: without it the
    /// address truncates to 32 bits, which ASLR makes fatal.
    /// Answers which step it is. What fills the hole is the layout rather
    /// than [`Encoder::patch`], so what a caller keeps is the step, and
    /// where in the file it lands is read off the finished positions.
    pub(crate) fn lea_rip(&mut self, dst: Reg) -> usize {
        self.step();
        self.rex(true, Some(dst), Reg::Rax);
        self.emit(&[0x8D, (dst.low() << 3) | 5]);
        self.emit(&[0; 4]);
        self.insts.len()
    }

    /// Leaves a hole for [`Encoder::patch`], like any other displacement.
    /// There is no short form of a call, so this is always a full
    /// displacement.
    pub(crate) fn call(&mut self) -> usize {
        self.close();
        self.insts.push(Inst::Call { to: None });
        self.insts.len() - 1
    }

    pub(crate) fn ret(&mut self) {
        self.step();
        self.emit(&[0xC3]);
    }

    pub(crate) fn close_frame(&mut self, bytes: u32) {
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
    pub(crate) fn jump(&mut self) -> usize {
        self.branch(None)
    }

    pub(crate) fn jump_if(&mut self, cc: u8) -> usize {
        self.branch(Some(cc))
    }

    fn branch(&mut self, cc: Option<u8>) -> usize {
        self.close();
        self.insts.push(Inst::Jump { cc, to: None });
        self.insts.len() - 1
    }

    /// Which step comes next, for aiming a jump at it.
    pub(crate) fn here(&mut self) -> usize {
        self.close();
        self.open = Some(self.pool.len());
        self.insts.len()
    }

    /// Where a jump goes, said once there is something to aim it at.
    ///
    /// # Panics
    ///
    /// If what was handed over is not a jump.
    pub(crate) fn patch(&mut self, jump: usize, target: usize) {
        let (Inst::Jump { to, .. } | Inst::Call { to }) = &mut self.insts[jump] else {
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

    fn encoded(build: impl FnOnce(&mut Encoder)) -> Vec<u8> {
        let mut asm = Encoder::default();
        build(&mut asm);
        asm.finish().0
    }

    #[test]
    fn each_form_encodes_to_its_documented_bytes() {
        assert_eq!(encoded(|a| a.xor_self(Reg::Rdi)), [0x31, 0xFF]);
        assert_eq!(encoded(|a| a.pop(Reg::Rdx)), [0x5A]);
        assert_eq!(encoded(|a| a.push_imm8(-5)), [0x6A, 0xFB]);
        assert_eq!(encoded(Encoder::multiply), [0x48, 0xF7, 0xE1]);
        assert_eq!(encoded(Encoder::divide), [0x48, 0xF7, 0xF1]);
        assert_eq!(encoded(|a| a.narrow(0)), [0x31, 0xC0]);
        assert_eq!(encoded(|a| a.narrow(7)), [0x83, 0xE0, 0x7F]);
        assert_eq!(encoded(|a| a.narrow(9)), [0x25, 0xFF, 0x01, 0x00, 0x00]);
        assert_eq!(encoded(|a| a.narrow(32)), [0x89, 0xC0]);
        assert_eq!(
            encoded(|a| a.mov_reg(Reg::Rdi, Reg::Rax, false)),
            [0x89, 0xC7]
        );
        assert_eq!(
            encoded(|a| a.mov_reg(Reg::Rdx, Reg::Rax, true)),
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
    fn high_registers_carry_rex_b() {
        assert_eq!(encoded(|a| a.pop(Reg::R11)), [0x41, 0x5B]);
        assert_eq!(encoded(|a| a.xor_self(Reg::R11)), [0x45, 0x31, 0xDB]);
    }
}
