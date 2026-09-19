//! 6502 instruction encodings, and the labels that tie them together.
//!
//! The steps are kept before any of them is written, in the shape every
//! tier above keeps a program: one array of them, another of the bytes the
//! fixed ones are, and an index rather than a pointer to say which.
//!
//! A conditional is two bytes when its target is within the 127 the
//! machine's relative branches reach, and five when it is not: the inverse
//! branch over a `jmp`. Which is which cannot be known until the addresses
//! are, and the addresses cannot be known until it is. So the widths settle
//! first, by measuring the steps rather than by writing any of them.

use faun::index::Range;

#[derive(Clone, Copy)]
pub(crate) struct Label(usize);

/// A condition, as the branch that takes it.
#[derive(Clone, Copy)]
pub(crate) enum Cc {
    Equal,
    NotEqual,
    NoCarry,
    Carry,
}

impl Cc {
    /// The branch taken when this condition holds.
    const fn taken(self) -> u8 {
        match self {
            Self::Equal => 0xF0,    // beq
            Self::NotEqual => 0xD0, // bne
            Self::NoCarry => 0x90,  // bcc
            Self::Carry => 0xB0,    // bcs
        }
    }

    /// The branch taken when it does not, for hopping over a `jmp`.
    const fn inverse(self) -> u8 {
        match self {
            Self::Equal => 0xD0,
            Self::NotEqual => 0xF0,
            Self::NoCarry => 0xB0,
            Self::Carry => 0x90,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Half {
    Low,
    High,
}

/// One step the lowering asked for, before anything says where it sits.
enum Inst {
    /// Bytes that are the same wherever they land.
    Fixed(Range),
    /// A conditional, which is two bytes where it reaches and five where it
    /// does not.
    Branch { cc: Cc, to: Label },
    /// A `jmp` or a `jsr`, which spends two bytes on an address either way.
    Absolute { opcode: u8, to: Label },
    /// Half of an address, as an immediate.
    Half { to: Label, half: Half },
}

impl Inst {
    /// What it costs, given whether a branch was found not to reach.
    fn len(&self, far: bool) -> usize {
        match *self {
            Self::Fixed(bytes) => bytes.len(),
            Self::Branch { .. } if far => 5,
            Self::Absolute { .. } => 3,
            // A branch that reaches, and an immediate: an opcode and one
            // byte either way.
            Self::Branch { .. } | Self::Half { .. } => 2,
        }
    }
}

#[derive(Default)]
pub(crate) struct Assembler {
    /// The steps, in the order they were asked for.
    insts: Vec<Inst>,
    /// Every fixed step's bytes, end to end.
    pool: Vec<u8>,
    /// Where the step now being written began, if one is open.
    open: Option<usize>,
    /// Which step each label stands before, once it has been bound.
    labels: Vec<Option<usize>>,
    origin: u16,
}

impl Assembler {
    pub(crate) fn new(origin: u16) -> Self {
        Self {
            origin,
            ..Self::default()
        }
    }

    /// Close the step being written, keeping what it wrote.
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

    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }

    /// Say that a label stands here, which is before whatever comes next.
    pub(crate) fn bind(&mut self, label: Label) {
        self.close();
        self.labels[label.0] = Some(self.insts.len());
    }

    /// Fill every hole with the address its label ended up at, and report
    /// the branches whose target turned out to be out of reach.
    /// The image, once every width is known.
    ///
    /// # Panics
    ///
    /// If a label was never bound, or the image outgrew the machine.
    pub(crate) fn finish(mut self) -> Vec<u8> {
        self.close();
        let (far, at) = self.settled();

        let mut bytes = Vec::with_capacity(at.last().copied().unwrap_or(0));
        for (id, inst) in self.insts.iter().enumerate() {
            match *inst {
                Inst::Fixed(held) => bytes.extend_from_slice(&self.pool[held.range()]),
                Inst::Absolute { opcode, to } => {
                    bytes.push(opcode);
                    bytes.extend_from_slice(&self.address(&at, to).to_le_bytes());
                }
                Inst::Half { to, half } => {
                    let [low, held] = self.address(&at, to).to_le_bytes();
                    let byte = match half {
                        Half::Low => low,
                        Half::High => held,
                    };
                    bytes.extend_from_slice(&[0xA9, byte]);
                }
                Inst::Branch { cc, to } => {
                    if far[id] {
                        // The inverse branch over a `jmp`, which is three
                        // bytes, so the hop is three.
                        bytes.extend_from_slice(&[cc.inverse(), 3, 0x4C]);
                        bytes.extend_from_slice(&self.address(&at, to).to_le_bytes());
                    } else {
                        let step = self.step_to(&at, id, to, 2);
                        let step = i8::try_from(step).expect("a branch that reaches");
                        bytes.extend_from_slice(&[cc.taken(), step.cast_unsigned()]);
                    }
                }
            }
        }
        bytes
    }

    /// Which branches do not reach, and where every step lands once they
    /// have the width they need.
    ///
    /// Nothing is written to find out. Every branch starts near, and any
    /// found not to reach is widened and the measuring done again; a branch
    /// only ever widens, so this settles.
    fn settled(&self) -> (Vec<bool>, Vec<usize>) {
        let mut far = vec![false; self.insts.len()];
        loop {
            let at = self.positions(&far);
            let mut again = false;
            for (id, inst) in self.insts.iter().enumerate() {
                let Inst::Branch { to, .. } = *inst else {
                    continue;
                };
                if far[id] {
                    continue;
                }
                if i8::try_from(self.step_to(&at, id, to, 2)).is_err() {
                    far[id] = true;
                    again = true;
                }
            }
            if !again {
                return (far, at);
            }
        }
    }

    /// Where each step would land in the image, at the widths it was given.
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

    /// Where a label stands, as the machine addresses it.
    ///
    /// # Panics
    ///
    /// If it was never bound, or the image outgrew the machine.
    fn address(&self, at: &[usize], label: Label) -> u16 {
        let held = self.labels[label.0].expect("every label is bound");
        self.origin + u16::try_from(at[held]).expect("an image within 64 KiB")
    }

    /// How far a branch steps, counted from the byte after it.
    ///
    /// # Panics
    ///
    /// If the label it aims at was never bound.
    fn step_to(&self, at: &[usize], from: usize, to: Label, width: usize) -> i32 {
        let held = self.labels[to.0].expect("every label is bound");
        let after = i32::try_from(at[from] + width).expect("an image within 64 KiB");
        i32::try_from(at[held]).expect("an image within 64 KiB") - after
    }

    // Loads and stores. A pair is two zero-page bytes, low first.

    pub(crate) fn lda_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0xA9, value]);
    }

    /// Half of a label's address, as an immediate.
    pub(crate) fn lda_imm_half(&mut self, label: Label, half: Half) {
        self.close();
        self.insts.push(Inst::Half { to: label, half });
    }

    /// A literal word, for data the target lays down itself.
    pub(crate) fn word(&mut self, value: u16) {
        self.step();
        self.emit(&value.to_le_bytes());
    }

    pub(crate) fn lda_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xA5, at]);
    }

    pub(crate) fn sta_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x85, at]);
    }

    pub(crate) fn stx_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x86, at]);
    }

    /// `a = [pair + y]`, and its mirror: the only way to reach a computed
    /// address, since the machine has no sixteen-bit register.
    pub(crate) fn lda_ind_y(&mut self, pair: u8) {
        self.step();
        self.emit(&[0xB1, pair]);
    }

    pub(crate) fn sta_ind_y(&mut self, pair: u8) {
        self.step();
        self.emit(&[0x91, pair]);
    }

    pub(crate) fn ldx_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0xA2, value]);
    }

    pub(crate) fn ldx_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xA6, at]);
    }

    pub(crate) fn ldy_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0xA0, value]);
    }

    pub(crate) fn iny(&mut self) {
        self.step();
        self.emit(&[0xC8]);
    }

    pub(crate) fn dex(&mut self) {
        self.step();
        self.emit(&[0xCA]);
    }

    pub(crate) fn asl_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x06, at]);
    }

    pub(crate) fn rol_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x26, at]);
    }

    pub(crate) fn lsr_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x46, at]);
    }

    pub(crate) fn ror_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x66, at]);
    }

    pub(crate) fn and_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0x29, value]);
    }

    pub(crate) fn txs(&mut self) {
        self.step();
        self.emit(&[0x9A]);
    }

    // Arithmetic and comparison, all through the accumulator.

    pub(crate) fn clc(&mut self) {
        self.step();
        self.emit(&[0x18]);
    }

    pub(crate) fn sec(&mut self) {
        self.step();
        self.emit(&[0x38]);
    }

    pub(crate) fn adc_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x65, at]);
    }

    pub(crate) fn adc_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0x69, value]);
    }

    pub(crate) fn sbc_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xE5, at]);
    }

    pub(crate) fn sbc_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0xE9, value]);
    }

    pub(crate) fn cmp_imm(&mut self, value: u8) {
        self.step();
        self.emit(&[0xC9, value]);
    }

    pub(crate) fn inc_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xE6, at]);
    }

    pub(crate) fn dec_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xC6, at]);
    }

    pub(crate) fn cmp_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0xC5, at]);
    }

    pub(crate) fn ora_zp(&mut self, at: u8) {
        self.step();
        self.emit(&[0x05, at]);
    }

    // Control flow.

    pub(crate) fn jsr(&mut self, label: Label) {
        self.absolute(0x20, label);
    }

    pub(crate) fn jmp(&mut self, label: Label) {
        self.absolute(0x4C, label);
    }

    /// A call to a fixed address, such as one of the simulator's hooks.
    pub(crate) fn jsr_abs(&mut self, at: u16, _back: Label) {
        self.step();
        self.emit(&[0x20]);
        self.emit(&at.to_le_bytes());
    }

    pub(crate) fn jmp_abs(&mut self, at: u16) {
        self.step();
        self.emit(&[0x4C]);
        self.emit(&at.to_le_bytes());
    }

    pub(crate) fn rts(&mut self) {
        self.step();
        self.emit(&[0x60]);
    }

    pub(crate) fn branch(&mut self, cc: Cc, label: Label) {
        self.close();
        self.insts.push(Inst::Branch { cc, to: label });
    }

    fn absolute(&mut self, opcode: u8, label: Label) {
        self.close();
        self.insts.push(Inst::Absolute { opcode, to: label });
    }

    fn emit(&mut self, bytes: &[u8]) {
        self.pool.extend_from_slice(bytes);
    }
}
