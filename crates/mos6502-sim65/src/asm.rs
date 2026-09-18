//! 6502 instruction encodings, and the labels that tie them together.
//!
//! A conditional is two bytes when its target is within the 127 the
//! machine's relative branches reach, and five when it is not: the inverse
//! branch over a `jmp`. Which is which cannot be known until the addresses
//! are, so [`Assembler::finish`] reports the ones that did not fit and the
//! caller assembles again.

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

#[derive(Default)]
pub(crate) struct Assembler {
    bytes: Vec<u8>,
    /// Where each label landed, once it has been bound.
    labels: Vec<Option<u16>>,
    /// Each hole, and the label it waits on.
    holes: Vec<(usize, Label)>,
    /// The same for the one-byte holes a relative branch leaves, with the
    /// branch's number so the caller can lengthen it.
    near: Vec<(usize, Label, usize)>,
    /// One-byte holes wanting half of a label's address, and which half.
    halves: Vec<(usize, Label, bool)>,
    /// Which branches, by number, have already been found not to reach.
    far: Vec<bool>,
    branches: usize,
    origin: u16,
}

impl Assembler {
    pub(crate) fn new(origin: u16, far: Vec<bool>) -> Self {
        Self {
            far,
            origin,
            ..Self::default()
        }
    }

    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }

    pub(crate) fn bind(&mut self, label: Label) {
        self.labels[label.0] = Some(self.here());
    }

    pub(crate) fn here(&self) -> u16 {
        self.origin + u16::try_from(self.bytes.len()).expect("an image within 64 KiB")
    }

    /// Fill every hole with the address its label ended up at, and report
    /// the branches whose target turned out to be out of reach.
    pub(crate) fn finish(mut self) -> (Vec<u8>, Vec<usize>) {
        for (at, label) in std::mem::take(&mut self.holes) {
            let target = self.labels[label.0].expect("every label is bound");
            self.bytes[at..at + 2].copy_from_slice(&target.to_le_bytes());
        }

        for (at, label, high) in std::mem::take(&mut self.halves) {
            let target = self.labels[label.0].expect("every label is bound");
            let [low, high_byte] = target.to_le_bytes();
            self.bytes[at] = if high { high_byte } else { low };
        }

        let mut overflowed = Vec::new();
        for (at, label, branch) in std::mem::take(&mut self.near) {
            let target = self.labels[label.0].expect("every label is bound");
            // Counted from the end of the branch, which is the byte after
            // the displacement.
            let from = self.origin + u16::try_from(at + 1).expect("an image within 64 KiB");
            match i8::try_from(i32::from(target) - i32::from(from)) {
                Ok(displacement) => self.bytes[at] = displacement.cast_unsigned(),
                Err(_) => overflowed.push(branch),
            }
        }
        (self.bytes, overflowed)
    }

    // Loads and stores. A pair is two zero-page bytes, low first.

    pub(crate) fn lda_imm(&mut self, value: u8) {
        self.emit(&[0xA9, value]);
    }

    /// Half of a label's address, as an immediate.
    pub(crate) fn lda_imm_half(&mut self, label: Label, high: bool) {
        self.emit(&[0xA9]);
        self.halves.push((self.bytes.len(), label, high));
        self.emit(&[0]);
    }

    /// A literal word, for data the target lays down itself.
    pub(crate) fn word(&mut self, value: u16) {
        self.emit(&value.to_le_bytes());
    }

    pub(crate) fn lda_zp(&mut self, at: u8) {
        self.emit(&[0xA5, at]);
    }

    pub(crate) fn sta_zp(&mut self, at: u8) {
        self.emit(&[0x85, at]);
    }

    /// `a = [pair + y]`, and its mirror: the only way to reach a computed
    /// address, since the machine has no sixteen-bit register.
    pub(crate) fn lda_ind_y(&mut self, pair: u8) {
        self.emit(&[0xB1, pair]);
    }

    pub(crate) fn sta_ind_y(&mut self, pair: u8) {
        self.emit(&[0x91, pair]);
    }

    pub(crate) fn ldx_imm(&mut self, value: u8) {
        self.emit(&[0xA2, value]);
    }

    pub(crate) fn ldx_zp(&mut self, at: u8) {
        self.emit(&[0xA6, at]);
    }

    pub(crate) fn ldy_imm(&mut self, value: u8) {
        self.emit(&[0xA0, value]);
    }

    pub(crate) fn iny(&mut self) {
        self.emit(&[0xC8]);
    }

    pub(crate) fn txs(&mut self) {
        self.emit(&[0x9A]);
    }

    // Arithmetic and comparison, all through the accumulator.

    pub(crate) fn clc(&mut self) {
        self.emit(&[0x18]);
    }

    pub(crate) fn sec(&mut self) {
        self.emit(&[0x38]);
    }

    pub(crate) fn adc_zp(&mut self, at: u8) {
        self.emit(&[0x65, at]);
    }

    pub(crate) fn adc_imm(&mut self, value: u8) {
        self.emit(&[0x69, value]);
    }

    pub(crate) fn sbc_zp(&mut self, at: u8) {
        self.emit(&[0xE5, at]);
    }

    pub(crate) fn sbc_imm(&mut self, value: u8) {
        self.emit(&[0xE9, value]);
    }

    pub(crate) fn cmp_imm(&mut self, value: u8) {
        self.emit(&[0xC9, value]);
    }

    pub(crate) fn inc_zp(&mut self, at: u8) {
        self.emit(&[0xE6, at]);
    }

    pub(crate) fn dec_zp(&mut self, at: u8) {
        self.emit(&[0xC6, at]);
    }

    pub(crate) fn cmp_zp(&mut self, at: u8) {
        self.emit(&[0xC5, at]);
    }

    pub(crate) fn ora_zp(&mut self, at: u8) {
        self.emit(&[0x05, at]);
    }

    // Control flow.

    pub(crate) fn jsr(&mut self, label: Label) {
        self.emit(&[0x20]);
        self.hole(label);
    }

    pub(crate) fn jmp(&mut self, label: Label) {
        self.emit(&[0x4C]);
        self.hole(label);
    }

    /// A call to a fixed address, such as one of the simulator's hooks.
    pub(crate) fn jsr_abs(&mut self, at: u16, _back: Label) {
        self.emit(&[0x20]);
        self.emit(&at.to_le_bytes());
    }

    pub(crate) fn jmp_abs(&mut self, at: u16) {
        self.emit(&[0x4C]);
        self.emit(&at.to_le_bytes());
    }

    pub(crate) fn rts(&mut self) {
        self.emit(&[0x60]);
    }

    pub(crate) fn branch(&mut self, cc: Cc, label: Label) {
        let branch = self.branches;
        self.branches += 1;

        if self.far.get(branch).copied().unwrap_or(false) {
            self.emit(&[cc.inverse(), 3]);
            self.jmp(label);
        } else {
            self.emit(&[cc.taken()]);
            self.near.push((self.bytes.len(), label, branch));
            self.emit(&[0]);
        }
    }

    fn hole(&mut self, label: Label) {
        self.holes.push((self.bytes.len(), label));
        self.emit(&[0, 0]);
    }

    fn emit(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }
}
