//! 6502 instructions, and the labels that tie them together.
//!
//! An instruction is kept as what it does and what it does it to, not as
//! the bytes it becomes, so that something reading these back can tell a
//! load from a store without decoding one. Bytes are written once, at the
//! end, when every address is known. The shape is the one every tier above
//! keeps a program in: one array of them, and an index rather than a
//! pointer to say which.
//!
//! A conditional is two bytes when its target is within the 127 the
//! machine's relative branches reach, and five when it is not: the inverse
//! branch over a `jmp`. Which is which cannot be known until the addresses
//! are, and the addresses cannot be known until it is. So the widths settle
//! first, by measuring the steps rather than by writing any of them.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Label(usize);

/// A condition, as the branch that takes it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Half {
    Low,
    High,
}

/// What an instruction does.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mnemonic {
    Lda,
    Sta,
    Ldx,
    Stx,
    Ldy,
    Iny,
    Dex,
    Asl,
    Rol,
    Lsr,
    Ror,
    And,
    Ora,
    Txs,
    Clc,
    Sec,
    Adc,
    Sbc,
    Cmp,
    Inc,
    Dec,
    Rts,
    Jsr,
    Jmp,
}

impl Mnemonic {
    /// Whether it writes the hardware stack.
    ///
    /// Said here rather than where one is written, so that adding an
    /// instruction that pushes -- `pha`, `php`, a software interrupt --
    /// means saying so beside the instruction rather than remembering to
    /// say so at every place that writes one.
    const fn pushes(self) -> bool {
        matches!(self, Self::Jsr)
    }
}

/// One byte where the machine can read it without working anything out.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Held {
    Imm(u8),
    Zero(u8),
}

/// What the accumulator is known to be.
///
/// A number and a place answer different questions -- is this the number it
/// already holds, is this the place it already equals -- and both can be
/// true at once, so keeping one is no reason to give up the other.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Acc {
    number: Option<u8>,
    place: Option<u8>,
}

impl Acc {
    /// Nothing known, which is where a label leaves it.
    const NOTHING: Self = Self {
        number: None,
        place: None,
    };

    /// Whether reading this byte would tell the accumulator what it already
    /// holds.
    const fn holds(self, held: Held) -> bool {
        match held {
            Held::Imm(value) => matches!(self.number, Some(known) if known == value),
            Held::Zero(at) => matches!(self.place, Some(known) if known == at),
        }
    }
}

/// What an instruction does it to, which is also how wide it is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Operand {
    /// The instruction is the whole of it.
    Implied,
    Imm(u8),
    /// A zero-page byte.
    Zero(u8),
    /// The byte at the address in a zero-page pair, stepped by `Y`.
    Indirect(u8),
    /// An address written out, for the simulator's hooks.
    Abs(u16),
}

impl Operand {
    const fn len(self) -> usize {
        match self {
            Self::Implied => 0,
            Self::Imm(_) | Self::Zero(_) | Self::Indirect(_) => 1,
            Self::Abs(_) => 2,
        }
    }
}

/// One step the lowering asked for, before anything says where it sits.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Inst {
    /// An instruction, as the machine reads it.
    Op {
        mnemonic: Mnemonic,
        operand: Operand,
    },
    /// A conditional, which is two bytes where it reaches and five where it
    /// does not.
    Branch { cc: Cc, to: Label },
    /// A `jmp` or a `jsr` naming a label, which spends two bytes on an
    /// address either way.
    Absolute { mnemonic: Mnemonic, to: Label },
    /// Half of an address, as an immediate.
    Half { to: Label, half: Half },
    /// A literal word, for data the target lays down itself.
    Word(u16),
}

impl Inst {
    /// What it costs, given whether a branch was found not to reach.
    const fn len(&self, far: bool) -> usize {
        match *self {
            Self::Op { operand, .. } => 1 + operand.len(),
            Self::Branch { .. } if far => 5,
            Self::Absolute { .. } => 3,
            // A branch that reaches, an immediate, and a word: two either
            // way.
            Self::Branch { .. } | Self::Half { .. } | Self::Word(_) => 2,
        }
    }
}

/// The byte the machine reads for an instruction and the way it names what
/// it works on.
///
/// # Panics
/// On a pairing the machine has not got, which nothing here writes: the
/// methods below are the only way to make one.
const fn opcode(mnemonic: Mnemonic, operand: Operand) -> u8 {
    use Mnemonic as M;
    use Operand as O;
    match (mnemonic, operand) {
        (M::Lda, O::Imm(_)) => 0xA9,
        (M::Lda, O::Zero(_)) => 0xA5,
        (M::Lda, O::Indirect(_)) => 0xB1,
        (M::Sta, O::Zero(_)) => 0x85,
        (M::Sta, O::Indirect(_)) => 0x91,
        (M::Ldx, O::Imm(_)) => 0xA2,
        (M::Ldx, O::Zero(_)) => 0xA6,
        (M::Stx, O::Zero(_)) => 0x86,
        (M::Ldy, O::Imm(_)) => 0xA0,
        (M::Iny, O::Implied) => 0xC8,
        (M::Dex, O::Implied) => 0xCA,
        (M::Asl, O::Zero(_)) => 0x06,
        (M::Rol, O::Zero(_)) => 0x26,
        (M::Lsr, O::Zero(_)) => 0x46,
        (M::Ror, O::Zero(_)) => 0x66,
        (M::And, O::Imm(_)) => 0x29,
        (M::Ora, O::Zero(_)) => 0x05,
        (M::Txs, O::Implied) => 0x9A,
        (M::Clc, O::Implied) => 0x18,
        (M::Sec, O::Implied) => 0x38,
        (M::Adc, O::Zero(_)) => 0x65,
        (M::Adc, O::Imm(_)) => 0x69,
        (M::Sbc, O::Zero(_)) => 0xE5,
        (M::Sbc, O::Imm(_)) => 0xE9,
        (M::Cmp, O::Imm(_)) => 0xC9,
        (M::Cmp, O::Zero(_)) => 0xC5,
        (M::Inc, O::Zero(_)) => 0xE6,
        (M::Dec, O::Zero(_)) => 0xC6,
        (M::Rts, O::Implied) => 0x60,
        (M::Jsr, O::Abs(_)) => 0x20,
        (M::Jmp, O::Abs(_)) => 0x4C,
        _ => panic!("no such instruction on this machine"),
    }
}

#[derive(Default)]
pub(crate) struct Assembler {
    /// The instructions, in the order they were asked for.
    insts: Vec<Inst>,
    /// Which instruction each label stands before, once it has been bound.
    labels: Vec<Option<usize>>,
    origin: u16,
    /// What is known about the accumulator.
    ///
    /// Kept while instructions are written rather than worked out after,
    /// since every one of them goes through here and nothing else does.
    acc: Acc,
}

impl Assembler {
    /// Whether anything written pushes onto the hardware stack.
    ///
    /// Read off what was written rather than remembered while writing it,
    /// so that nothing has to say it twice.
    pub(crate) fn pushes(&self) -> bool {
        self.insts.iter().any(|inst| match *inst {
            Inst::Op { mnemonic, .. } | Inst::Absolute { mnemonic, .. } => mnemonic.pushes(),
            Inst::Branch { .. } | Inst::Half { .. } | Inst::Word(_) => false,
        })
    }

    pub(crate) fn new(origin: u16) -> Self {
        Self {
            origin,
            ..Self::default()
        }
    }

    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }

    /// Say that a label stands here, which is before whatever comes next.
    pub(crate) fn bind(&mut self, label: Label) {
        self.acc = Acc::NOTHING;
        self.labels[label.0] = Some(self.insts.len());
    }

    /// Read a byte into the accumulator, unless it already holds it.
    ///
    /// The load left out is one that would have set the negative and zero
    /// flags from the value they already reflect. Nothing between here and
    /// whatever reads those reads them: every branch this target writes is
    /// reached through a compare, a bit test or a decrement, each of which
    /// writes the flags itself.
    pub(crate) fn load(&mut self, held: Held) {
        if self.acc.holds(held) {
            return;
        }
        match held {
            Held::Imm(value) => self.lda_imm(value),
            Held::Zero(at) => self.lda_zp(at),
        }
    }

    /// Put what `from` holds at `to`.
    pub(crate) fn carry(&mut self, from: Held, to: u8) {
        self.load(from);
        self.sta_zp(to);
    }

    /// What is known about the accumulator once an instruction has run.
    fn after(&self, mnemonic: Mnemonic, operand: Operand) -> Acc {
        use Mnemonic as M;
        let held = self.acc;
        match mnemonic {
            M::Lda => match operand {
                Operand::Imm(value) => Acc {
                    number: Some(value),
                    place: None,
                },
                Operand::Zero(at) => Acc {
                    number: None,
                    place: Some(at),
                },
                _ => Acc::NOTHING,
            },
            // Reading is the whole of what these do.
            M::Cmp | M::Ldx | M::Ldy | M::Iny | M::Dex | M::Txs | M::Clc | M::Sec => held,
            // Writing the accumulator somewhere says it equals that place,
            // and says nothing less about the number it holds.
            M::Sta => match operand {
                Operand::Zero(at) => Acc {
                    place: Some(at),
                    ..held
                },
                // Through a pointer it could have written anywhere, so a
                // place the accumulator equalled may have parted from it.
                _ => Acc {
                    place: None,
                    ..held
                },
            },
            // Every other way of writing a place, which the accumulator
            // does not follow.
            M::Stx | M::Inc | M::Dec | M::Asl | M::Rol | M::Lsr | M::Ror => match operand {
                Operand::Zero(at) if held.place == Some(at) => Acc {
                    place: None,
                    ..held
                },
                _ => held,
            },
            // An answer worked out rather than fetched, and leaving
            // altogether.
            M::And | M::Ora | M::Adc | M::Sbc | M::Jsr | M::Jmp | M::Rts => Acc::NOTHING,
        }
    }

    /// Fill every hole with the address its label ended up at, and report
    /// the branches whose target turned out to be out of reach.
    /// The image, once every width is known.
    ///
    /// # Panics
    ///
    /// If a label was never bound, or the image outgrew the machine.
    pub(crate) fn finish(self) -> Vec<u8> {
        let (far, at) = self.settled();

        let mut bytes = Vec::with_capacity(at.last().copied().unwrap_or(0));
        for (id, inst) in self.insts.iter().enumerate() {
            match *inst {
                Inst::Op { mnemonic, operand } => {
                    bytes.push(opcode(mnemonic, operand));
                    match operand {
                        Operand::Implied => {}
                        Operand::Imm(held) | Operand::Zero(held) | Operand::Indirect(held) => {
                            bytes.push(held);
                        }
                        Operand::Abs(held) => bytes.extend_from_slice(&held.to_le_bytes()),
                    }
                }
                Inst::Word(held) => bytes.extend_from_slice(&held.to_le_bytes()),
                Inst::Absolute { mnemonic, to } => {
                    bytes.push(opcode(mnemonic, Operand::Abs(0)));
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
        self.op(Mnemonic::Lda, Operand::Imm(value));
    }

    /// Half of a label's address, as an immediate.
    pub(crate) fn lda_imm_half(&mut self, label: Label, half: Half) {
        self.acc = Acc::NOTHING;
        self.insts.push(Inst::Half { to: label, half });
    }

    /// A literal word, for data the target lays down itself.
    pub(crate) fn word(&mut self, value: u16) {
        self.acc = Acc::NOTHING;
        self.insts.push(Inst::Word(value));
    }

    pub(crate) fn lda_zp(&mut self, at: u8) {
        self.op(Mnemonic::Lda, Operand::Zero(at));
    }

    pub(crate) fn sta_zp(&mut self, at: u8) {
        self.op(Mnemonic::Sta, Operand::Zero(at));
    }

    pub(crate) fn stx_zp(&mut self, at: u8) {
        self.op(Mnemonic::Stx, Operand::Zero(at));
    }

    /// `a = [pair + y]`, and its mirror: the only way to reach a computed
    /// address, since the machine has no sixteen-bit register.
    pub(crate) fn lda_ind_y(&mut self, pair: u8) {
        self.op(Mnemonic::Lda, Operand::Indirect(pair));
    }

    pub(crate) fn sta_ind_y(&mut self, pair: u8) {
        self.op(Mnemonic::Sta, Operand::Indirect(pair));
    }

    pub(crate) fn ldx_imm(&mut self, value: u8) {
        self.op(Mnemonic::Ldx, Operand::Imm(value));
    }

    pub(crate) fn ldx_zp(&mut self, at: u8) {
        self.op(Mnemonic::Ldx, Operand::Zero(at));
    }

    pub(crate) fn ldy_imm(&mut self, value: u8) {
        self.op(Mnemonic::Ldy, Operand::Imm(value));
    }

    pub(crate) fn iny(&mut self) {
        self.op(Mnemonic::Iny, Operand::Implied);
    }

    pub(crate) fn dex(&mut self) {
        self.op(Mnemonic::Dex, Operand::Implied);
    }

    pub(crate) fn asl_zp(&mut self, at: u8) {
        self.op(Mnemonic::Asl, Operand::Zero(at));
    }

    pub(crate) fn rol_zp(&mut self, at: u8) {
        self.op(Mnemonic::Rol, Operand::Zero(at));
    }

    pub(crate) fn lsr_zp(&mut self, at: u8) {
        self.op(Mnemonic::Lsr, Operand::Zero(at));
    }

    pub(crate) fn ror_zp(&mut self, at: u8) {
        self.op(Mnemonic::Ror, Operand::Zero(at));
    }

    pub(crate) fn and_imm(&mut self, value: u8) {
        self.op(Mnemonic::And, Operand::Imm(value));
    }

    pub(crate) fn txs(&mut self) {
        self.op(Mnemonic::Txs, Operand::Implied);
    }

    // Arithmetic and comparison, all through the accumulator.

    pub(crate) fn clc(&mut self) {
        self.op(Mnemonic::Clc, Operand::Implied);
    }

    pub(crate) fn sec(&mut self) {
        self.op(Mnemonic::Sec, Operand::Implied);
    }

    pub(crate) fn adc_zp(&mut self, at: u8) {
        self.op(Mnemonic::Adc, Operand::Zero(at));
    }

    pub(crate) fn adc_imm(&mut self, value: u8) {
        self.op(Mnemonic::Adc, Operand::Imm(value));
    }

    pub(crate) fn sbc_zp(&mut self, at: u8) {
        self.op(Mnemonic::Sbc, Operand::Zero(at));
    }

    pub(crate) fn sbc_imm(&mut self, value: u8) {
        self.op(Mnemonic::Sbc, Operand::Imm(value));
    }

    pub(crate) fn cmp_imm(&mut self, value: u8) {
        self.op(Mnemonic::Cmp, Operand::Imm(value));
    }

    pub(crate) fn inc_zp(&mut self, at: u8) {
        self.op(Mnemonic::Inc, Operand::Zero(at));
    }

    pub(crate) fn dec_zp(&mut self, at: u8) {
        self.op(Mnemonic::Dec, Operand::Zero(at));
    }

    pub(crate) fn cmp_zp(&mut self, at: u8) {
        self.op(Mnemonic::Cmp, Operand::Zero(at));
    }

    pub(crate) fn ora_zp(&mut self, at: u8) {
        self.op(Mnemonic::Ora, Operand::Zero(at));
    }

    // Control flow.

    pub(crate) fn jsr(&mut self, label: Label) {
        self.absolute(Mnemonic::Jsr, label);
    }

    pub(crate) fn jmp(&mut self, label: Label) {
        self.absolute(Mnemonic::Jmp, label);
    }

    /// A call to a fixed address, such as one of the simulator's hooks.
    pub(crate) fn jsr_abs(&mut self, at: u16, _back: Label) {
        self.op(Mnemonic::Jsr, Operand::Abs(at));
    }

    pub(crate) fn jmp_abs(&mut self, at: u16) {
        self.op(Mnemonic::Jmp, Operand::Abs(at));
    }

    pub(crate) fn rts(&mut self) {
        self.op(Mnemonic::Rts, Operand::Implied);
    }

    pub(crate) fn branch(&mut self, cc: Cc, label: Label) {
        self.acc = Acc::NOTHING;
        self.insts.push(Inst::Branch { cc, to: label });
    }

    fn op(&mut self, mnemonic: Mnemonic, operand: Operand) {
        self.acc = self.after(mnemonic, operand);
        self.insts.push(Inst::Op { mnemonic, operand });
    }

    fn absolute(&mut self, mnemonic: Mnemonic, to: Label) {
        self.acc = Acc::NOTHING;
        self.insts.push(Inst::Absolute { mnemonic, to });
    }
}
