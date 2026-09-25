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
    Cpx,
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

/// What an eight-bit register is known to be.
///
/// A number and a place answer different questions -- is this the number it
/// already holds, is this the place it already equals -- and both can be
/// true at once, so keeping one is no reason to give up the other.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Register {
    number: Option<u8>,
    place: Option<u8>,
}

impl Register {
    /// Nothing known, which is where a label leaves it.
    const NOTHING: Self = Self {
        number: None,
        place: None,
    };

    /// What is known after this byte was loaded.
    const fn holding(held: Held) -> Self {
        match held {
            Held::Imm(number) => Self {
                number: Some(number),
                place: None,
            },
            Held::Zero(place) => Self {
                number: None,
                place: Some(place),
            },
        }
    }

    /// Whether reading this byte would tell the register what it already
    /// holds.
    const fn holds(self, held: Held) -> bool {
        match held {
            Held::Imm(value) => matches!(self.number, Some(known) if known == value),
            Held::Zero(at) => matches!(self.place, Some(known) if known == at),
        }
    }

    fn join(self, other: Self) -> Self {
        Self {
            number: same(self.number, other.number),
            place: same(self.place, other.place),
        }
    }
}

/// What is known about the status bits instructions and branches observe.
/// Interrupt and decimal mode are environment controls this target never
/// changes or branches on; the break bit is not persistent processor state.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Flags {
    carry: Option<bool>,
    zero: Option<bool>,
    negative: Option<bool>,
    overflow: Option<bool>,
    /// The register whose present value N and Z were last set from, which
    /// makes a compare of that register against nought say nothing new to
    /// a branch on Z.
    from: Option<Reg>,
}

/// One of the eight-bit registers this assembler tracks.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reg {
    A,
    X,
}

impl Flags {
    const fn with_nz(mut self, value: Option<u8>) -> Self {
        self.zero = match value {
            Some(value) => Some(value == 0),
            None => None,
        };
        self.negative = match value {
            Some(value) => Some(value & 0x80 != 0),
            None => None,
        };
        self
    }

    fn join(self, other: Self) -> Self {
        Self {
            carry: same(self.carry, other.carry),
            zero: same(self.zero, other.zero),
            negative: same(self.negative, other.negative),
            overflow: same(self.overflow, other.overflow),
            from: same(self.from, other.from),
        }
    }
}

fn same<T: Copy + PartialEq>(left: Option<T>, right: Option<T>) -> Option<T> {
    if left == right { left } else { None }
}

/// Retain a register's value while updating whether it still equals memory.
const fn stored(register: Register, operand: Operand) -> Register {
    match operand {
        Operand::Zero(at) => Register {
            place: Some(at),
            ..register
        },
        Operand::Implied | Operand::Imm(_) | Operand::Indirect(_) | Operand::Abs(_) => Register {
            place: None,
            ..register
        },
    }
}

/// A write to a register's remembered place breaks that equality.
fn overwritten(register: Register, operand: Operand) -> Register {
    match operand {
        Operand::Zero(at) if register.place == Some(at) => Register {
            place: None,
            ..register
        },
        // Indirect stores do not reach zero page in this target, but the
        // assembler does not carry that address-space proof.
        Operand::Indirect(_) => Register {
            place: None,
            ..register
        },
        Operand::Implied | Operand::Imm(_) | Operand::Zero(_) | Operand::Abs(_) => register,
    }
}

/// Machine state carried between adjacent selected instructions.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct MachineState {
    acc: Register,
    x: Register,
    flags: Flags,
}

impl MachineState {
    const UNKNOWN: Self = Self {
        acc: Register::NOTHING,
        x: Register::NOTHING,
        flags: Flags {
            carry: None,
            zero: None,
            negative: None,
            overflow: None,
            from: None,
        },
    };

    pub(crate) fn join(self, other: Self) -> Self {
        Self {
            acc: self.acc.join(other.acc),
            x: self.x.join(other.x),
            flags: self.flags.join(other.flags),
        }
    }

    /// Whether a branch on `cc` is taken, where the flag it reads is known.
    const fn decides(self, cc: Cc) -> Option<bool> {
        let (flag, when) = match cc {
            Cc::Equal => (self.flags.zero, true),
            Cc::NotEqual => (self.flags.zero, false),
            Cc::Carry => (self.flags.carry, true),
            Cc::NoCarry => (self.flags.carry, false),
        };
        match flag {
            Some(set) => Some(set == when),
            None => None,
        }
    }

    const fn on_branch(mut self, cc: Cc, taken: bool) -> Self {
        match cc {
            Cc::Equal => self.flags.zero = Some(taken),
            Cc::NotEqual => self.flags.zero = Some(!taken),
            Cc::NoCarry => self.flags.carry = Some(!taken),
            Cc::Carry => self.flags.carry = Some(taken),
        }
        self
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
    /// Whether execution continues somewhere else rather than after this.
    const fn is_jump(self) -> bool {
        matches!(
            self,
            Self::Op {
                mnemonic: Mnemonic::Jmp,
                ..
            } | Self::Absolute {
                mnemonic: Mnemonic::Jmp,
                ..
            }
        )
    }

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
#[expect(
    clippy::too_many_lines,
    reason = "the exhaustive instruction encoding table is clearer in one place"
)]
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
        (M::Asl, O::Implied) => 0x0A,
        (M::Asl, O::Zero(_)) => 0x06,
        (M::Rol, O::Implied) => 0x2A,
        (M::Rol, O::Zero(_)) => 0x26,
        (M::Lsr, O::Implied) => 0x4A,
        (M::Lsr, O::Zero(_)) => 0x46,
        (M::Ror, O::Implied) => 0x6A,
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
        (M::Cpx, O::Imm(_)) => 0xE0,
        (M::Cpx, O::Zero(_)) => 0xE4,
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
    /// What is known about the accumulator and status flags.
    ///
    /// Kept while instructions are selected rather than recovered afterward,
    /// since every emitted instruction passes through this owner.
    state: MachineState,
    /// What every edge written so far into each unbound label agrees on,
    /// or `None` where nothing has jumped there yet.
    arriving: Vec<Option<MachineState>>,
    /// What each bound label took to be known there. An edge written after
    /// the label must agree with it.
    assumed: Vec<Option<MachineState>>,
    /// Whether the next instruction is reached by running into it, which
    /// is not so after a jump or a return.
    unreached: bool,
    /// Zero-page bytes something outside the program reads.
    ///
    /// What reads a byte is otherwise read off the instructions, and an
    /// instruction is not the only thing that can: the simulator is told
    /// where to find the stack it takes a hook's arguments on, and reads it
    /// without any instruction here saying so.
    outside: Vec<u8>,
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

    /// Say that something outside the program reads this byte, so that
    /// nothing here takes a store to it for a store nobody wanted.
    pub(crate) fn read_outside(&mut self, at: u8) {
        self.outside.push(at);
    }

    pub(crate) fn new(origin: u16) -> Self {
        Self {
            origin,
            ..Self::default()
        }
    }

    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        self.arriving.push(None);
        self.assumed.push(None);
        Label(self.labels.len() - 1)
    }

    /// Say that a label stands here, which is before whatever comes next.
    ///
    /// What is known there is what every edge into it agrees on: each jump
    /// and branch written to it so far, and running into it where that
    /// happens. Every edge must be written before the label is bound, save
    /// for ones that agree with what it assumed; a loop's head, which its
    /// own body jumps back to, is bound with [`Self::bind_reentered`].
    pub(crate) fn bind(&mut self, label: Label) {
        let arriving = self.arriving[label.0].take();
        self.state = match (arriving, self.unreached) {
            (Some(arriving), false) => arriving.join(self.state),
            (Some(arriving), true) => arriving,
            (None, false) => self.state,
            (None, true) => MachineState::UNKNOWN,
        };
        self.place(label);
    }

    /// Bind a label something reaches after it is bound, such as a loop's
    /// head, or from where nothing here sees, such as a function's start.
    /// Nothing is assumed there.
    pub(crate) fn bind_reentered(&mut self, label: Label) {
        self.arriving[label.0] = None;
        self.state = MachineState::UNKNOWN;
        self.place(label);
    }

    fn place(&mut self, label: Label) {
        self.assumed[label.0] = Some(self.state);
        self.unreached = false;
        self.labels[label.0] = Some(self.insts.len());
    }

    /// Record an edge into `label` carrying `state`.
    ///
    /// # Panics
    /// If the label is already bound and assumed something this edge does
    /// not bring: the code after it was chosen on a fact that is not so.
    fn arrive(&mut self, label: Label, state: MachineState) {
        if let Some(assumed) = self.assumed[label.0] {
            assert!(
                assumed.join(state) == assumed,
                "an edge into a bound label contradicts what it assumed"
            );
            return;
        }
        let arriving = &mut self.arriving[label.0];
        *arriving = Some(arriving.map_or(state, |known| known.join(state)));
    }

    /// Whether reading this byte would change the accumulator.
    ///
    /// Instruction selection asks before choosing which side of a commutative
    /// operation to read first; [`Self::load`] makes the same decision when it
    /// writes the chosen sequence.
    pub(crate) const fn needs_load(&self, held: Held) -> bool {
        !self.state.acc.holds(held)
    }

    /// Whether `X` already holds this byte.
    pub(crate) const fn x_holds(&self, held: Held) -> bool {
        self.state.x.holds(held)
    }

    /// Whether Z already says if this byte is nought: a register holds it,
    /// and N and Z were set from that register's present value.
    pub(crate) const fn zero_reflects(&self, held: Held) -> bool {
        match self.state.flags.from {
            Some(Reg::A) => self.state.acc.holds(held),
            Some(Reg::X) => self.state.x.holds(held),
            None => false,
        }
    }

    /// Read a byte into the accumulator, unless it already holds it.
    ///
    /// The load left out would have set N and Z from the byte, and they may
    /// reflect something else. A branch that reads them without a compare,
    /// a bit test or a decrement first asks [`Self::zero_reflects`], which
    /// only answers yes where they reflect the register holding it.
    pub(crate) fn load(&mut self, held: Held) {
        if !self.needs_load(held) {
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

    /// A byte's numeric value where current machine state proves one.
    fn number(&self, operand: Operand) -> Option<u8> {
        match operand {
            Operand::Imm(value) => Some(value),
            Operand::Zero(at) => [self.state.acc, self.state.x]
                .into_iter()
                .find_map(|register| {
                    (register.place == Some(at))
                        .then_some(register.number)
                        .flatten()
                }),
            Operand::Implied | Operand::Indirect(_) | Operand::Abs(_) => None,
        }
    }

    /// What is known once an instruction has run.
    fn after(&self, mnemonic: Mnemonic, operand: Operand) -> MachineState {
        let mut state = self.effect(mnemonic, operand);
        state.flags.from = self.nz_from(mnemonic, operand);
        state
    }

    /// Which register N and Z reflect once an instruction has run. Every
    /// instruction that writes A or X sets them from it; those that write
    /// neither the registers nor N and Z leave the answer as it was.
    const fn nz_from(&self, mnemonic: Mnemonic, operand: Operand) -> Option<Reg> {
        use Mnemonic as M;
        match (mnemonic, operand) {
            (M::Lda | M::Adc | M::Sbc | M::And | M::Ora, _)
            | (M::Asl | M::Rol | M::Lsr | M::Ror, Operand::Implied) => Some(Reg::A),
            (M::Ldx | M::Dex, _) => Some(Reg::X),
            (M::Sta | M::Stx | M::Clc | M::Sec | M::Txs | M::Jmp | M::Rts, _) => {
                self.state.flags.from
            }
            _ => None,
        }
    }

    /// What an instruction does to the registers and to what is known of
    /// the flags' values.
    #[expect(
        clippy::too_many_lines,
        reason = "one exhaustive arm per machine instruction family"
    )]
    fn effect(&self, mnemonic: Mnemonic, operand: Operand) -> MachineState {
        use Mnemonic as M;
        let before = self.state;
        match mnemonic {
            M::Lda => self.after_load(operand),
            M::Ldx => self.after_load_x(operand),
            M::Sta => {
                let acc = stored(before.acc, operand);
                let x = overwritten(before.x, operand);
                MachineState { acc, x, ..before }
            }
            M::Stx => {
                let acc = overwritten(before.acc, operand);
                let x = stored(before.x, operand);
                MachineState { acc, x, ..before }
            }
            M::Ldy => MachineState {
                flags: before.flags.with_nz(self.number(operand)),
                ..before
            },
            M::Iny => MachineState {
                flags: before.flags.with_nz(None),
                ..before
            },
            M::Dex => {
                let number = before.x.number.map(|value| value.wrapping_sub(1));
                MachineState {
                    x: Register {
                        number,
                        place: None,
                    },
                    flags: before.flags.with_nz(number),
                    ..before
                }
            }
            M::Clc | M::Sec => MachineState {
                flags: Flags {
                    carry: Some(mnemonic == M::Sec),
                    ..before.flags
                },
                ..before
            },
            M::Cmp => self.after_compare(before.acc, operand),
            M::Cpx => self.after_compare(before.x, operand),
            M::And | M::Ora => self.after_logic(mnemonic, operand),
            M::Adc | M::Sbc => self.after_arithmetic(mnemonic, operand),
            M::Asl | M::Rol | M::Lsr | M::Ror => self.after_shift(mnemonic, operand),
            // These alter a memory byte and N/Z, but not A, X, C or V.
            M::Inc | M::Dec => MachineState {
                acc: overwritten(before.acc, operand),
                x: overwritten(before.x, operand),
                flags: before.flags.with_nz(None),
            },
            // Calls may answer with anything. The jumps themselves preserve
            // state, but no emitted instruction follows them by fallthrough.
            M::Jsr => MachineState::UNKNOWN,
            M::Txs | M::Jmp | M::Rts => before,
        }
    }

    fn loaded(&self, operand: Operand) -> Register {
        let number = self.number(operand);
        match operand {
            Operand::Imm(value) => Register::holding(Held::Imm(value)),
            Operand::Zero(at) => Register {
                number,
                place: Some(at),
            },
            Operand::Implied | Operand::Indirect(_) | Operand::Abs(_) => Register {
                number,
                place: None,
            },
        }
    }

    fn after_load(&self, operand: Operand) -> MachineState {
        let acc = self.loaded(operand);
        MachineState {
            acc,
            flags: self.state.flags.with_nz(acc.number),
            ..self.state
        }
    }

    fn after_load_x(&self, operand: Operand) -> MachineState {
        let x = self.loaded(operand);
        MachineState {
            x,
            flags: self.state.flags.with_nz(x.number),
            ..self.state
        }
    }

    fn after_compare(&self, register: Register, operand: Operand) -> MachineState {
        let flags = match (register.number, self.number(operand)) {
            (Some(left), Some(right)) => self.state.flags.with_nz(Some(left.wrapping_sub(right))),
            _ => self.state.flags.with_nz(None),
        };
        // Nothing is under nought, so a compare against it always sets carry.
        let carry = match (register.number, self.number(operand)) {
            (Some(left), Some(right)) => Some(left >= right),
            (_, Some(0)) => Some(true),
            _ => None,
        };
        MachineState {
            flags: Flags { carry, ..flags },
            ..self.state
        }
    }

    fn after_logic(&self, mnemonic: Mnemonic, operand: Operand) -> MachineState {
        let number = self
            .state
            .acc
            .number
            .zip(self.number(operand))
            .map(|(left, right)| match mnemonic {
                Mnemonic::And => left & right,
                Mnemonic::Ora => left | right,
                _ => unreachable!("a logical instruction"),
            });
        MachineState {
            acc: Register {
                number,
                place: None,
            },
            flags: self.state.flags.with_nz(number),
            ..self.state
        }
    }

    fn after_arithmetic(&self, mnemonic: Mnemonic, operand: Operand) -> MachineState {
        let known = self
            .state
            .acc
            .number
            .zip(self.number(operand))
            .zip(self.state.flags.carry);
        let Some(((left, right), carry)) = known else {
            return MachineState {
                acc: Register::NOTHING,
                flags: Flags::default(),
                ..self.state
            };
        };
        let (number, carry, overflow) = match mnemonic {
            Mnemonic::Adc => {
                let sum = u16::from(left) + u16::from(right) + u16::from(carry);
                let number = sum.to_le_bytes()[0];
                let overflow = (!(left ^ right) & (left ^ number) & 0x80) != 0;
                (number, sum > 0xFF, overflow)
            }
            Mnemonic::Sbc => {
                let subtrahend = u16::from(right) + u16::from(!carry);
                let number = left.wrapping_sub(subtrahend.to_le_bytes()[0]);
                let overflow = ((left ^ number) & (left ^ right) & 0x80) != 0;
                (number, u16::from(left) >= subtrahend, overflow)
            }
            _ => unreachable!("an arithmetic instruction"),
        };
        MachineState {
            acc: Register {
                number: Some(number),
                place: None,
            },
            flags: Flags {
                carry: Some(carry),
                overflow: Some(overflow),
                ..self.state.flags.with_nz(Some(number))
            },
            ..self.state
        }
    }

    fn after_shift(&self, mnemonic: Mnemonic, operand: Operand) -> MachineState {
        let before = self.state;
        let value = match operand {
            Operand::Implied => before.acc.number,
            _ => self.number(operand),
        };
        let known = value.zip(match mnemonic {
            Mnemonic::Rol | Mnemonic::Ror => before.flags.carry,
            Mnemonic::Asl | Mnemonic::Lsr => Some(false),
            _ => unreachable!("a shift instruction"),
        });
        let result = known.map(|(value, carry)| match mnemonic {
            Mnemonic::Asl => (value << 1, value & 0x80 != 0),
            Mnemonic::Rol => ((value << 1) | u8::from(carry), value & 0x80 != 0),
            Mnemonic::Lsr => (value >> 1, value & 1 != 0),
            Mnemonic::Ror => ((value >> 1) | (u8::from(carry) << 7), value & 1 != 0),
            _ => unreachable!("a shift instruction"),
        });
        let number = result.map(|(number, _)| number);
        let acc = match operand {
            Operand::Implied => Register {
                number,
                place: None,
            },
            _ => overwritten(before.acc, operand),
        };
        MachineState {
            acc,
            x: overwritten(before.x, operand),
            flags: Flags {
                carry: result.map(|(_, carry)| carry),
                ..before.flags.with_nz(number)
            },
        }
    }

    /// Fill every hole with the address its label ended up at, and report
    /// the branches whose target turned out to be out of reach.
    /// The image, once every width is known.
    ///
    /// # Panics
    ///
    /// If a label was never bound, or the image outgrew the machine.
    pub(crate) fn finish(mut self) -> Vec<u8> {
        self.drop_unread_stores();
        self.thread_jumps();
        self.drop_repeated_jumps();
        let (far, at) = self.settled();
        let mut bytes = Vec::with_capacity(at.last().copied().unwrap_or(0));
        for (id, inst) in self.insts.iter().enumerate() {
            self.write(*inst, id, &far, &at, &mut bytes);
        }
        bytes
    }

    /// One instruction's bytes, now that every address is known.
    fn write(&self, inst: Inst, id: usize, far: &[bool], at: &[usize], bytes: &mut Vec<u8>) {
        match inst {
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
                bytes.extend_from_slice(&self.address(at, to).to_le_bytes());
            }
            Inst::Half { to, half } => {
                let [low, held] = self.address(at, to).to_le_bytes();
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
                    bytes.extend_from_slice(&self.address(at, to).to_le_bytes());
                } else {
                    let step = self.step_to(at, id, to, 2);
                    let step = i8::try_from(step).expect("a branch that reaches");
                    bytes.extend_from_slice(&[cc.taken(), step.cast_unsigned()]);
                }
            }
        }
    }

    /// Leave out a store to a place nothing ever reads.
    ///
    /// The only reason to keep what a register held is that something reads
    /// it back, and where every reader took it directly from a register the
    /// place it was kept in is written and never looked at.
    ///
    /// Whether anything reads one is a question about the whole program and
    /// not about what follows the store, which is what makes it answerable
    /// here: zero page is only ever reached directly. Every base an indirect
    /// access goes through holds an address above the first page -- the
    /// simulator's argument stack, a frame, a datum, or the heap -- so no
    /// load through one can be the load of a byte kept here.
    fn drop_unread_stores(&mut self) {
        let read = self.bytes_read();
        let kept: Vec<bool> = self
            .insts
            .iter()
            .map(|inst| match *inst {
                Inst::Op {
                    mnemonic: Mnemonic::Sta | Mnemonic::Stx,
                    operand: Operand::Zero(at),
                } => read[usize::from(at)],
                _ => true,
            })
            .collect();
        if kept.iter().all(|held| *held) {
            return;
        }
        self.keeping(&kept);
    }

    /// Send a `jmp` that lands on another `jmp` straight to where that one
    /// goes. The bytes are the same and the second jump's cycles are saved;
    /// a label left with nothing naming it costs nothing.
    fn thread_jumps(&mut self) {
        for at in 0..self.insts.len() {
            // Each step moves to a different jump, so a ring of them is the
            // only way to go on longer than there are instructions.
            for _ in 0..self.insts.len() {
                let Inst::Absolute {
                    mnemonic: Mnemonic::Jmp,
                    to,
                } = self.insts[at]
                else {
                    break;
                };
                let landing = self.labels[to.0].and_then(|id| self.insts.get(id)).copied();
                match landing {
                    Some(next) if next.is_jump() && next != self.insts[at] => {
                        self.insts[at] = next;
                    }
                    _ => break,
                }
            }
        }
    }

    /// Merge adjacent copies of the same unconditional jump.
    ///
    /// A terminal branch arm and the continuation beside it can end at the
    /// same hook or label. Keeping the later jump gives both entries the same
    /// tail: execution that reached the first now falls into the second, and
    /// labels before either instruction move with [`Self::keeping`].
    fn drop_repeated_jumps(&mut self) {
        let kept: Vec<_> = (0..self.insts.len())
            .map(|at| {
                at + 1 == self.insts.len()
                    || !(self.insts[at].is_jump() && self.insts[at] == self.insts[at + 1])
            })
            .collect();
        if kept.iter().all(|held| *held) {
            return;
        }
        self.keeping(&kept);
    }

    /// Which zero-page bytes anything reads.
    fn bytes_read(&self) -> [bool; 256] {
        let mut read = [false; 256];
        for &at in &self.outside {
            read[usize::from(at)] = true;
        }
        for inst in &self.insts {
            let Inst::Op { mnemonic, operand } = *inst else {
                continue;
            };
            match (mnemonic, operand) {
                // A store is the one thing that reads nothing here.
                (Mnemonic::Sta | Mnemonic::Stx, Operand::Zero(_)) => {}
                // Through a pointer it reads the pointer, not what it points
                // at, and what it points at is not here.
                (_, Operand::Indirect(at)) => {
                    read[usize::from(at)] = true;
                    read[usize::from(at.wrapping_add(1))] = true;
                }
                // Everything else that names a byte here reads it, a
                // read-modify-write included.
                (_, Operand::Zero(at)) => read[usize::from(at)] = true,
                _ => {}
            }
        }
        read
    }

    /// Keep the instructions said to be kept, and move every label that
    /// stood before one that is not.
    ///
    /// A label stands before whatever comes next, so one standing before an
    /// instruction that goes stands before whatever that instruction stood
    /// before.
    fn keeping(&mut self, kept: &[bool]) {
        let mut moved = Vec::with_capacity(kept.len() + 1);
        let mut at = 0;
        for held in kept {
            moved.push(at);
            at += usize::from(*held);
        }
        moved.push(at);
        for label in self.labels.iter_mut().flatten() {
            *label = moved[*label];
        }
        let mut insts = std::mem::take(&mut self.insts).into_iter();
        self.insts = kept
            .iter()
            .filter_map(|held| insts.next().filter(|_| *held))
            .collect();
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
        // An address taken is somewhere anything may go, knowing nothing.
        self.arrive(label, MachineState::UNKNOWN);
        self.state = MachineState {
            acc: Register::NOTHING,
            flags: Flags {
                from: Some(Reg::A),
                ..self.state.flags.with_nz(None)
            },
            ..self.state
        };
        self.insts.push(Inst::Half { to: label, half });
    }

    /// A literal word, for data the target lays down itself.
    pub(crate) fn word(&mut self, value: u16) {
        self.state = MachineState::UNKNOWN;
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

    /// Shift the accumulator up one. The bit leaving the top becomes the
    /// carry, which is what a doubling throws away and what the next byte of
    /// a wider one takes in.
    pub(crate) fn asl(&mut self) {
        self.op(Mnemonic::Asl, Operand::Implied);
    }

    /// The same, taking the carry in at the bottom.
    pub(crate) fn rol(&mut self) {
        self.op(Mnemonic::Rol, Operand::Implied);
    }

    /// Shift the accumulator down one, the bit leaving the bottom becoming
    /// the carry.
    pub(crate) fn lsr(&mut self) {
        self.op(Mnemonic::Lsr, Operand::Implied);
    }

    /// The same, taking the carry in at the top.
    pub(crate) fn ror(&mut self) {
        self.op(Mnemonic::Ror, Operand::Implied);
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

    /// The carry, where it is known.
    pub(crate) const fn known_carry(&self) -> Option<bool> {
        self.state.flags.carry
    }

    pub(crate) fn clc(&mut self) {
        if self.state.flags.carry != Some(false) {
            self.op(Mnemonic::Clc, Operand::Implied);
        }
    }

    pub(crate) fn sec(&mut self) {
        if self.state.flags.carry != Some(true) {
            self.op(Mnemonic::Sec, Operand::Implied);
        }
    }

    /// Record a carry result proved by the value bounds used for selection.
    pub(crate) const fn carry_is(&mut self, set: bool) {
        self.state.flags.carry = Some(set);
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

    pub(crate) fn cpx_imm(&mut self, value: u8) {
        self.op(Mnemonic::Cpx, Operand::Imm(value));
    }

    pub(crate) fn cpx_zp(&mut self, at: u8) {
        self.op(Mnemonic::Cpx, Operand::Zero(at));
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

    /// A branch: its target learns the condition held, and what runs on
    /// from here learns it did not. One the flags already decide is not
    /// written where it is never taken, and ends what runs on where it
    /// always is.
    pub(crate) fn branch(&mut self, cc: Cc, label: Label) {
        match self.state.decides(cc) {
            Some(false) => {}
            Some(true) => {
                self.arrive(label, self.state);
                self.unreached = true;
                self.insts.push(Inst::Branch { cc, to: label });
            }
            None => {
                self.arrive(label, self.state.on_branch(cc, true));
                self.state = self.state.on_branch(cc, false);
                self.insts.push(Inst::Branch { cc, to: label });
            }
        }
    }

    fn op(&mut self, mnemonic: Mnemonic, operand: Operand) {
        self.state = self.after(mnemonic, operand);
        self.unreached |= matches!(mnemonic, Mnemonic::Jmp | Mnemonic::Rts);
        self.insts.push(Inst::Op { mnemonic, operand });
    }

    /// A `jmp` or `jsr` to a label, which arrives there with what the
    /// machine holds: neither instruction changes a register or a flag.
    fn absolute(&mut self, mnemonic: Mnemonic, to: Label) {
        self.arrive(to, self.state);
        self.state = MachineState::UNKNOWN;
        self.unreached |= mnemonic == Mnemonic::Jmp;
        self.insts.push(Inst::Absolute { mnemonic, to });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_tracks_every_result_flag() {
        let mut asm = Assembler::new(0x200);
        asm.lda_imm(0x7F);
        asm.clc();
        asm.adc_imm(1);

        assert_eq!(asm.state.acc.number, Some(0x80));
        assert_eq!(asm.state.flags.carry, Some(false));
        assert_eq!(asm.state.flags.zero, Some(false));
        assert_eq!(asm.state.flags.negative, Some(true));
        assert_eq!(asm.state.flags.overflow, Some(true));

        // ADC proved carry clear, so ensuring it again emits nothing.
        asm.clc();
        assert_eq!(asm.finish(), [0xA9, 0x7F, 0x18, 0x69, 0x01]);
    }

    #[test]
    fn x_comparison_preserves_the_accumulator_and_makes_register_spills_dead() {
        let mut asm = Assembler::new(0x200);
        asm.lda_imm(7);
        asm.sta_zp(0x20);
        asm.ldx_imm(0);
        asm.stx_zp(0x21);

        assert!(!asm.needs_load(Held::Zero(0x20)));
        assert!(asm.x_holds(Held::Zero(0x21)));
        asm.cpx_imm(0);
        assert!(!asm.needs_load(Held::Zero(0x20)));
        assert_eq!(asm.state.flags.zero, Some(true));
        assert_eq!(asm.state.flags.carry, Some(true));

        // Neither remembered place is read from memory, so both stores leave.
        assert_eq!(asm.finish(), [0xA9, 0x07, 0xA2, 0x00, 0xE0, 0x00]);
    }

    #[test]
    fn zero_flag_follows_the_register_last_written_until_a_compare() {
        let mut asm = Assembler::new(0x200);
        asm.lda_zp(0x20);
        asm.clc();
        asm.adc_imm(1);
        asm.sta_zp(0x21);
        // A store changes neither A nor the flags set from it.
        assert!(asm.zero_reflects(Held::Zero(0x21)));
        asm.ldx_zp(0x22);
        assert!(!asm.zero_reflects(Held::Zero(0x21)));
        assert!(asm.zero_reflects(Held::Zero(0x22)));
        asm.cmp_imm(3);
        assert!(!asm.zero_reflects(Held::Zero(0x21)));
        assert!(!asm.zero_reflects(Held::Zero(0x22)));
    }

    #[test]
    fn a_jump_to_a_jump_goes_to_the_second_target() {
        let mut asm = Assembler::new(0x200);
        let over = asm.label();
        let tail = asm.label();
        asm.jmp(tail);
        asm.bind(over);
        asm.lda_imm(0);
        asm.bind(tail);
        asm.jmp_abs(0xFFF9);

        assert_eq!(
            asm.finish(),
            [0x4C, 0xF9, 0xFF, 0xA9, 0x00, 0x4C, 0xF9, 0xFF]
        );
    }

    #[test]
    fn adjacent_equal_jumps_share_one_tail() {
        let mut asm = Assembler::new(0x200);
        let common = asm.label();
        asm.branch(Cc::Equal, common);
        asm.lda_imm(0);
        asm.jmp_abs(0xFFF9);
        asm.bind(common);
        asm.jmp_abs(0xFFF9);

        assert_eq!(asm.finish(), [0xF0, 0x02, 0xA9, 0x00, 0x4C, 0xF9, 0xFF]);
    }

    #[test]
    fn a_branch_refines_both_edges_and_a_label_joins_only_agreement() {
        let mut asm = Assembler::new(0x200);
        let target = asm.label();
        asm.branch(Cc::NoCarry, target);
        assert_eq!(asm.state.flags.carry, Some(true));
        let joined = asm.label();
        asm.branch(Cc::Carry, joined);
        // Only the branch reaches `target`, having found carry clear.
        asm.bind(target);
        assert_eq!(asm.state.flags.carry, Some(false));
        // Running into `joined` with carry clear, and branching to it with
        // carry set, leaves carry unknown there.
        asm.bind(joined);
        assert_eq!(asm.state.flags.carry, None);
        assert_eq!(asm.finish(), [0x90, 0x02, 0xB0, 0x00]);
    }

    #[test]
    fn a_branch_the_flags_decide_is_left_out_or_ends_the_run() {
        let mut asm = Assembler::new(0x200);
        let target = asm.label();
        asm.sec();
        asm.branch(Cc::NoCarry, target);
        asm.branch(Cc::Carry, target);
        // Always taken: what follows is reached only through a label.
        assert!(asm.unreached);
        asm.bind(target);
        assert_eq!(asm.state.flags.carry, Some(true));
        assert_eq!(asm.finish(), [0x38, 0xB0, 0x00]);
    }

    #[test]
    fn a_jump_carries_what_it_knows_and_nothing_runs_on_after_it() {
        let mut asm = Assembler::new(0x200);
        let end = asm.label();
        let unreached = asm.label();
        asm.lda_imm(7);
        asm.sta_zp(0x20);
        asm.jmp(end);
        asm.lda_imm(9);
        // The jump is the only way here: what ran on after it never does.
        asm.bind(end);
        assert!(!asm.needs_load(Held::Zero(0x20)));
        asm.rts();
        // Nothing reaches this, so nothing is known here.
        asm.bind(unreached);
        assert!(asm.needs_load(Held::Zero(0x20)));
    }

    #[test]
    #[should_panic(expected = "contradicts what it assumed")]
    fn an_edge_back_into_a_label_must_agree_with_what_it_assumed() {
        let mut asm = Assembler::new(0x200);
        let head = asm.label();
        asm.lda_imm(7);
        asm.bind(head);
        asm.lda_imm(8);
        asm.jmp(head);
    }

    #[test]
    fn a_reentered_label_assumes_nothing() {
        let mut asm = Assembler::new(0x200);
        let head = asm.label();
        asm.lda_imm(7);
        asm.bind_reentered(head);
        assert!(asm.needs_load(Held::Imm(7)));
        asm.lda_imm(8);
        asm.jmp(head);
    }
}
