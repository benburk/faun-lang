//! A target owns everything below the IR: the machine, the environment it
//! calls into, and the files it writes.
//!
//! - Targets share [`bytes`] and nothing else.
//! - Duplication beats an abstraction fitting neither. Their parallel moves
//!   have no common shape: wasm pushes every source before setting any
//!   destination and lets its operand stack swap, where x86-64 routes
//!   through scratch.

pub(crate) mod bytes;
pub mod mos6502_sim65;
pub mod wasm32_wasi;
pub mod x86_64_linux;

use std::fmt;

use crate::ir::{Class, Op, Program, RegionId, ValueId};

#[derive(Debug)]
pub struct Artifact {
    /// Appended to the output name, such as `.wasm`. Empty when the target
    /// writes a bare executable.
    pub extension: &'static str,
    pub bytes: Vec<u8>,
    pub executable: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    X86_64Linux,
    Wasm32Wasi,
    Mos6502Sim65,
}

impl Target {
    pub const ALL: [Self; 3] = [Self::X86_64Linux, Self::Wasm32Wasi, Self::Mos6502Sim65];

    /// The target native to the machine the compiler is running on, if there
    /// is a backend for it. `None` means `--target` is not optional here.
    pub const HOST: Option<Self> = if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        Some(Self::X86_64Linux)
    } else {
        None
    };

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::X86_64Linux => "x86_64-linux",
            Self::Wasm32Wasi => "wasm32-wasi",
            Self::Mos6502Sim65 => "mos6502-sim65",
        }
    }

    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|target| target.name() == name)
    }

    /// The widths this target has forms for, and how wide its own word is.
    /// A program wanting another is one this target cannot compile, which is
    /// a different thing from one it compiles wrongly.
    const fn widths(self) -> (&'static [u16], u16) {
        match self {
            Self::X86_64Linux => (&[8, 16, 32, 64], 64),
            Self::Wasm32Wasi => (&[8, 16, 32], 32),
            Self::Mos6502Sim65 => (&[8, 16], 16),
        }
    }

    /// Whether this target can hold what the program holds.
    ///
    /// A word is as wide as the machine is, so a number the program knows
    /// the size of is a claim about which machines it runs on. Nothing above
    /// this tier can check that claim -- a class says `Word` and means
    /// something different here than it does on the next target along -- so
    /// it is checked here, once, rather than found out by an instruction
    /// that quietly holds less than it was given.
    ///
    /// # Errors
    ///
    /// Names the first thing it cannot hold.
    pub fn accepts(self, program: &Program) -> Result<(), String> {
        let (widths, word) = self.widths();
        for at in 0..program.values_count() {
            let class = program.class(ValueId::at(at));
            if let Class::Fixed { bits } = class
                && !widths.contains(&bits)
            {
                return Err(format!("{self} has no {bits}-bit form"));
            }
        }
        for function in program.functions() {
            self.holds(program, function.body, word)?;
        }
        Ok(())
    }

    /// Every constant in a region, against the width of what holds it.
    fn holds(self, program: &Program, region: RegionId, word: u16) -> Result<(), String> {
        for op in program.ops(region) {
            match *op {
                Op::Constant { class, value } => {
                    let bits = match class {
                        Class::Fixed { bits } => bits,
                        Class::Word | Class::Address => word,
                    };
                    // A fixed width is taken modulo its own, so only a word
                    // can be handed more than it holds.
                    if bits < 64 && value >> bits != 0 {
                        return Err(format!(
                            "{self} holds {bits} bits, and {value} does not fit in them"
                        ));
                    }
                }
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.holds(program, then_region, word)?;
                    self.holds(program, else_region, word)?;
                }
                Op::Loop { body, .. } => self.holds(program, body, word)?,
                _ => {}
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn emit(self, program: &Program) -> Vec<Artifact> {
        match self {
            Self::X86_64Linux => x86_64_linux::emit(program),
            Self::Wasm32Wasi => wasm32_wasi::emit(program),
            Self::Mos6502Sim65 => mos6502_sim65::emit(program),
        }
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}
