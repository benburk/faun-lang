//! What a target is, and the little every one of them shares.
//!
//! A target owns everything below the IR: the machine, the environment it
//! calls into, and the files it writes. Each is its own crate and answers
//! [`Target`], which asks three things -- what it is called, how wide its
//! word is, and what it makes of a program. Everything else a backend does
//! is what that backend does, and not something to agree on.
//!
//! - Targets share [`bytes`] and nothing else.
//! - Duplication beats an abstraction fitting neither. Their parallel moves
//!   have no common shape: wasm pushes every source before setting any
//!   destination and lets its operand stack swap, where x86-64 routes
//!   through scratch.

pub mod bytes;

use std::fmt;

use crate::ir::{Class, Op, Program, ValueId};

#[derive(Debug)]
pub struct Artifact {
    /// Appended to the output name, such as `.wasm`. Empty when the target
    /// writes a bare executable.
    pub extension: &'static str,
    pub bytes: Vec<u8>,
    pub executable: bool,
}

/// A machine, and everything below the IR that reaching it takes.
///
/// Three answers, because nothing else is shared. What one holds a value in,
/// how it calls, what a file of its code looks like -- none of those have a
/// shape two targets both fit, and an abstraction over them would be one
/// more thing to read past on the way to the machine.
pub trait Target: fmt::Debug {
    /// What names it on a command line and in what a message says.
    fn name(&self) -> &'static str;

    /// How wide its own word is, which is the widest value it holds. A width
    /// is what a value needs, so anything narrower than this is held in one
    /// of these and anything wider is a program this target cannot compile
    /// -- which is a different thing from one it compiles wrongly.
    fn word(&self) -> u16;

    /// The routines it answers for, by the name a target is asked by.
    ///
    /// What a program may reach is what its target provides, and no two
    /// provide the same set: one machine has a kernel to ask, another has a
    /// simulator's hooks, and a third has neither and does what it can for
    /// itself. A program naming anything else is refused here rather than
    /// found out by a backend part way through writing it.
    fn provides(&self) -> &'static [&'static str];

    /// The routines a program compiled for it is read against.
    ///
    /// What a compiler knows is not what any one machine can do, so a
    /// program naming something this target has no answer for is refused
    /// where it is written rather than after it is lowered.
    fn routines(&self) -> crate::platform::Routines {
        crate::platform::Routines::builtin()
            .only(self.provides())
            .with_word(self.word())
    }

    /// The files an already validated, accepted scalar program becomes.
    /// Prefer [`Self::compile`], which establishes these preconditions.
    fn emit(&self, program: &Program) -> Vec<Artifact>;

    /// Target-specific calling-convention and representation limits.
    ///
    /// This runs from [`Self::accepts`] after scalar class checks. The IR
    /// itself permits multivalue functions and regions; a target that cannot
    /// implement those shapes must reject them here, before emission.
    ///
    /// # Errors
    /// Names an unsupported target-specific program shape.
    fn limits(&self, _program: &Program) -> Result<(), String> {
        Ok(())
    }

    /// Prepare once, then accept and emit that same scalar program.
    ///
    /// # Errors
    /// Reports invalid IR, unsupported representations or target constraints.
    fn compile(&self, program: &Program) -> Result<Vec<Artifact>, String> {
        let prepared = self.prepare(program)?;
        Ok(self.emit(&prepared))
    }

    /// Legalize representations using a bounded, reusable private heap.
    /// Exhaustion terminates with status 2, never a wrapped natural result.
    /// On supported runtime targets, clients needing a different budget can
    /// call `ir::legalize` with an explicit `ir::natural::Config`, then compile
    /// the scalar result. The config word size MUST match this target: serialized
    /// headers are target sized, which ordinary Address IR cannot detect later.
    /// This is NOT a supported way to bypass the 16-bit guard: manually legalized
    /// scalar input needs a complete backend image/stack capacity audit.
    ///
    /// # Errors
    /// Reports invalid IR or a representation this target cannot safely emit.
    fn prepare(&self, program: &Program) -> Result<Program, String> {
        crate::ir::validate(program)?;
        // The 6502 backend has image/frame and hardware-stack limits not yet
        // audited for generated runtime helpers. Do not enter its infallible
        // emitter with a larger image and hope that address arithmetic fits.
        let naturals = (0..program.values_count())
            .any(|at| program.class(ValueId::at(at)) == Class::Natural)
            || program
                .functions()
                .iter()
                .any(|f| program.signature(f.returns).contains(&Class::Natural));
        if self.word() == 16 && naturals {
            return Err(format!(
                "{} runtime naturals await checked image/frame limits",
                self.name()
            ));
        }
        let prepared = crate::ir::legalize(
            program,
            crate::ir::natural::Config {
                word_bits: self.word(),
                heap_bytes: if self.word() == 16 {
                    8 * 1024
                } else {
                    64 * 1024
                },
            },
        )?;
        self.accepts(&prepared)?;
        Ok(prepared)
    }

    /// Whether it can hold what the program holds.
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
    fn accepts(&self, program: &Program) -> Result<(), String> {
        let (name, word) = (self.name(), self.word());
        for at in 0..program.values_count() {
            let class = program.class(ValueId::at(at));
            accepts_class(name, word, class)?;
        }
        for &class in signature_classes(program) {
            accepts_class(name, word, class)?;
        }
        let provides = self.provides();
        for op in program
            .functions()
            .iter()
            .flat_map(|function| program.every(function.body))
        {
            match *op {
                // A fixed width is taken modulo its own, so only a word can
                // be handed more than it holds.
                Op::Constant { class, value } => {
                    let bits = class.bits(word);
                    if bits < 64 && value >> bits != 0 {
                        return Err(format!(
                            "{name} holds {bits} bits, and {value} does not fit in them"
                        ));
                    }
                }
                Op::PlatformCall { platform, .. } => {
                    let held = program.name(program.platforms()[platform.index()].name);
                    if !provides.contains(&held) {
                        return Err(format!("{name} answers for nothing called `{held}`"));
                    }
                }
                _ => {}
            }
        }
        self.limits(program)
    }
}

fn signature_classes(program: &Program) -> impl Iterator<Item = &Class> {
    let returns = program
        .functions()
        .iter()
        .flat_map(|f| program.signature(f.returns));
    let platform = program.platforms().iter().flat_map(|p| {
        program
            .signature(p.params)
            .iter()
            .chain(program.signature(p.returns))
    });
    returns.chain(platform)
}

fn accepts_class(name: &str, word: u16, class: Class) -> Result<(), String> {
    if class == Class::Natural {
        return Err(format!(
            "{name} raw emission requires legalization of arbitrary-precision naturals"
        ));
    }
    if let Class::Fixed { bits } = class
        && bits > word
    {
        return Err(format!(
            "{name} holds {word} bits, and a value here needs {bits}"
        ));
    }
    Ok(())
}

/// What a program is read against is what its own target answers for, not
/// what every target between them does. A program naming something this one
/// has no answer for never reaches a backend at all.
#[cfg(test)]
mod reading {
    use super::*;

    #[test]
    fn a_program_reads_against_the_routines_of_one_target() {
        let spartan = tests::Spartan.routines();
        assert!(spartan.get("exit").is_some());
        assert!(spartan.get("write").is_none(), "one it does not answer for");
        assert!(
            crate::platform::Routines::builtin().get("write").is_some(),
            "which something else does"
        );
    }
}

/// A target is written the way it is named, wherever one is said.
impl fmt::Display for dyn Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Builder;

    /// A machine with a kernel to ask but nothing to ask it for.
    #[derive(Debug)]
    pub(super) struct Spartan;

    impl Target for Spartan {
        fn name(&self) -> &'static str {
            "spartan"
        }

        fn word(&self) -> u16 {
            32
        }

        fn provides(&self) -> &'static [&'static str] {
            &["exit"]
        }

        fn emit(&self, _: &Program) -> Vec<Artifact> {
            Vec::new()
        }
    }

    #[test]
    fn unsupported_bigints_are_rejected_instead_of_wrapping() {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            b.natural(&(num_bigint::BigUint::from(1u8) << 100usize));
            let status = b.constant(Class::Word, 0);
            b.ret(&[status])
        });
        assert!(
            Spartan
                .accepts(&program)
                .unwrap_err()
                .contains("arbitrary-precision")
        );
    }

    /// What a program may reach is what its target answers for, whether it
    /// is refused where it is written or after it is lowered. One naming
    /// anything else is refused by name, rather than found out by a backend
    /// part way through writing a file it cannot finish.
    #[test]
    fn a_target_refuses_a_routine_it_does_not_answer_for() {
        let held = |routine: &str| {
            let (mut program, main) = Program::new("main");
            let called = program.platform(routine);
            program.define(main, |b: &mut Builder, _| {
                let status = b.constant(Class::Word, 0);
                b.platform_call(called, &[status]);
                b.ret(&[status])
            });
            Spartan.accepts(&program)
        };

        held("exit").expect("a routine it answers for");

        let refused = held("write").unwrap_err();
        assert!(
            refused.contains("spartan answers for nothing called `write`"),
            "{refused}"
        );
    }
}
