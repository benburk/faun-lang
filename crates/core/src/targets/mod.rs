//! What a target is, and the little every one of them shares.
//!
//! A target owns everything below the IR: the machine, the environment it
//! calls into, and the files it writes. Each is its own crate and answers
//! [`Target`], which supplies its layout, host contracts, acceptance limits
//! and emission. Representation legalization is shared machine-IR code;
//! instruction selection and file formats remain backend responsibilities.
//!
//! - Targets share [`bytes`] and the checked preparation path.
//! - Duplication beats an abstraction fitting neither. Their parallel moves
//!   have no common shape: wasm pushes every source before setting any
//!   destination and lets its operand stack swap, where x86-64 routes
//!   through scratch.

pub mod bytes;

use std::fmt;

use crate::ir::{Budget, Class, Endian, Layout, Op, Program, Returns, ValueId};

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
/// Shared preparation checks layout and representation; each target checks
/// its own ABI and image limits before emission. Named parameters on the
/// logical entry are supplied by the target's process startup convention.
/// Register placement, calling sequences and file formats remain target-specific.
pub trait Target: fmt::Debug {
    /// What names it on a command line and in what a message says.
    fn name(&self) -> &'static str;

    /// Width of a scalar word and address. Wider Fixed values are rejected;
    /// unbounded Naturals are legalized separately, never implicitly wrapped.
    fn word(&self) -> u16;

    /// Byte order for word-sized memory accesses.
    fn endian(&self) -> Endian {
        Endian::Little
    }

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

    /// Target-specific calling-convention, logical-entry, and representation limits.
    ///
    /// This runs from [`Self::accepts`] after scalar class checks. The IR
    /// itself permits multivalue functions and regions; a target that cannot
    /// implement those shapes must reject them here, before emission, and
    /// declare the same numbers in [`Self::budget`] so preparation fits a
    /// program to them first.
    ///
    /// # Errors
    /// Names an unsupported target-specific program shape.
    fn limits(&self, _program: &Program) -> Result<(), String> {
        Ok(())
    }

    /// How many values its calling convention and region edges carry.
    ///
    /// Preparation packs anything more into a cell, so a program within the
    /// IR's own rules is never refused for how many values cross a boundary.
    /// [`Self::limits`] still checks the prepared program against the same
    /// numbers.
    fn budget(&self) -> Budget {
        Budget::UNLIMITED
    }

    /// Prepare once, then accept and emit that same scalar program.
    ///
    /// # Errors
    /// Reports invalid IR, unsupported representations or target constraints.
    fn compile(&self, program: &Program) -> Result<Vec<Artifact>, String> {
        let prepared = self.prepare(program)?;
        Ok(self.emit(&prepared))
    }

    /// Fit boundaries to [`Self::budget`], then legalize representations
    /// using a bounded, reusable private heap.
    /// Exhaustion terminates with status 2, never a wrapped natural result.
    /// On supported runtime targets, clients needing a different budget can
    /// call `ir::legalize` with an explicit `ir::natural::Config`, then compile
    /// the scalar result. Its recorded layout must match this target; acceptance
    /// rejects mismatched word sizes and byte orders.
    /// This cannot bypass the 16-bit runtime guard: acceptance also checks the
    /// layout recorded on prelegalized input.
    ///
    /// # Errors
    /// Reports invalid IR or a representation this target cannot safely emit.
    fn prepare(&self, program: &Program) -> Result<Program, String> {
        crate::ir::validate(program)?;
        let program = &crate::ir::fit(program, self.budget());
        // The 6502 backend has image/frame and hardware-stack limits not yet
        // audited for generated runtime helpers. Do not enter its infallible
        // emitter with a larger image and hope that address arithmetic fits.
        let naturals = (0..program.values_count())
            .any(|at| program.class(ValueId::at(at)) == Class::Natural)
            || signature_classes(program).any(|&class| class == Class::Natural);
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
        let layout = Layout {
            word_bits: word,
            endian: self.endian(),
        };
        accepts_layout(name, layout, program)?;
        for at in 0..program.values_count() {
            let class = program.class(ValueId::at(at));
            accepts_class(name, word, class)?;
        }
        for &class in signature_classes(program) {
            accepts_class(name, word, class)?;
        }
        accepts_externals(self, program)?;
        for (op, results) in program
            .functions()
            .iter()
            .filter_map(crate::ir::Function::body)
            .flat_map(|body| program.walk_within(body))
        {
            // Encoded constants must fit; narrowing is explicit.
            if let Op::Constant { value } = *op {
                let bits = program.class(results[0]).bits(word);
                if bits < 64 && value >> bits != 0 {
                    return Err(format!(
                        "{name} holds {bits} bits, and {value} does not fit in them"
                    ));
                }
            }
        }
        self.limits(program)
    }
}

fn accepts_externals<T: Target + ?Sized>(target: &T, program: &Program) -> Result<(), String> {
    let (name, word) = (target.name(), target.word());
    let routines = target.routines();
    // Only calls require a provider. Unused declarations remain metadata,
    // just as a frontend environment may offer more routines than are used.
    for op in program
        .functions()
        .iter()
        .filter_map(crate::ir::Function::body)
        .flat_map(|body| program.every(body))
    {
        let Op::Call { function, .. } = *op else {
            continue;
        };
        let function = program.function(function);
        let Some(symbol) = function.external() else {
            continue;
        };
        let held = program.name(symbol);
        let routine = routines
            .get(held)
            .filter(|_| target.provides().contains(&held))
            .ok_or_else(|| format!("{name} answers for nothing called `{held}`"))?;
        let classes_agree = |left: &[Class], right: &[Class]| {
            left.iter()
                .map(|&c| abi_class(c, word))
                .eq(right.iter().map(|&c| abi_class(c, word)))
        };
        if !classes_agree(program.signature(function.params), &routine.reads())
            || !classes_agree(
                program.signature(function.returns.classes()),
                routine.answers().as_slice(),
            )
            || matches!(function.returns, Returns::Never) == routine.comes_back()
        {
            return Err(format!(
                "{name}: external `{held}` disagrees with its provider contract"
            ));
        }
    }
    Ok(())
}

fn accepts_layout(name: &str, layout: Layout, program: &Program) -> Result<(), String> {
    program.check_layout(layout)?;
    // Cell-only preparation uses the bounded 8 KiB heap and its generated
    // release walk is exercised by the 6502 conformance suite. Arbitrary
    // naturals still enter through the guard in `prepare`; prelegalized
    // natural programs do not carry the cell-runtime marker.
    if layout.word_bits == 16
        && program.layout().is_some()
        && (program.has_runtime_naturals() || !program.has_runtime_cells())
    {
        return Err(format!(
            "{name} runtime naturals await checked image/frame limits"
        ));
    }
    Ok(())
}

fn signature_classes(program: &Program) -> impl Iterator<Item = &Class> {
    program.functions().iter().flat_map(|f| {
        program
            .signature(f.params)
            .iter()
            .chain(program.signature(f.returns.classes()))
    })
}

// Environment discovery may refine a Word result to the target's fixed width.
// Both describe the same scalar ABI here, but narrower claims must still agree.
fn abi_class(class: Class, word: u16) -> Class {
    match class {
        Class::Held(_) if matches!(class.width(), Some(bits) if bits == word) => Class::Word,
        class => class,
    }
}

fn accepts_class(name: &str, word: u16, class: Class) -> Result<(), String> {
    if class == Class::Cell {
        return Err(format!(
            "{name} raw emission requires legalization of algebraic cells"
        ));
    }
    if class == Class::Natural {
        return Err(format!(
            "{name} raw emission requires legalization of arbitrary-precision naturals"
        ));
    }
    if let Some(bits) = class.width()
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
        assert!(spartan.get("exit!").is_some());
        assert!(
            spartan.get("write!").is_none(),
            "one it does not answer for"
        );
        assert!(
            crate::platform::Routines::builtin().get("write!").is_some(),
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
            &["exit!"]
        }

        fn emit(&self, _: &Program) -> Vec<Artifact> {
            Vec::new()
        }
    }

    #[test]
    fn abstract_cells_require_preparation_before_raw_emission() {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            let field = b.constant(Class::Word, 1);
            b.cell(0, &[field]);
            let status = b.constant(Class::Word, 0);
            b.ret(&[status]);
        });
        assert!(
            Spartan
                .accepts(&program)
                .unwrap_err()
                .contains("legalization of algebraic cells")
        );
    }

    #[test]
    fn unsupported_bigints_are_rejected_instead_of_wrapping() {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            b.natural(&(num_bigint::BigUint::from(1u8) << 100usize));
            let status = b.constant(Class::Word, 0);
            b.ret(&[status]);
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
            let called = crate::platform::Routines::builtin().declare(&mut program, routine);
            program.define(main, |b: &mut Builder, _| {
                let status = b.constant(Class::Word, 0);
                b.call(called, &[status]);
                b.ret(&[status]);
            });
            Spartan.accepts(&program)
        };

        held("exit!").expect("a routine it answers for");

        let refused = held("write!").unwrap_err();
        assert!(
            refused.contains("spartan answers for nothing called `write!`"),
            "{refused}"
        );
    }
}
