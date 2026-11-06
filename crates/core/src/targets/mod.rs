//! What a target is, and the little every one of them shares.
//!
//! A target owns everything below the IR: the machine, the environment it
//! calls into, and the files it writes. Each is its own crate and answers
//! [`Target`], which supplies its layout, host contracts, acceptance limits,
//! emission, and how its image is written and rendered. Representation legalization is shared machine-IR code;
//! instruction selection and file formats remain backend responsibilities.
//!
//! - Targets share [`bytes`], [`code`] for selected instructions and their
//!   labels, and the checked preparation path.
//! - Duplication beats an abstraction fitting neither. Their parallel moves
//!   have no common shape: wasm pushes every source before setting any
//!   destination and lets its operand stack swap, where x86-64 routes
//!   through scratch.

pub mod bytes;
pub mod code;

use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::ir::{Budget, Class, Layout, Op, Program, Returns, ValueId};

/// What a build favours where speed and size pull apart: speed by default.
///
/// Favouring size writes calls where speed would write the case they make,
/// counts each claim taken or given up by a call, and joins sequences
/// without a join routine, in place only after the first. A tiny program
/// joining once is smaller so; one joining often is smaller with the
/// routine, so a build favouring size keeps whichever image is smaller.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Favour {
    #[default]
    Speed,
    Size,
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
    /// Whether it computes IEEE 754 binary32 and binary64 arithmetic with
    /// instructions of its own; see [`crate::platform::Routines::with_floats`].
    fn floats(&self) -> bool {
        false
    }

    fn routines(&self) -> crate::platform::Routines {
        let routines = crate::platform::Routines::builtin()
            .only(self.provides())
            .with_word(self.word());
        if self.floats() {
            routines.with_floats()
        } else {
            routines
        }
    }

    /// The image an already validated, accepted scalar program becomes.
    /// Prefer [`Self::compile_machine_ir`], which establishes these preconditions.
    fn emit(&self, program: &Program) -> Vec<u8>;

    /// The image [`Self::emit`] makes, its code favouring speed or size
    /// where they pull apart, and with [`SymbolTable::Written`] a symbol
    /// naming each function, for a profiler or a disassembler. A target
    /// with no such choices, writing no symbols, makes the same image
    /// whichever is asked; [`Self::emit`] favours speed.
    fn emit_with(&self, program: &Program, favour: Favour, symbols: SymbolTable) -> Vec<u8> {
        let _ = (favour, symbols);
        self.emit(program)
    }

    /// Put an image [`Self::emit`] made at `output`, answering the path it
    /// was written to. The layout on disk is the target's: by default a
    /// plain file at `output`.
    ///
    /// # Errors
    /// Reports what the filesystem refused.
    fn write(&self, image: &[u8], output: &Path) -> io::Result<PathBuf> {
        write_image(output, "", image, false)
    }

    /// What [`Self::emit`] encodes for an already prepared program, in the
    /// target's own readable form, as each tier above renders itself: its
    /// assembly, or the text of a target whose image is text. Where a target
    /// has no form of its own yet, the machine IR it was prepared to, every
    /// runtime routine and representation written out.
    fn render(&self, program: &Program) -> String {
        program.render()
    }

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

    /// Whether it shifts a word by a distance held in a register, in one
    /// instruction. Where it does not, preparation writes such a shift as a
    /// loop of shifts by one place.
    fn shifts_by_register(&self) -> bool {
        false
    }

    /// Prepare once, then accept and emit that same scalar program.
    ///
    /// # Errors
    /// Reports invalid IR, unsupported representations or target constraints.
    fn compile_machine_ir(&self, program: &Program) -> Result<Vec<u8>, String> {
        self.compile_machine_ir_with(program, Favour::Speed, SymbolTable::Omitted)
    }

    /// [`Self::compile_machine_ir`], favouring speed or size where they
    /// pull apart, with symbols as [`Self::emit_with`] writes them.
    ///
    /// # Errors
    /// Reports invalid IR, unsupported representations or target constraints.
    fn compile_machine_ir_with(
        &self,
        program: &Program,
        favour: Favour,
        symbols: SymbolTable,
    ) -> Result<Vec<u8>, String> {
        let image = self.emit_with(&self.prepare_favouring(program, favour)?, favour, symbols);
        if favour == Favour::Speed {
            return Ok(image);
        }
        // What favours size here is calls in place of inline cases and
        // joins, and which is smaller depends on how often a program makes
        // them, so it is built both ways and the smaller kept: either way,
        // claims are counted by calls, and its code is emitted favouring
        // size.
        let faster = self.emit_with(
            &prepare_counting(self, program, Favour::Speed, false)?,
            Favour::Size,
            symbols,
        );
        Ok(if faster.len() < image.len() {
            faster
        } else {
            image
        })
    }

    /// Fit boundaries to [`Self::budget`], then legalize representations
    /// using a reusable private heap that grows as far as the target has room.
    /// Exhaustion terminates with status 2, never a wrapped natural result.
    /// On supported runtime targets, clients needing a different budget can
    /// call `ir::legalize` with an explicit `ir::natural::Config`, then compile
    /// the scalar result. Its recorded layout must match this target; acceptance
    /// rejects mismatched word sizes and byte orders.
    ///
    /// # Errors
    /// Reports invalid IR or a representation this target cannot safely emit.
    fn prepare(&self, program: &Program) -> Result<Program, String> {
        self.prepare_favouring(program, Favour::Speed)
    }

    /// [`Self::prepare`], favouring speed or size where they pull apart.
    ///
    /// # Errors
    /// Reports invalid IR or a representation this target cannot safely emit.
    fn prepare_favouring(&self, program: &Program, favour: Favour) -> Result<Program, String> {
        prepare_counting(self, program, favour, favour == Favour::Speed)
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
        let layout = Layout { word_bits: word };
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
            // A shift by a register is one instruction or nothing: see
            // `ir::expand_shifts`, which preparation runs.
            if let Op::Binary {
                op: crate::ir::Binary::ShiftUp | crate::ir::Binary::ShiftDown,
                ..
            } = *op
                && !self.shifts_by_register()
            {
                return Err(format!("{name} shifts by a known distance only"));
            }
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

/// [`Target::prepare_favouring`], counting claims where they are taken and
/// given up where `counts` says to, and the target has room for it.
fn prepare_counting<T: Target + ?Sized>(
    target: &T,
    program: &Program,
    favour: Favour,
    counts: bool,
) -> Result<Program, String> {
    let speed = favour == Favour::Speed;
    crate::ir::validate(program)?;
    let program = &crate::ir::expand_shifts(program, target.word(), target.shifts_by_register());
    // A number wider than the word becomes words first, which may make
    // more cross a boundary than fits; fitting then packs the rest.
    let program = &crate::ir::split(program, target.word());
    crate::ir::validate(program).map_err(|error| format!("after splitting: {error}"))?;
    let program = &crate::ir::fit(program, target.budget());
    let prepared = crate::ir::legalize(
        program,
        crate::ir::natural::Config {
            word_bits: target.word(),
            // The first arena the heap asks the target for; it grows
            // from there, doubling, as far as the target has room.
            heap_bytes: if target.word() == 16 { 1024 } else { 64 * 1024 },
            grows: true,
            // A 16-bit target runs short of room before it runs short of
            // time, and a call is smaller than the case it saves.
            inline_small: speed && target.word() != 16,
            // Likewise, a count's call is smaller than its common case;
            // a build favouring size counts by calls either way.
            inline_counts: counts && target.word() != 16,
            // A join routine takes six values and answers two.
            join_routines: speed && target.budget().carries(6, 2),
        },
    )?;
    // What legalization wrote -- offsets from known sizes, steps by
    // known strides -- is worked out again with the word's width known.
    let prepared = crate::ir::optimize(&prepared);
    // Each loop then asks whether it is done where it goes round.
    let prepared = crate::ir::rotate(&prepared);
    crate::ir::validate(&prepared).map_err(|error| format!("after rotating loops: {error}"))?;
    target.accepts(&prepared)?;
    Ok(prepared)
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
    program
        .check_layout(layout)
        .map_err(|error| format!("{name}: {error}"))
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
    if matches!(class, Class::Cell | Class::Buffer) {
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

/// Whether an image names its functions. Nothing a program does reads the
/// names, so they are left out unless asked for, and an image without them
/// is as small as it can be.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SymbolTable {
    #[default]
    Omitted,
    Written,
}

/// Write `image` to `output` with `suffix` appended to its name, marked
/// executable where asked, answering the path written.
///
/// # Errors
/// Reports what the filesystem refused.
pub fn write_image(
    output: &Path,
    suffix: &str,
    image: &[u8],
    executable: bool,
) -> io::Result<PathBuf> {
    let mut path = output.as_os_str().to_owned();
    path.push(suffix);
    let path = PathBuf::from(path);
    std::fs::write(&path, image)?;
    #[cfg(unix)]
    if executable {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))?;
    }
    #[cfg(not(unix))]
    let _ = executable;
    Ok(path)
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

        fn emit(&self, _: &Program) -> Vec<u8> {
            Vec::new()
        }
    }

    #[test]
    fn abstract_cells_require_preparation_before_raw_emission() {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            let field = b.constant(Class::Word, 1);
            let word = b.shape(&[Class::Word]);
            b.cell(0, word, &[field]);
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
