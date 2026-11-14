//! `selected` flattens machine-IR regions into a verified target-local SSA
//! CFG. Its allocator computes segmented liveness, splits around constraints
//! and clobbers, plans transfers through `parallel_copy`, and lowers a fully
//! verified symbolic `machine::Allocated` sequence. Allowed-register sets
//! separate integer and scalar XMM operands; copies and spills preserve their
//! low-word bit patterns across banks. `encode` alone lays that sequence out
//! as bytes. Data addresses remain `Reloc`s until `elf` chooses
//! the image layout and fills them in.
//!
//! The lab takes the same optimized Barb as the stock backend. It shares portable
//! lowering and representation passes with the other lab targets and keeps
//! its own machine IR, instruction selection, register allocator and ELF emitter.

mod barb;
pub use faun_core::{facts, float, index};
pub mod ir;
pub mod platform;
#[cfg(test)]
#[path = "../../core/src/programs.rs"]
pub mod programs;
pub mod targets;

#[cfg(test)]
#[path = "../../core/tests/support/runtime_lifetimes.rs"]
mod lifetime_fixture;

mod elf;
mod encode;
mod jumps;
mod machine;
mod parallel_copy;
mod selected;
#[cfg(test)]
mod tests;

use std::io;
use std::path::{Path, PathBuf};

use crate::ir::{DataId, FunctionId, Program};
use crate::targets::{Favour, SymbolTable, Target, write_image};

/// How wide this machine's own word is, which is the widest value it holds
/// and what any class but a fixed one means here.
pub(crate) const WORD_BITS: u16 = 64;

/// Parameters a call passes, one per System V integer argument register.
const ARG_COUNT: usize = 6;

/// This target, for whoever is choosing between them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct X86_64Linux;

impl Target for X86_64Linux {
    fn name(&self) -> &'static str {
        "x86_64-linux"
    }

    fn word(&self) -> u16 {
        WORD_BITS
    }

    /// SSE2 is part of x86-64: every processor it runs on has scalar
    /// binary32 and binary64 arithmetic, correctly rounded to nearest-even
    /// with exceptions masked, as the control word is when a process starts.
    fn floats(&self) -> bool {
        true
    }

    fn provides(&self) -> &'static [&'static str] {
        &[
            "fd_put!",
            "fd_read!",
            "fd_open!",
            "fd_close!",
            "exit!",
            "write_fd!",
            "read_fd!",
            "open_at!",
            "write!",
            "read_byte!",
            "grow",
            "argc",
            "argv",
        ]
    }

    fn shifts_by_register(&self) -> bool {
        true
    }

    fn limits(&self, program: &Program) -> Result<(), String> {
        let entry = program.entry();
        // Each entry parameter is a startup value: the count, then where the
        // arguments' addresses lie.
        for (at, name) in program.parameter_names(entry).enumerate() {
            if [(0, "argc"), (1, "argv")].contains(&(at, name)) {
                continue;
            }
            {
                return Err(format!(
                    "x86-64-linux cannot supply entry parameter {at} `{name}`"
                ));
            }
        }
        Ok(())
    }

    fn emit(&self, program: &Program) -> Vec<u8> {
        self.emit_with(program, Favour::Speed, SymbolTable::Omitted)
    }

    fn emit_with(&self, program: &Program, favour: Favour, symbols: SymbolTable) -> Vec<u8> {
        // A program written with its symbols is one to profile, so each
        // function keeps a frame pointer a profiler can walk the stack by.
        let frame_pointers = symbols == SymbolTable::Written;
        let allocated = selected::select_and_allocate_favouring(program, favour, frame_pointers)
            .expect("accepted machine IR has a valid x86 selected allocation");
        let code = encode::encode(&allocated);
        elf::image(&code, program, symbols)
    }

    /// An executable named `output`.
    fn write(&self, image: &[u8], output: &Path) -> io::Result<PathBuf> {
        write_image(output, "", image, true)
    }
}

/// Machine code whose data addresses are not resolved yet.
struct Code {
    bytes: Vec<u8>,
    relocs: Vec<Reloc>,
    /// Each function and where in `bytes` its code starts, in order.
    functions: Vec<(FunctionId, usize)>,
}

struct Reloc {
    offset: usize,
    data: DataId,
}

/// Lower a validated Barb program to machine IR and run the machine
/// optimization passes: the middle stage of compiling, between a frontend's
/// Barb and a target's image.
///
/// # Errors
///
/// Names what the machine tier cannot represent.
pub fn lower_to_machine_ir(
    program: &barb::Program,
    routines: &platform::Routines,
) -> Result<Program, String> {
    let held = ir::lower(program, routines)?;
    ir::validate(&held)?;
    let optimized = ir::optimize(&held);
    // A program that reads only how many arguments it has keeps no call
    // making them a list, and is lowered again without one, so that what
    // it holds is what it would have held counting them.
    let made = optimized
        .functions()
        .iter()
        .position(|function| optimized.name(function.name) == ir::MAKE_ARGUMENTS);
    if let Some(made) = made
        && !optimized.calls(FunctionId::at(made))
    {
        let counted = ir::lower_counting_arguments(program, routines)?;
        ir::validate(&counted)?;
        return Ok(ir::optimize(&counted));
    }
    Ok(optimized)
}

/// Compile shared, optimized Barb through the experimental x86 pipeline.
///
/// # Errors
/// Reports invalid Barb or a program the machine cannot represent.
pub fn compile(
    barb: &barb::Program,
    favour: Favour,
    symbols: SymbolTable,
) -> Result<Vec<u8>, String> {
    let machine = lower_to_machine_ir(barb, &X86_64Linux.routines())?;
    X86_64Linux.compile_machine_ir_with(&machine, favour, symbols)
}
