//! `selected` flattens machine-IR regions into a verified target-local SSA
//! CFG. Its allocator computes segmented liveness, splits around constraints
//! and clobbers, plans transfers through `parallel_copy`, and lowers a fully
//! verified symbolic `machine::Allocated` sequence. `encode` alone lays that
//! sequence out as bytes. Data addresses remain `Reloc`s until `elf` chooses
//! the image layout and fills them in.

#[cfg(test)]
mod abi_tests;
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

use faun_core::ir::{Budget, DataId, Program};
use faun_core::targets::{Target, write_image};

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

    fn budget(&self) -> Budget {
        Budget::new(ARG_COUNT, 1, usize::MAX)
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
        for function in program.functions() {
            let name = program.name(function.name);
            if function.params.len() > ARG_COUNT {
                return Err(format!(
                    "x86-64-linux function `{name}` has {} parameters; at most {ARG_COUNT} are supported",
                    function.params.len()
                ));
            }
            if function.returns.classes().len() > 1 {
                return Err(format!(
                    "x86-64-linux function `{name}` has {} results; at most 1 is supported",
                    function.returns.classes().len()
                ));
            }
        }
        Ok(())
    }

    fn emit(&self, program: &Program) -> Vec<u8> {
        let allocated = selected::select_and_allocate(program)
            .expect("accepted machine IR has a valid x86 selected allocation");
        let code = encode::encode(&allocated);
        elf::image(&code, program)
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
}

struct Reloc {
    offset: usize,
    data: DataId,
}
