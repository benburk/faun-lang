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
mod machine;
mod parallel_copy;
mod selected;
#[cfg(test)]
mod tests;

use faun::ir::{DataId, Program};
use faun::targets::{Artifact, Target};

/// How wide this machine's own word is, which is the widest value it holds
/// and what any class but a fixed one means here.
pub(crate) const WORD_BITS: u16 = 64;

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

    fn provides(&self) -> &'static [&'static str] {
        &["write", "exit!", "grow", "argc!"]
    }

    fn limits(&self, program: &Program) -> Result<(), String> {
        for function in program.functions() {
            let name = program.name(function.name);
            if function.params.len() > 6 {
                return Err(format!(
                    "x86-64-linux function `{name}` has {} parameters; at most 6 are supported",
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

    fn emit(&self, program: &Program) -> Vec<Artifact> {
        let allocated = selected::select_and_allocate(program)
            .expect("accepted machine IR has a valid x86 selected allocation");
        let code = encode::encode(&allocated);
        vec![Artifact {
            extension: "",
            bytes: elf::image(&code, program),
            executable: true,
        }]
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
