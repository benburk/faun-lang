//! [`lower`] turns the IR into instructions but cannot know where the data
//! will sit, so it leaves a [`Reloc`] wherever an address belongs; [`elf`]
//! chooses the layout and fills them in.

mod elf;
mod encode;
mod lower;

use faun::ir::{DataId, Program};
use faun::targets::{Artifact, Target};

/// This target, for whoever is choosing between them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct X86_64Linux;

impl Target for X86_64Linux {
    fn name(&self) -> &'static str {
        "x86_64-linux"
    }

    fn word(&self) -> u16 {
        64
    }

    fn emit(&self, program: &Program) -> Vec<Artifact> {
        vec![Artifact {
            extension: "",
            bytes: elf::image(&lower::lower(program), program),
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
