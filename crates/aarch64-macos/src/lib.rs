//! `AArch64` machine code in a self-signed Mach-O image for macOS.
//!
//! The image names dyld because modern macOS does not launch static Mach-O
//! executables, but imports no symbols and links no libraries. `write` and
//! `exit!` enter the kernel directly with `svc #0x80`.
//!
//! This first slice deliberately accepts only the baseline needed for
//! returning or exiting with a constant, exiting with `argc`, and writing
//! static data. Unsupported machine IR is rejected before emission.

mod encode;
mod lower;
mod macho;

use faun_core::ir::Program;
use faun_core::targets::{Artifact, Target};

pub(crate) const WORD_BITS: u16 = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Aarch64Macos;

impl Target for Aarch64Macos {
    fn name(&self) -> &'static str {
        "aarch64-macos"
    }

    fn word(&self) -> u16 {
        WORD_BITS
    }

    fn provides(&self) -> &'static [&'static str] {
        &["write!", "exit!", "argc!"]
    }

    fn limits(&self, program: &Program) -> Result<(), String> {
        lower::check(program)?;
        macho::check_size(&lower::lower(program), program)
    }

    fn emit(&self, program: &Program) -> Vec<Artifact> {
        vec![Artifact {
            extension: "",
            bytes: macho::image(&lower::lower(program), program),
            executable: true,
        }]
    }
}

struct Code {
    words: Vec<u32>,
    relocs: Vec<encode::Reloc>,
}

#[cfg(test)]
mod tests {
    use faun_core::ir::Class;
    use faun_core::programs;
    use faun_core::targets::Target;

    use super::*;

    fn exits_with_host() -> Program {
        let (mut program, main) = Program::new_with_params("main", &[("host", Class::Word)]);
        let exit = Aarch64Macos.routines().declare(&mut program, "exit!");
        program.define(main, |b, params| {
            b.call(exit, &[params[0]]);
        });
        program
    }

    fn emitted_words(program: &Program, count: usize) -> Vec<u32> {
        let artifact = Aarch64Macos.compile(program).unwrap().remove(0);
        assert!(artifact.executable);
        artifact.bytes[macho::CODE_OFFSET..][..count * 4]
            .chunks_exact(4)
            .map(|word| u32::from_le_bytes(word.try_into().unwrap()))
            .collect()
    }

    #[test]
    fn compiles_the_three_initial_baselines() {
        assert_eq!(
            emitted_words(&programs::empty(), 3),
            [0xD280_0000, 0xD280_0030, 0xD400_1001]
        );
        assert_eq!(
            emitted_words(&exits_with_host(), 4),
            [0xAA00_03F3, 0xAA13_03E0, 0xD280_0030, 0xD400_1001]
        );
        assert_eq!(
            emitted_words(&programs::hello_world(), 8),
            [
                0xD280_0020,
                0x1000_00E1,
                0xD280_01C2,
                0xD280_0090,
                0xD400_1001,
                0xD280_0000,
                0xD280_0030,
                0xD400_1001,
            ]
        );
    }

    #[test]
    fn unsupported_ir_is_refused_before_emission() {
        let error = Aarch64Macos.compile(&programs::two_and_two()).unwrap_err();
        assert!(error.contains("does not yet support"), "{error}");
    }
}
