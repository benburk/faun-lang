//! Select the backend independently of the source program's target host.
//!
//! Every backend compiles by `faun_driver`'s line. On x86-64 Linux there
//! are two emitters: the stock one and x86-lab's.

use faun_core::targets::{Favour, SymbolTable, Target};
use faun_frontend::diagnostic::Diagnostic;
use faun_x86_64_linux::X86_64Linux;

use crate::args::Stage;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Compiler(&'static dyn Target);

impl Compiler {
    pub(crate) fn choose(target: &'static dyn Target, backend: &str) -> Result<Self, String> {
        let x86 = target.name() == X86_64Linux.name();
        match backend {
            "lab" | "x86-lab" if x86 => Ok(Self(&faun_x86_lab::X86_64Linux)),
            "stock" | "lab" => Ok(Self(target)),
            "x86-lab" => Err(format!(
                "the x86-lab backend cannot compile for {}",
                target.name()
            )),
            _ => Err(format!(
                "unknown backend `{backend}`, expected stock, lab or x86-lab"
            )),
        }
    }

    pub(crate) const fn host(self) -> &'static dyn Target {
        self.0
    }

    /// The target whose host the program is checked against, as the
    /// frontend reads it.
    pub(crate) fn platform(self) -> faun_frontend::Platform {
        faun_driver::platform(self.host())
    }

    pub(crate) fn compile(
        self,
        program: barb::Program,
        favour: Favour,
        symbols: SymbolTable,
    ) -> Result<Vec<u8>, Diagnostic> {
        faun_driver::compile_barb(program, self.0, favour, symbols)
    }

    pub(crate) fn render(self, stage: Stage, program: &barb::Program) -> Result<String, String> {
        if matches!(stage, Stage::Barb) {
            return Ok(program.render_analyzed(&program.analyze()));
        }
        let machine = faun_driver::machine_ir(program, self.0)?;
        match stage {
            Stage::Target => Ok(self.0.render(&self.0.prepare(&machine)?)),
            _ => Ok(machine.render()),
        }
    }
}
