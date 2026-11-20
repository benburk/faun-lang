//! Compile for the chosen target by `faun_driver`'s line.

use faun_core::targets::{Favour, SymbolTable, Target};
use faun_frontend::diagnostic::Diagnostic;

use crate::args::Stage;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Compiler(&'static dyn Target);

impl Compiler {
    /// The target, and the backend a command line names for it: every
    /// target has one, which `lab` and `x86-lab` still name
    /// for a script written when there were two.
    pub(crate) fn choose(
        target: &'static dyn Target,
        backend: Option<&str>,
    ) -> Result<Self, String> {
        match backend {
            None | Some("lab" | "x86-lab") => Ok(Self(target)),
            Some("stock") => Err(String::from(
                "the stock backend is gone: every target has one backend, so leave out --backend",
            )),
            Some(backend) => Err(format!(
                "unknown backend `{backend}`: every target has one backend, so leave out --backend"
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
