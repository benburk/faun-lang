//! Select the backend independently of the source program's target host.

use faun::diagnostic::Diagnostic;
use faun_core::barb;
use faun_core::targets::{Favour, SymbolTable, Target};
use faun_x86_64_linux::X86_64Linux;

use crate::args::Stage;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Compiler {
    Stock(&'static dyn Target),
    X86Lab,
}

impl Compiler {
    pub(crate) fn choose(target: &'static dyn Target, backend: &str) -> Result<Self, String> {
        match backend {
            "stock" => Ok(Self::Stock(target)),
            "x86-lab" if target.name() == X86_64Linux.name() => Ok(Self::X86Lab),
            "x86-lab" => Err(format!(
                "the x86-lab backend cannot compile for {}",
                target.name()
            )),
            _ => Err(format!(
                "unknown backend `{backend}`, expected stock or x86-lab"
            )),
        }
    }

    pub(crate) const fn host(self) -> &'static dyn Target {
        match self {
            Self::Stock(target) => target,
            Self::X86Lab => &X86_64Linux,
        }
    }

    pub(crate) fn compile(
        self,
        program: barb::Program,
        favour: Favour,
        symbols: SymbolTable,
    ) -> Result<Vec<u8>, Diagnostic> {
        match self {
            Self::Stock(target) => {
                faun::compile_barb_to_image_with(program, target, favour, symbols)
            }
            Self::X86Lab => {
                let program = faun::optimize_application(program)?;
                faun_x86_lab::compile(&program, favour, symbols).map_err(Diagnostic::new)
            }
        }
    }

    pub(crate) fn render(self, stage: Stage, program: &barb::Program) -> Result<String, String> {
        if matches!(stage, Stage::Barb) {
            return Ok(program.render_analyzed(&program.analyze()));
        }
        match self {
            Self::Stock(target) => {
                let machine = faun_core::lower_to_machine_ir(program, &target.routines())?;
                match stage {
                    Stage::Target => Ok(target.render(&target.prepare(&machine)?)),
                    _ => Ok(machine.render()),
                }
            }
            Self::X86Lab => {
                use faun_x86_lab::{X86_64Linux as Lab, targets::Target as _};
                let machine = faun_x86_lab::lower_to_machine_ir(program, &Lab.routines())?;
                match stage {
                    Stage::Target => Ok(Lab.render(&Lab.prepare(&machine)?)),
                    _ => Ok(machine.render()),
                }
            }
        }
    }
}
