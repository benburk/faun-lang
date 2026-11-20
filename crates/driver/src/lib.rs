//! The Faun compiler's one line, sequenced in one place.
//!
//! ```text
//! source → faun-frontend → Barb → barb::optimize → faun-core → machine IR → target → image
//! ```
//!
//! Each tier is a crate that does its one job and knows nothing of the
//! next: the frontend reads a target only as a [`Platform`], Barb knows no
//! target at all, and the machine tier and the targets never see source.
//! What joins them is here. [`platform`] says what the frontend reads of a
//! target, [`machine_ir`] lowers optimized Barb for one, and
//! [`compile_barb`] takes an application's Barb all the way to its image.
//!
//! Which targets exist, and which back end compiles for one, is the
//! command's to say: this crate depends on no target, so a target's own
//! tests can run the whole line with it.

use faun_core::ir;
use faun_core::platform::Routines;
use faun_core::targets::{Favour, Pipeline, SymbolTable, Target};
use faun_frontend::Diagnostic;
use faun_frontend::platform::{Platform, Routine};

/// What the frontend reads of `target`: its name, which names its host
/// module, and every routine it answers for, with whether each uses up
/// what it is handed.
#[must_use]
pub fn platform(target: &dyn Target) -> Platform {
    platform_for(target.name(), &target.routines())
}

/// The target named `name` answering for `routines`, as the frontend reads
/// it.
fn platform_for(name: &str, routines: &Routines) -> Platform {
    Platform::new(
        name,
        routines.all().map(|routine| Routine {
            name: routine.name.clone(),
            consumes: routine.consumes,
        }),
    )
}

/// Lower optimized Barb to the machine IR `target` compiles, by
/// `pipeline`'s passes.
///
/// # Errors
/// Names what the machine tier cannot represent.
pub fn machine_ir(
    barb: &barb::Program,
    target: &dyn Target,
    pipeline: Pipeline,
) -> Result<ir::Program, String> {
    faun_core::lower_with_pipeline(barb, &target.routines(), pipeline)
}

/// Compile an application's Barb to `target`'s image: optimize it, lower
/// it to machine IR by `pipeline`'s passes, and let the target compile
/// that.
///
/// The image favours speed or size where they pull apart, as `favour`
/// says, with symbols naming each function where `symbols` asks and the
/// target writes them.
///
/// # Errors
/// Reports what the machine tier or the target cannot represent.
pub fn compile_barb(
    barb: barb::Program,
    target: &dyn Target,
    pipeline: Pipeline,
    favour: Favour,
    symbols: SymbolTable,
) -> Result<Vec<u8>, Diagnostic> {
    let mut barb = barb;
    barb::optimize(&mut barb);
    let machine = machine_ir(&barb, target, pipeline).map_err(Diagnostic::new)?;
    target
        .compile_with_pipeline(&machine, favour, symbols, pipeline)
        .map_err(Diagnostic::new)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn lowers_the_host_entry_through_the_machine_boundary() {
        let entry = Path::new(env!("CARGO_MANIFEST_DIR")).join("../frontend/examples/main.fn");
        let platform = platform_for("x86_64-linux", &Routines::builtin());
        let mut program = faun_frontend::lower_to_barb(&entry, &platform).unwrap();
        barb::optimize(&mut program);
        for bits in [16, 32, 64] {
            let routines = Routines::builtin().with_word(bits);
            let machine = faun_core::lower_to_machine_ir(&program, &routines).unwrap();
            // A program reading only how many arguments it has is handed
            // `argc` alone, into the entry's frame, as wide as its word.
            let entry = machine.entry();
            assert_eq!(machine.parameter_names(entry).collect::<Vec<_>>(), ["argc"]);
            let body = machine.function(entry).body().unwrap();
            let argc = machine.values(machine.region(body).params)[0];
            assert_eq!(machine.class(argc), ir::Class::fixed(bits));
            // A status is a byte, so the count is taken modulo 256 where the
            // program says so, rather than by whatever the target keeps.
            let rendered = machine.render();
            assert!(rendered.contains("= convert v0 to 0..255"), "{rendered}");
            assert!(rendered.contains("call exit!(v1)"), "{rendered}");
        }
    }
}
