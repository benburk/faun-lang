//! The Faun compiler as a library.
//!
//! [`lower()`] takes an application's source to Barb, which is what checking
//! it means, and [`compile()`] takes it on to a target's image. Any
//! [`Target`] will do; which targets exist is the command line's to say.
//!
//! [`lower()`] runs the frontend passes in order. Parsing retains compact
//! source spans. Module loading and qualification then produce symbol-based
//! HIR without merging raw ASTs. Checking performs Hindley–Milner inference,
//! nominal receiver-directed method resolution, and contextual literal
//! elaboration. The entry's reachable functions are then specialized,
//! defunctionalized, and lowered to Barb. [`compile()`] hands that Barb to
//! `faun_core` for the machine tier and to the target for its image.

use std::path::{Path, PathBuf};

use faun_core::barb;
use faun_core::targets::Target;

pub mod ast;
mod barb_lower;
pub mod blessed;
pub mod check;
mod defunctionalize;
pub mod diagnostic;
mod grammar;
pub mod hir;
pub mod host;
pub mod lex;
pub mod literal;
pub mod lower;
pub mod modules;
mod parse;
pub mod resolve;
pub mod source;
mod specialize;
pub mod symbol;

pub use diagnostic::Diagnostic;
pub use modules::ModuleId;
pub use parse::{ParseError, parse, parse_in};
pub use source::{Source, SourceId, Sources};
pub use symbol::{Symbol, Symbols};

/// Return the primary standard package bundled with this frontend crate.
#[must_use]
pub fn standard_path() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/standard/standard.fn"))
}

/// Compile the Faun application at `source` to `target`'s image: lower it to
/// Barb, optimize that, lower it to machine IR, and let the target compile it.
///
/// # Errors
/// Reports the first stage that refuses the program.
pub fn compile(source: &Path, target: &dyn Target) -> Result<Vec<u8>, Diagnostic> {
    let mut barb = lower(source, target)?;
    barb::optimize(&mut barb);
    let machine = faun_core::to_machine(&mut barb, &target.routines()).map_err(Diagnostic::new)?;
    target.compile(&machine).map_err(Diagnostic::new)
}

/// Lower the Faun application at `source` to Barb for `target`, before any
/// optimization.
///
/// Reaching Barb is what checking a program means: it meets `target`'s host
/// module and every routine it asks for exists.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn lower(source: &Path, target: &dyn Target) -> Result<barb::Program, Diagnostic> {
    let loaded = modules::load_with_host(source, standard_path(), &host_path(target)?)?;
    let prelude = blessed::PreludeIds::resolve(&loaded).map_err(|e| Diagnostic::new(e.message))?;
    let host = host::HostIds::resolve(&loaded)?;
    let resolved = resolve::resolve(loaded)?;
    let checked = check::program(resolved, prelude)?;
    check::application(&checked, &host)?;
    let specialized =
        specialize::application(&checked, &host).map_err(|e| Diagnostic::new(e.message))?;
    let first_order = defunctionalize::defunctionalize(specialized);
    barb_lower::application(&checked, first_order, &target.routines())
        .map_err(|e| Diagnostic::new(e.message))
}

/// The host module mounted at `std.host` for `target`.
fn host_path(target: &dyn Target) -> Result<PathBuf, Diagnostic> {
    let path = standard_path().with_file_name(format!("hosts/{}.fn", target.name()));
    if !path.is_file() {
        return Err(Diagnostic::new(format!(
            "no Faun host module for target `{}`",
            target.name()
        )));
    }
    Ok(path)
}

#[cfg(test)]
mod tests;
