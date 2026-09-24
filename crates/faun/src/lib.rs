//! The primary Faun frontend, following Ori's source language.
//!
//! Parsing retains compact source spans. Module loading and qualification then
//! produce symbol-based HIR without merging raw ASTs. Checking performs
//! Hindley–Milner inference, nominal receiver-directed method resolution, and
//! contextual literal elaboration. Reachable monomorphic entries can then be
//! specialized, defunctionalized, and lowered to Barb.

use std::path::Path;

use faun_core::targets::Target;

pub mod ast;
mod barb_lower;
pub mod blessed;
pub mod check;
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

pub use modules::ModuleId;
pub use parse::{ParseError, parse, parse_in};
pub use source::{Source, SourceId, Sources};
pub use symbol::{Symbol, Symbols};

/// Return the primary standard package bundled with this frontend crate.
#[must_use]
pub fn standard_path() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/standard/standard.fn"))
}

/// Load and check a Faun program with the standard package and `std.host`.
/// An application is also checked for a `main!` taking the host.
///
/// # Errors
/// Reports loading, resolution or checking errors.
pub fn check(source: &Path, application: bool) -> Result<(), String> {
    let loaded = load(source, application)?;
    if let Some(host) = &loaded.host {
        check::application(&loaded.resolved, &loaded.checked, host).map_err(text)?;
    }
    Ok(())
}

/// Load, check and lower a Faun application for `target`, stopping at Barb
/// before any optimization.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn barb(source: &Path, target: &dyn Target) -> Result<faun_core::barb::Program, String> {
    let loaded = load(source, true)?;
    let host = loaded
        .host
        .ok_or_else(|| "an application is loaded with its host".to_owned())?;
    lower::application(
        &loaded.resolved,
        &loaded.checked,
        &loaded.blessed,
        &host,
        &target.routines(),
    )
    .map_err(text)
}

/// Compile a Faun application to the machine IR `target` compiles.
///
/// # Errors
/// Reports any error [`barb`] does, or what the machine tier cannot represent.
pub fn machine(source: &Path, target: &dyn Target) -> Result<faun_core::ir::Program, String> {
    let mut program = barb(source, target)?;
    faun_core::barb::optimize(&mut program);
    faun_core::machine(&mut program, &target.routines())
}

/// A program loaded, resolved and checked, with its host where it is an
/// application.
struct Loaded {
    resolved: resolve::ResolvedProgram,
    checked: check::CheckedProgram,
    blessed: blessed::PreludeIds,
    host: Option<host::HostIds>,
}

fn load(source: &Path, application: bool) -> Result<Loaded, String> {
    let prelude = standard_path();
    // The host is the same for every target, so any program may import it.
    let host_module = prelude.with_file_name("host.fn");
    let loaded =
        modules::load_with_host(&[source.to_path_buf()], Some(prelude), Some(&host_module))
            .map_err(text)?;
    let blessed = blessed::PreludeIds::resolve(&loaded).map_err(text)?;
    let host = application
        .then(|| host::HostIds::resolve(&loaded, &blessed))
        .transpose()
        .map_err(text)?;
    let resolved = resolve::resolve(loaded).map_err(text)?;
    let checked = check::program(&resolved, &blessed).map_err(text)?;
    Ok(Loaded {
        resolved,
        checked,
        blessed,
        host,
    })
}

fn text(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[cfg(test)]
mod tests;
