//! The primary Faun frontend, following Ori's source language.
//!
//! Parsing retains compact source spans. Module loading and qualification then
//! produce symbol-based HIR without merging raw ASTs. Checking performs
//! Hindley–Milner inference, nominal receiver-directed method resolution, and
//! contextual literal elaboration. Reachable monomorphic entries can then be
//! specialized, defunctionalized, and lowered to Barb.

use std::path::{Path, PathBuf};

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

/// The host module mounted at `std.host` for `target`.
fn host_path(target: &dyn Target) -> PathBuf {
    standard_path().with_file_name(format!("hosts/{}.fn", target.name()))
}

/// Load, check and lower a Faun application for `target`, stopping at Barb
/// before any optimization.
///
/// Reaching Barb is what checking a program means: it meets `target`'s host
/// module and every routine it asks for exists.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn barb(source: &Path, target: &dyn Target) -> Result<faun_core::barb::Program, String> {
    let loaded = load(source, target)?;
    lower::application(
        &loaded.resolved,
        &loaded.checked,
        &loaded.blessed,
        &loaded.host,
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

/// An application loaded, resolved and checked against its target's host.
struct Loaded {
    resolved: resolve::ResolvedProgram,
    checked: check::CheckedProgram,
    blessed: blessed::PreludeIds,
    host: host::HostIds,
}

fn load(source: &Path, target: &dyn Target) -> Result<Loaded, String> {
    let prelude = standard_path();
    let host_module = host_path(target);
    if !host_module.is_file() {
        return Err(format!(
            "no Faun host module for target `{}`",
            target.name()
        ));
    }
    let loaded =
        modules::load_with_host(&[source.to_path_buf()], Some(prelude), Some(&host_module))
            .map_err(text)?;
    let blessed = blessed::PreludeIds::resolve(&loaded).map_err(text)?;
    let host = host::HostIds::resolve(&loaded, &blessed).map_err(text)?;
    let resolved = resolve::resolve(loaded).map_err(text)?;
    let checked = check::program(&resolved, &blessed).map_err(text)?;
    check::application(&resolved, &checked, &host).map_err(text)?;
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
