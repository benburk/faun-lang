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

/// The host module mounted at `std.host` for `target`.
fn host_path(target: &dyn Target) -> PathBuf {
    standard_path().with_file_name(format!("hosts/{}.fn", target.name()))
}

/// Lower a Faun application to Barb for `target`: load it, check it, and
/// lower it, before any optimization.
///
/// Reaching Barb is what checking a program means: it meets `target`'s host
/// module and every routine it asks for exists.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn lower(source: &Path, target: &dyn Target) -> Result<faun_core::barb::Program, Diagnostic> {
    let loaded = load(source, target)?;
    lower::application(
        &loaded.resolved,
        &loaded.checked,
        &loaded.blessed,
        &loaded.host,
        &target.routines(),
    )
    .map_err(|error| Diagnostic::new(error.message))
}

/// An application loaded, resolved and checked against its target's host.
struct Loaded {
    resolved: resolve::ResolvedProgram,
    checked: check::CheckedProgram,
    blessed: blessed::PreludeIds,
    host: host::HostIds,
}

fn load(source: &Path, target: &dyn Target) -> Result<Loaded, Diagnostic> {
    let prelude = standard_path();
    let host_module = host_path(target);
    if !host_module.is_file() {
        return Err(Diagnostic::new(format!(
            "no Faun host module for target `{}`",
            target.name()
        )));
    }
    let loaded =
        modules::load_with_host(&[source.to_path_buf()], Some(prelude), Some(&host_module))?;
    let blessed =
        blessed::PreludeIds::resolve(&loaded).map_err(|error| Diagnostic::new(error.message))?;
    let host = host::HostIds::resolve(&loaded, &blessed)?;
    let resolved = resolve::resolve(loaded)?;
    let placed =
        |error: check::CheckError| resolved.diagnostic(error.module, error.span, error.message);
    let checked = check::program(&resolved, &blessed).map_err(placed)?;
    check::application(&resolved, &checked, &host).map_err(placed)?;
    Ok(Loaded {
        resolved,
        checked,
        blessed,
        host,
    })
}

#[cfg(test)]
mod tests;
