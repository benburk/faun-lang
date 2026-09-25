//! The Faun compiler as a library.
//!
//! [`lower_to_barb`] checks a package against a target's host and lowers
//! it to Barb, which is what checking it means. An entry that defines `main!`
//! makes it an application, whose Barb starts there; one that does not is a
//! library, whose Barb has no entry. [`compile_barb_to_image`] takes an
//! application's Barb on to a target's image. [`lower_tests_to_barb`] lowers
//! a package whose entry asks its `expect`s instead. Any [`Target`] will do;
//! which targets exist is the command line's to say.
//!
//! [`lower_to_barb`] runs the frontend passes in order. Parsing retains compact
//! source spans. Module loading and qualification then produce symbol-based
//! HIR without merging raw ASTs. Checking performs Hindley–Milner inference,
//! nominal receiver-directed method resolution, and contextual literal
//! elaboration. The package's functions are then specialized, each taking a
//! function once for every set of callbacks it is handed, and lowered to
//! Barb. [`compile_barb_to_image`] hands that Barb to
//! `faun_core` for the machine tier and to the target for its image.

use std::path::{Path, PathBuf};

use faun_core::barb;
use faun_core::targets::Target;

pub mod ast;
mod barb_lower;
pub mod blessed;
mod callbacks;
pub mod check;
mod defunctionalize;
pub mod diagnostic;
mod exhaustive;
mod expectations;
mod grammar;
pub mod hir;
pub mod host;
pub mod lex;
pub mod literal;
pub mod lower;
pub mod modules;
mod parse;
pub mod resolve;
mod second_class;
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

/// Check the Faun package at `source` against `target`'s host and lower it
/// to Barb, before any optimization.
///
/// Every definition the package writes that can stand on its own is lowered
/// and checked, whether or not anything calls it, and so is every `expect`.
/// The entry defining `main!` makes it an application, whose Barb starts
/// there; without one it is a library, whose Barb has no entry and so
/// nothing to build.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn lower_to_barb(source: &Path, target: &dyn Target) -> Result<barb::Program, Diagnostic> {
    let loaded = modules::load_program(source, standard_path(), &host_path(target)?)?;
    let (prelude, host) = identities(&loaded)?;
    let main = host::Main::find_in(&loaded)?;
    let mut resolved = resolve::resolve_names(loaded)?;
    if let Some(main) = &main {
        host::sign_main(&mut resolved, &host, main);
    }
    lower_resolved(resolved, prelude, &host, main.as_ref(), target)
}

/// A package's expectations, built to be run.
#[derive(Debug)]
pub struct Tests {
    /// An application whose `main!` prints the number of each expectation
    /// that does not hold, each followed by a space, and exits with status
    /// nought.
    pub barb: barb::Program,
    /// Where each expectation was written, the first numbered one.
    pub expectations: Vec<diagnostic::Location>,
}

/// Check the Faun package at `source` as [`lower_to_barb`] does, and lower it
/// to Barb whose entry asks every `expect` in the package.
///
/// The entry takes the place of the package's `main!`, if it has one, which
/// is checked all the same.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn lower_tests_to_barb(source: &Path, target: &dyn Target) -> Result<Tests, Diagnostic> {
    let mut loaded = modules::load_program(source, standard_path(), &host_path(target)?)?;
    let (prelude, host) = identities(&loaded)?;
    let application = host::Main::find_in(&loaded)?;
    let main = expectations::main(&mut loaded);
    let mut resolved = resolve::resolve_names(loaded)?;
    if let Some(application) = &application {
        host::sign_main(&mut resolved, &host, application);
    }
    let expectations = expectations::enter(&mut resolved, &host, &main);
    let barb = lower_resolved(resolved, prelude, &host, Some(&main), target)?;
    Ok(Tests { barb, expectations })
}

fn identities(
    loaded: &modules::LoadedProgram,
) -> Result<(blessed::PreludeIds, host::HostIds), Diagnostic> {
    let prelude = blessed::PreludeIds::find_in(loaded).map_err(|e| Diagnostic::new(e.message))?;
    Ok((prelude, host::HostIds::find_in(loaded)?))
}

/// Check a resolved package and lower it to Barb, entering by `main`.
fn lower_resolved(
    resolved: resolve::ResolvedProgram,
    prelude: blessed::PreludeIds,
    host: &host::HostIds,
    main: Option<&host::Main>,
    target: &dyn Target,
) -> Result<barb::Program, Diagnostic> {
    let checked = check::type_check(resolved, prelude)?;
    if let Some(main) = main {
        check::check_application_abi(&checked, host, main)?;
    }
    let specialized =
        specialize::monomorphize_package(&checked, host, main).map_err(|e| match e.at {
            Some((module, span)) => checked.resolved.diagnostic(module, span, e.message),
            None => Diagnostic::new(e.message),
        })?;
    let first_order = defunctionalize::defunctionalize(specialized);
    barb_lower::lower_package_to_barb(&checked, first_order, &target.routines())
}

/// Compile the Faun application at `source` to `target`'s image.
///
/// # Errors
/// Reports the first stage that refuses the program.
pub fn compile_to_image(source: &Path, target: &dyn Target) -> Result<Vec<u8>, Diagnostic> {
    compile_barb_to_image(lower_to_barb(source, target)?, target)
}

/// Compile an application's Barb to `target`'s image: optimize it, lower it
/// to machine IR, and let the target compile that.
///
/// # Errors
/// Reports a library, which has no `main!` to build, and what the machine
/// tier or the target cannot represent.
pub fn compile_barb_to_image(
    mut barb: barb::Program,
    target: &dyn Target,
) -> Result<Vec<u8>, Diagnostic> {
    if barb.entry().is_none() {
        return Err(Diagnostic::new("a library has no `main!` to build")
            .help("write `main! : Host -> []` and a clause `main!(host) -> ...`"));
    }
    barb::optimize(&mut barb);
    let machine =
        faun_core::lower_to_machine_ir(&mut barb, &target.routines()).map_err(Diagnostic::new)?;
    target.compile_machine_ir(&machine).map_err(Diagnostic::new)
}

/// The x86-64 Linux host, which frontend tests load their programs with.
#[cfg(test)]
fn test_host() -> PathBuf {
    standard_path().with_file_name("hosts/x86_64-linux.fn")
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
