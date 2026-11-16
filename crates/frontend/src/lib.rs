//! The Faun compiler as a library.
//!
//! [`check_package`] checks a package against a target's host. An entry that
//! defines `main!` makes it an application, lowered to Barb starting there;
//! one that does not is a library, which the frontend's checks are all of.
//! [`lower_to_barb`] is the same for an application alone, and
//! [`compile_barb_to_image`] takes an application's Barb on to a target's
//! image. [`lower_tests_to_barb`] lowers a package whose entry asks its
//! `expect`s instead. Any [`Target`] will do;
//! which targets exist is the command line's to say.
//!
//! The frontend is a line of stages, each taking the program as one tree and
//! answering the next, beside a [`Context`] holding what the trees point
//! into: source text, symbols, and the standard and host identities.
//! [`lower_to_barb`] and [`lower_tests_to_barb`] write the line out, and
//! differ only in their entry:
//!
//! 1. Loading reads each module's syntax, with compact source spans.
//! 2. [`resolve()`] names every global and local, as HIR.
//! 3. [`checked()`] groups each function's signature and clauses, writes the
//!    members a type asks for, infers types (Hindley–Milner, with
//!    receiver-directed methods and literal elaboration) and checks that
//!    patterns cover what they take apart, as typed HIR.
//! 4. Specialization makes each definition concrete at the types it is used
//!    at; functions are then checked to be second class.
//! 5. Callback lowering makes a definition for each set of callbacks, so no
//!    value is a function; resources are then checked to be used up once.
//! 6. Pattern compilation turns clauses into decisions and bindings into
//!    ordered unpacks, which Barb emission reads.
//!
//! [`compile_barb_to_image`] hands Barb to `faun_core` for the machine tier
//! and to the target for its image.

use std::path::{Path, PathBuf};

use faun_core::barb;
use faun_core::targets::{Favour, SymbolTable, Target};

use context::Context;
use host::Main;
use modules::LoadedProgram;
use packages::Packages;

pub mod ast;
mod barb_lower;
pub mod blessed;
mod builders;
mod callbacks;
pub mod check;
pub mod context;
pub mod declarations;
mod derive;
pub mod diagnostic;
#[cfg(test)]
mod ebnf;
mod exhaustive;
mod expectations;
mod first_order;
mod grammar;
pub mod hir;
pub mod host;
pub mod lex;
mod linearity;
mod lines;
pub mod literal;
pub mod modules;
pub mod packages;
mod parse;
mod pattern_compile;
pub mod resolve;
mod second_class;
pub mod source;
mod specialize;
mod standard;
pub mod symbol;
mod test_uses;
pub mod typed;

pub use diagnostic::Diagnostic;
pub use modules::ModuleId;
pub use parse::{ParseError, parse, parse_in};
pub use source::{Source, SourceId, Sources};
pub use symbol::{Symbol, Symbols};

/// The primary standard package's root module: built into the compiler,
/// or read from the directory `FAUN_STD` names where it is set.
#[must_use]
pub fn standard_path() -> &'static Path {
    standard::root_module()
}

/// A checked package.
#[derive(Debug)]
pub enum Package {
    /// A package with no `main!`. The frontend's checks are all a library
    /// has: nothing enters it, so it has no Barb.
    Library,
    /// A package whose entry defines `main!`, and its Barb, before any
    /// optimization, starting there.
    Application(Box<barb::Program>),
}

/// Check the Faun package at `source` against `target`'s host, and lower it
/// to Barb where it is an application.
///
/// Every definition the package writes that can stand on its own is
/// checked, whether or not anything calls it, and so is every `expect`.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn check_package(source: &Path, target: &dyn Target) -> Result<Package, Diagnostic> {
    check_package_using(source, target, &Packages::default())
}

/// [`check_package`], reading each URL dependency from where `packages`
/// says.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn check_package_using(
    source: &Path,
    target: &dyn Target,
    packages: &Packages,
) -> Result<Package, Diagnostic> {
    let loaded = load(source, target, packages)?;
    let main = Main::find_in(&loaded)?;
    let facts = test_uses::Facts::of(&loaded);
    let (program, cx) = resolve(loaded)?;
    test_uses::check(&program, &cx, &facts)?;
    let program = host::sign_main(program, &cx, main.as_ref());
    lower(program, cx, main.as_ref(), target)
}

/// Check the Faun application at `source` against `target`'s host and lower
/// it to Barb, before any optimization.
///
/// # Errors
/// Reports a library, which has no `main!` to lower, and loading,
/// resolution, checking or lowering errors.
pub fn lower_to_barb(source: &Path, target: &dyn Target) -> Result<barb::Program, Diagnostic> {
    lower_to_barb_using(source, target, &Packages::default())
}

/// [`lower_to_barb`], reading each URL dependency from where `packages`
/// says.
///
/// # Errors
/// Reports a library, which has no `main!` to lower, and loading,
/// resolution, checking or lowering errors.
pub fn lower_to_barb_using(
    source: &Path,
    target: &dyn Target,
    packages: &Packages,
) -> Result<barb::Program, Diagnostic> {
    match check_package_using(source, target, packages)? {
        Package::Application(barb) => Ok(*barb),
        Package::Library => Err(Diagnostic::new("a library has no `main!` to build")
            .help("write `main! : Host -> []` and a clause `main!(host) -> ...`")),
    }
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
    lower_tests_to_barb_using(source, target, &Packages::default())
}

/// [`lower_tests_to_barb`], reading each URL dependency from where
/// `packages` says.
///
/// # Errors
/// Reports loading, resolution, checking or lowering errors.
pub fn lower_tests_to_barb_using(
    source: &Path,
    target: &dyn Target,
    packages: &Packages,
) -> Result<Tests, Diagnostic> {
    let mut loaded = load(source, target, packages)?;
    let application = Main::find_in(&loaded)?;
    let main = expectations::main(&mut loaded);
    let facts = test_uses::Facts::of(&loaded);
    let (program, mut cx) = resolve(loaded)?;
    test_uses::check(&program, &cx, &facts)?;
    let program = host::sign_main(program, &cx, application.as_ref());
    let (program, expectations) = expectations::enter(program, &mut cx, &main);
    let Package::Application(barb) = lower(program, cx, Some(&main), target)? else {
        unreachable!("the expectations' runner is an application")
    };
    Ok(Tests {
        barb: *barb,
        expectations,
    })
}

/// Read the package at `source`, beside the standard package and `target`'s
/// host.
fn load(
    source: &Path,
    target: &dyn Target,
    packages: &Packages,
) -> Result<LoadedProgram, Diagnostic> {
    modules::load_program_using(source, standard_path(), &host_path(target)?, packages)
}

/// The modules of the package at `source`, its root first, each with its
/// text: what `faun bundle` writes.
///
/// # Errors
/// Reports loading errors.
///
/// # Panics
/// Never: every loaded module has its source.
pub fn package_modules(
    source: &Path,
    target: &dyn Target,
    packages: &Packages,
) -> Result<Vec<(PathBuf, String)>, Diagnostic> {
    let loaded = load(source, target, packages)?;
    let mut modules = vec![loaded.entry];
    modules.extend(loaded.package.iter().filter(|&&id| id != loaded.entry));
    Ok(modules
        .into_iter()
        .map(|id| {
            let module = loaded.module(id);
            let text = loaded
                .sources
                .get(module.source)
                .expect("a loaded module has its source")
                .text()
                .to_owned();
            (module.path.clone(), text)
        })
        .collect())
}

/// Name every global and local `loaded` writes, and write its record
/// builders out: the program as HIR, and the context every later stage
/// reads.
///
/// # Errors
/// Reports a standard package or host missing what literals and the entry
/// are made of, and a name nothing declares or two declarations share.
pub fn resolve(loaded: LoadedProgram) -> Result<(hir::Program, Context), Diagnostic> {
    let prelude = blessed::PreludeIds::find_in(&loaded)?;
    let host = host::HostIds::find_in(&loaded)?;
    let (program, mut cx) = resolve::resolve_names(loaded, prelude, host)?;
    let program = builders::desugar(program, &mut cx);
    Ok((program, cx))
}

/// Check `program` and lower it to Barb, entering by `main`.
fn lower(
    program: hir::Program,
    mut cx: Context,
    main: Option<&Main>,
    target: &dyn Target,
) -> Result<Package, Diagnostic> {
    let typed = checked(program, &mut cx)?;
    if let Some(main) = main {
        host::check_application_abi(&typed, &cx, main)?;
    }
    let routines = target.routines();
    let program = specialize::monomorphize_package(&typed, &cx, main)?;
    second_class::check(&program, &cx)?;
    let program = callbacks::lower(program, &cx)?;
    linearity::check(&program, &typed, &cx, &routines)?;
    let program = pattern_compile::compile(program, &cx)?;
    if main.is_none() {
        return Ok(Package::Library);
    }
    barb_lower::lower_package_to_barb(program, &cx, &routines)
        .map(|barb| Package::Application(Box::new(barb)))
}

/// `program` with each function's signature and clauses grouped, the
/// members it asks for written, its types inferred, and its patterns
/// known to cover what they take apart: typed HIR.
///
/// # Errors
/// Reports what checking refuses, and clauses that leave a case unmatched.
pub fn checked(program: hir::Program, cx: &mut Context) -> Result<typed::Program, Diagnostic> {
    let program = declarations::normalize(program);
    let program = derive::requested(program, cx)?;
    let typed = check::type_check(program, cx)?;
    exhaustive::check(&typed, cx)?;
    Ok(typed)
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
/// Reports what the machine tier or the target cannot represent.
pub fn compile_barb_to_image(
    barb: barb::Program,
    target: &dyn Target,
) -> Result<Vec<u8>, Diagnostic> {
    compile_barb_to_image_with(barb, target, Favour::Speed, SymbolTable::Omitted)
}

/// [`compile_barb_to_image`], favouring speed or size where they pull apart,
/// with symbols naming each function where `symbols` asks and the target
/// writes them.
///
/// # Errors
/// As [`compile_barb_to_image`].
pub fn compile_barb_to_image_with(
    barb: barb::Program,
    target: &dyn Target,
    favour: Favour,
    symbols: SymbolTable,
) -> Result<Vec<u8>, Diagnostic> {
    let mut barb = barb;
    barb::optimize(&mut barb);
    let machine =
        faun_core::lower_to_machine_ir(&barb, &target.routines()).map_err(Diagnostic::new)?;
    target
        .compile_machine_ir_with(&machine, favour, symbols)
        .map_err(Diagnostic::new)
}

/// The x86-64 Linux host, which frontend tests load their programs with.
#[cfg(test)]
fn test_host() -> PathBuf {
    standard_path().with_file_name("hosts/x86_64-linux.fn")
}

/// A package checked as [`lower_to_barb`] checks one, for a test to read a
/// later stage of.
#[cfg(test)]
pub(crate) struct Checked {
    pub(crate) program: typed::Program,
    pub(crate) cx: Context,
}

/// The package at `entry`, beside the standard package and the x86-64 Linux
/// host, checked.
#[cfg(test)]
pub(crate) fn checked_for_test(entry: &Path) -> Checked {
    let loaded = modules::load_program(entry, standard_path(), &test_host()).unwrap();
    let (program, mut cx) = resolve(loaded).unwrap();
    let program = checked(program, &mut cx).unwrap();
    Checked { program, cx }
}

/// The host module mounted at `std.host` for `target`.
fn host_path(target: &dyn Target) -> Result<PathBuf, Diagnostic> {
    let path = standard_path().with_file_name(format!("hosts/{}.fn", target.name()));
    if !standard::is_module(&path) {
        return Err(Diagnostic::new(format!(
            "no Faun host module for target `{}`",
            target.name()
        )));
    }
    Ok(path)
}

#[cfg(test)]
mod tests;
