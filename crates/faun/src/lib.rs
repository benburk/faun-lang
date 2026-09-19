//! The compiler, down to the tier a target reads.
//!
//! Three tiers and the interface below them. [`surface`] is the language,
//! [`barb`] the core it lowers to, [`ir`] the tier that decides how a value
//! is held, and [`platform`] what a target answers for. A target is not
//! here: it is a crate implementing [`targets::Target`], so what this
//! compiles for is a fact about a build rather than about the compiler.

pub mod barb;
pub mod index;
pub mod ir;
pub mod platform;
pub mod programs;
pub mod surface;
pub mod targets;

/// Read a program and lower it to the tier a target compiles: what it says,
/// then what each definition computes, then how to compute it.
///
/// # Errors
///
/// Names what it could not read, or what it read and cannot represent.
pub fn read(text: &str, routines: &platform::Routines) -> Result<ir::Program, String> {
    read_with_options(text, routines, &barb::OptimizeOptions::default())
}

/// Compile with deterministic optimization controls. Totality checking always
/// runs, even when all optional passes are disabled.
///
/// # Errors
///
/// Names what it could not read, or what it read and cannot represent. Disabling
/// helper inlining can reduce the range information available to lowering.
pub fn read_with_options(
    text: &str,
    routines: &platform::Routines,
    options: &barb::OptimizeOptions,
) -> Result<ir::Program, String> {
    let mut program = surface::parse(text, routines)?;
    barb::validate(&program)?;
    barb::optimize(&mut program, options);
    let facts = barb::analyze(&program);
    ir::lower(&program, &facts, routines)
}
