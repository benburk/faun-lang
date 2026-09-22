//! The compiler, down to the tier a target reads.
//!
//! The new [`surface`] frontend is growing toward Ori's source language.
//! [`simple`] preserves the original first-order test frontend and still feeds
//! [`barb`], the core it lowers to. [`ir`] decides how a value is held, while
//! [`platform`] describes what a target answers for. A target is not here: it
//! is a crate implementing [`targets::Target`], so what this compiles for is a
//! fact about a build rather than about the compiler.

pub mod barb;
pub mod facts;
pub mod index;
pub mod ir;
pub mod platform;
pub mod programs;
pub mod simple;
pub mod surface;
pub mod targets;

/// Read a program in the archived [`simple`] language and lower it to the
/// tier a target compiles.
///
/// # Errors
///
/// Names what it could not read, or what it read and cannot represent.
pub fn read(text: &str, routines: &platform::Routines) -> Result<ir::Program, String> {
    read_with_options(text, routines, &barb::OptimizeOptions::default())
}

/// Compile a [`simple`] program with deterministic optimization controls.
/// Totality checking always runs, even when all optional passes are disabled.
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
    machine(&read_barb_with_options(text, routines, options)?, routines)
}

/// Lower a validated, optimized Barb program to the machine IR a target
/// reads, and run the machine passes over it.
///
/// This is the rest of [`read_with_options`] once there is a Barb program
/// to do it to, and it is the whole compiler for anything written at that
/// tier rather than in a surface language.
///
/// # Errors
/// Names what it cannot represent.
pub fn machine(
    program: &barb::Program,
    routines: &platform::Routines,
) -> Result<ir::Program, String> {
    let facts = barb::analyze(program);
    let held = ir::lower(program, &facts, routines)?;
    // Machine passes read a structurally sound program and say nothing
    // useful about one that is not, so this is where it is said.
    ir::validate(&held)?;
    Ok(ir::optimize(&held, &ir::OptimizeOptions::default()))
}

/// Read a [`simple`] program, validate and optimize Barb, then stop before
/// representation selection.
///
/// This is the same archived frontend pipeline used by [`read_with_options`],
/// exposed for inspection. Analyze the returned program before machine
/// lowering.
///
/// # Errors
/// Reports parsing, typing, structural or totality errors. Inspection never
/// bypasses validation, even when optional optimization passes are disabled.
pub fn read_barb_with_options(
    text: &str,
    routines: &platform::Routines,
    options: &barb::OptimizeOptions,
) -> Result<barb::Program, String> {
    let mut program = simple::parse(text, routines)?;
    barb::validate(&program)?;
    barb::optimize(&mut program, options);
    Ok(program)
}
