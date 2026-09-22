//! The archived simple frontend: text read directly into [`faun::barb`].
//!
//! This remains the smallest executable test of the core and backends. It is
//! deliberately close to Barb: first-order, monomorphic, and without the type
//! inference or richer forms of the primary `faun-frontend` crate.

mod parse;
pub mod programs;

pub use parse::parse;

/// Read a program and lower it to the machine IR a target compiles.
///
/// # Errors
///
/// Names what it could not read, or what it read and cannot represent.
pub fn read(text: &str, routines: &faun::platform::Routines) -> Result<faun::ir::Program, String> {
    read_with_options(text, routines, &faun::barb::OptimizeOptions::default())
}

/// Compile a program with deterministic optimization controls.
///
/// # Errors
///
/// Reports parsing, typing, structural, totality, or representation errors.
pub fn read_with_options(
    text: &str,
    routines: &faun::platform::Routines,
    options: &faun::barb::OptimizeOptions,
) -> Result<faun::ir::Program, String> {
    faun::machine(&read_barb_with_options(text, routines, options)?, routines)
}

/// Validate and optimize a program, stopping at Barb.
///
/// # Errors
///
/// Reports parsing, typing, structural, or totality errors.
pub fn read_barb_with_options(
    text: &str,
    routines: &faun::platform::Routines,
    options: &faun::barb::OptimizeOptions,
) -> Result<faun::barb::Program, String> {
    let mut program = parse(text, routines)?;
    faun::barb::validate(&program)?;
    faun::barb::optimize(&mut program, options);
    Ok(program)
}

#[cfg(test)]
mod tests;
