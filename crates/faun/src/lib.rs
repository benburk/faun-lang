//! The Faun compiler core, down to the tier a target reads.
//!
//! Source-language policy lives in the sibling `faun-frontend` and
//! `faun-simple` crates. [`barb`] is the shared functional core; [`ir`] decides
//! how a value is held, while [`platform`] describes what a target answers for.
//! A target is a separate crate implementing [`targets::Target`].

pub mod barb;
pub mod facts;
pub mod index;
pub mod ir;
pub mod platform;
pub mod programs;
pub mod targets;

/// Lower a validated, optimized Barb program to machine IR and run the machine
/// optimization passes.
///
/// # Errors
///
/// Names what the machine tier cannot represent.
pub fn machine(
    program: &barb::Program,
    routines: &platform::Routines,
) -> Result<ir::Program, String> {
    let facts = barb::analyze(program);
    let held = ir::lower(program, &facts, routines)?;
    ir::validate(&held)?;
    Ok(ir::optimize(&held, &ir::OptimizeOptions::default()))
}

// Core unit tests still exercise source-to-machine behavior. Reuse the simple
// parser's source directly because a dev-dependency would compile a second,
// type-incompatible copy of this crate around the dependency cycle.
#[cfg(test)]
extern crate self as faun;

#[cfg(test)]
#[allow(unreachable_pub)]
#[path = "../../simple/src/parse.rs"]
mod simple_parse;

#[cfg(test)]
fn read(text: &str, routines: &platform::Routines) -> Result<ir::Program, String> {
    read_with_options(text, routines, &barb::OptimizeOptions::default())
}

#[cfg(test)]
fn read_with_options(
    text: &str,
    routines: &platform::Routines,
    options: &barb::OptimizeOptions,
) -> Result<ir::Program, String> {
    machine(&read_barb_with_options(text, routines, options)?, routines)
}

#[cfg(test)]
fn read_barb_with_options(
    text: &str,
    routines: &platform::Routines,
    options: &barb::OptimizeOptions,
) -> Result<barb::Program, String> {
    let mut program = simple_parse::parse(text, routines)?;
    barb::validate(&program)?;
    barb::optimize(&mut program, options);
    Ok(program)
}

#[cfg(test)]
mod simple {
    pub(crate) use super::simple_parse::parse;
}
