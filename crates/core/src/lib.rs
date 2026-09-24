//! The Faun compiler core, down to the tier a target reads.
//!
//! Source-language policy lives in the sibling `faun` and
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
    program: &mut barb::Program,
    routines: &platform::Routines,
) -> Result<ir::Program, String> {
    program.analyze();
    let held = ir::lower(program, routines)?;
    ir::validate(&held)?;
    Ok(ir::optimize(&held))
}

// Core unit tests still exercise source-to-machine behavior. Reuse the simple
// parser's source directly because a dev-dependency would compile a second,
// type-incompatible copy of this crate around the dependency cycle.
#[cfg(test)]
extern crate self as faun_core;

#[cfg(test)]
#[allow(unreachable_pub)]
#[path = "../../simple/src/parse.rs"]
mod simple_parse;

#[cfg(test)]
fn read(text: &str, routines: &platform::Routines) -> Result<ir::Program, String> {
    let mut program = read_barb(text, routines)?;
    machine(&mut program, routines)
}

#[cfg(test)]
fn read_barb(text: &str, routines: &platform::Routines) -> Result<barb::Program, String> {
    let mut program = read_valid(text, routines)?;
    barb::optimize(&mut program);
    Ok(program)
}

/// Read and check a program without optimizing it, for a test of what the
/// tiers below make of shapes the optimizer would have removed.
#[cfg(test)]
fn read_valid(text: &str, routines: &platform::Routines) -> Result<barb::Program, String> {
    let program = simple_parse::parse(text, routines)?;
    barb::validate(&program)?;
    Ok(program)
}

/// The same, lowered to machine IR.
#[cfg(test)]
fn read_unoptimized(text: &str, routines: &platform::Routines) -> Result<ir::Program, String> {
    read_with(text, routines, |_| {})
}

/// Read and check a program, run the stages `optimize` names, and lower it:
/// a test isolating lowering from one stage says which it runs instead.
#[cfg(test)]
fn read_with(
    text: &str,
    routines: &platform::Routines,
    optimize: impl FnOnce(&mut barb::Program),
) -> Result<ir::Program, String> {
    let mut program = read_valid(text, routines)?;
    optimize(&mut program);
    machine(&mut program, routines)
}

/// Every stage of the Barb schedule but its arithmetic laws, for a test of
/// lowering the operations those laws would have rewritten away.
#[cfg(test)]
fn optimize_without_laws(program: &mut barb::Program) {
    barb::structural(program);
    barb::normalize_with_limits(program, barb::InlineLimits::default());
    barb::fold(program);
}

#[cfg(test)]
mod simple {
    pub(crate) use super::simple_parse::parse;
}
