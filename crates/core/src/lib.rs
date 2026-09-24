//! The Faun compiler core, down to the tier a target reads.
//!
//! Source-language policy lives in the sibling `faun` crate. [`barb`] is the
//! shared functional core; [`ir`] decides
//! how a value is held, while [`platform`] describes what a target answers for.
//! A target is a separate crate implementing [`targets::Target`].

pub mod barb;
pub mod facts;
pub mod index;
pub mod ir;
pub mod platform;
pub mod programs;
pub mod targets;

/// Lower a validated Barb program to machine IR and run the machine
/// optimization passes: the middle stage of compiling, between a frontend's
/// Barb and a target's image.
///
/// # Errors
///
/// Names what the machine tier cannot represent.
pub fn to_machine(
    program: &mut barb::Program,
    routines: &platform::Routines,
) -> Result<ir::Program, String> {
    let held = ir::lower(program, routines)?;
    ir::validate(&held)?;
    Ok(ir::optimize(&held))
}
