//! The Faun compiler core, down to the tier a target reads.
//!
//! Source-language policy lives in the sibling `faun` crate. [`barb`] is the
//! shared functional core; [`ir`] decides
//! how a value is held, while [`platform`] describes what a target answers for.
//! A target is a separate crate implementing [`targets::Target`].

pub mod barb;
pub mod codegen;
pub mod facts;
pub mod float;
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
pub fn lower_to_machine_ir(
    program: &barb::Program,
    routines: &platform::Routines,
) -> Result<ir::Program, String> {
    lower_with_pipeline(program, routines, targets::Pipeline::Stock)
}

/// Lower Barb using the selected target-independent representation passes.
///
/// # Errors
/// Reports invalid Barb or machine IR.
pub fn lower_with_pipeline(
    program: &barb::Program,
    routines: &platform::Routines,
    pipeline: targets::Pipeline,
) -> Result<ir::Program, String> {
    let (lower, counting): (Lower, Lower) = match pipeline {
        targets::Pipeline::Stock => (ir::lower, ir::lower_counting_arguments),
        targets::Pipeline::Lab => (ir::lab::lower, ir::lab::lower_counting_arguments),
    };
    let held = lower(program, routines)?;
    ir::validate(&held)?;
    let optimized = ir::optimize(&held);
    // A program that reads only how many arguments it has keeps no call
    // making them a list, and is lowered again without one, so that what
    // it holds is what it would have held counting them.
    let made = optimized
        .functions()
        .iter()
        .position(|function| optimized.name(function.name) == ir::MAKE_ARGUMENTS);
    if let Some(made) = made
        && !optimized.calls(ir::FunctionId::at(made))
    {
        let counted = counting(program, routines)?;
        ir::validate(&counted)?;
        return Ok(ir::optimize(&counted));
    }
    Ok(optimized)
}

type Lower = fn(&barb::Program, &platform::Routines) -> Result<ir::Program, String>;
