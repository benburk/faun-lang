//! What a target is entitled to assume.

use super::model::{Class, Exit, Op, Program, Range, RegionId};
use crate::platform::routine;

/// What a program has to be true of before a target sees it. These are the
/// mistakes a builder can make that a target would otherwise miscompile in
/// silence rather than reject.
///
/// # Errors
///
/// Names the first disagreement found.
pub fn validate(program: &Program) -> Result<(), String> {
    for function in program.functions() {
        let name = program.name(function.name);
        let returns = program.signature(function.returns);
        check(program, name, function.body, returns)?;
    }
    Ok(())
}

fn check(program: &Program, name: &str, region: RegionId, returns: &[Class]) -> Result<(), String> {
    for (op, results) in program.walk(region) {
        match *op {
            // Operands of one operation are read at one width, and a value
            // needing fewer bits already reads as one needing more. What
            // they may not be is wider than what reads them, or an address
            // where a number is read.
            Op::Binary { left, right, .. } => {
                let held = program.class(results[0]);
                for operand in [left, right] {
                    let operand = program.class(operand);
                    if !operand.fits(held) {
                        return Err(format!("{name}: {operand:?} read as {held:?}"));
                    }
                }
            }
            Op::Compare { left, right, .. } => {
                let (left, right) = (program.class(left), program.class(right));
                if !left.fits(right) && !right.fits(left) {
                    return Err(format!("{name}: {left:?} and {right:?} in one operation"));
                }
            }
            Op::Call { .. } | Op::PlatformCall { .. } => given(program, name, op)?,
            Op::If {
                then_region,
                else_region,
                ..
            } => {
                check(program, name, then_region, returns)?;
                check(program, name, else_region, returns)?;
            }
            Op::Loop { body, .. } => check(program, name, body, returns)?,
            _ => {}
        }
    }
    leaves(program, name, region)?;

    left(program, name, region, returns)
}

/// What a region leaves with, against what the function it is in answers.
fn left(program: &Program, name: &str, region: RegionId, returns: &[Class]) -> Result<(), String> {
    let terminator = program.region(region).terminator;
    if terminator.exit != Exit::Return {
        return Ok(());
    }
    let found: Vec<_> = program
        .values(terminator.values)
        .iter()
        .map(|&value| program.class(value))
        .collect();
    let fits = found.len() == returns.len()
        && found
            .iter()
            .zip(returns)
            .all(|(found, wanted)| found.fits(*wanted));
    if fits {
        return Ok(());
    }
    Err(format!(
        "{name} returns {returns:?} but leaves with {found:?}"
    ))
}

/// What a call hands over, against what the name it calls takes. A target
/// reads arguments by position, so one too many, or one of another class,
/// is read as something it is not.
fn given(program: &Program, name: &str, op: &Op) -> Result<(), String> {
    let classes = |values: Range| -> Vec<Class> {
        program
            .values(values)
            .iter()
            .map(|&value| program.class(value))
            .collect()
    };
    let (callee, takes, args) = match *op {
        Op::Call { function, args } => {
            let callee = &program.functions()[function.index()];
            (callee.name, classes(callee.params), args)
        }
        Op::PlatformCall { platform, args } => {
            let routine = &program.platforms()[platform.index()];
            (
                routine.name,
                program.signature(routine.params).to_vec(),
                args,
            )
        }
        _ => return Ok(()),
    };
    let held = classes(args);
    if held.len() == takes.len()
        && held
            .iter()
            .zip(&takes)
            .all(|(held, wanted)| held.fits(*wanted))
    {
        return Ok(());
    }
    let callee = program.name(callee);
    Err(format!(
        "{name} calls `{callee}` with {held:?} where it takes {takes:?}"
    ))
}

/// A call to a routine that does not come back ends its region: nothing
/// after it is reached, so nothing may be written there for a target to lay
/// out. The terminator says the same thing, and has to.
fn leaves(program: &Program, name: &str, region: RegionId) -> Result<(), String> {
    let ops = program.ops(region);
    for (at, op) in ops.iter().enumerate() {
        let Op::PlatformCall { platform, .. } = *op else {
            continue;
        };
        let held = program.name(program.platforms()[platform.index()].name);
        if routine(held).is_none_or(|routine| routine.comes_back) {
            continue;
        }
        if at + 1 != ops.len() || program.region(region).terminator.exit != Exit::Unreachable {
            return Err(format!(
                "{name} calls `{held}`, which does not come back, and carries on"
            ));
        }
    }
    Ok(())
}
