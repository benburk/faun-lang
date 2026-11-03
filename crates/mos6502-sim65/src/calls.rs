//! How deep calls can go on the hardware stack.
//!
//! The hardware stack is one page, and every `jsr` pushes two bytes onto it,
//! so it holds 128 return addresses. A function that can reach itself through
//! calls can go deeper than that, and is the one place a check is needed:
//! anything else calls only so deep. Each function in a call cycle checks
//! the stack pointer on the way in, leaving room for whatever its body
//! pushes before it reaches the next function that checks.

use faun_core::ir::{FunctionId, Op, Program};

/// What a `jsr` pushes: its return address.
const RETURN_ADDRESS: u16 = 2;

/// For each function in a call cycle, the bytes of hardware stack its body
/// may push before anything it calls checks again; nothing for the rest.
/// A program whose calls cannot go round has nothing for every function.
pub(crate) fn reserves(program: &Program) -> Vec<Option<u16>> {
    let callees = callees(program);
    let cycles: Vec<bool> = (0..callees.len())
        .map(|at| reaches_itself(&callees, at))
        .collect();
    let mut below = vec![None; callees.len()];
    (0..callees.len())
        .map(|at| cycles[at].then(|| pushed(&callees, &cycles, &mut below, at)))
        .collect()
}

/// What each function calls: another body, by index, or `None` for a routine
/// the simulator answers, which a `jsr` to one of its hooks reaches.
fn callees(program: &Program) -> Vec<Vec<Option<usize>>> {
    program
        .functions()
        .iter()
        .map(|function| {
            let Some(body) = function.body() else {
                return Vec::new();
            };
            program
                .every(body)
                .filter_map(|op| match *op {
                    Op::Call { function, .. } => Some(callee(program, function)),
                    _ => None,
                })
                .collect()
        })
        .collect()
}

fn callee(program: &Program, function: FunctionId) -> Option<usize> {
    let defined = program.function(function).body().is_some();
    defined.then_some(function.index())
}

/// Whether a function reaches itself through what it calls.
fn reaches_itself(callees: &[Vec<Option<usize>>], start: usize) -> bool {
    let mut seen = vec![false; callees.len()];
    let mut held: Vec<usize> = callees[start].iter().flatten().copied().collect();
    while let Some(at) = held.pop() {
        if at == start {
            return true;
        }
        if seen[at] {
            continue;
        }
        seen[at] = true;
        held.extend(callees[at].iter().flatten());
    }
    false
}

/// The most a function's body pushes before something it calls checks: a
/// return address for each call, and below one to a function that does not
/// check, what that one's body pushes. Functions outside every cycle call
/// round nothing, so this comes to an end; each is worked out once.
fn pushed(
    callees: &[Vec<Option<usize>>],
    cycles: &[bool],
    below: &mut [Option<u16>],
    function: usize,
) -> u16 {
    let mut most = 0;
    for &callee in &callees[function] {
        let beneath = match callee {
            Some(at) if !cycles[at] => unchecked(callees, cycles, below, at),
            _ => 0,
        };
        let reach = RETURN_ADDRESS.saturating_add(beneath);
        most = most.max(reach);
    }
    most
}

/// What a function that does not check pushes, worked out the first time
/// it is asked for.
fn unchecked(
    callees: &[Vec<Option<usize>>],
    cycles: &[bool],
    below: &mut [Option<u16>],
    function: usize,
) -> u16 {
    if let Some(known) = below[function] {
        return known;
    }
    let found = pushed(callees, cycles, below, function);
    below[function] = Some(found);
    found
}
