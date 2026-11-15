//! How deep calls can go on the hardware stack.
//!
//! The hardware stack is one page, and every `jsr` pushes two bytes onto it,
//! so it holds 128 return addresses. A function that can reach itself through
//! calls can go deeper than that, and is the one place a check is needed:
//! anything else calls only so deep. Each function in a call cycle checks
//! the stack pointer on the way in, leaving room for whatever its body
//! pushes before it reaches the next function that checks. In a program
//! whose calls cannot go round, how deep they go, and how much of the frames'
//! stack they take, is known before it runs, and one that would not fit is
//! refused rather than built.

use faun_core::ir::{FunctionId, Op, Program};

/// What a `jsr` pushes: its return address.
pub(crate) const RETURN_ADDRESS: u32 = 2;

/// The bytes of hardware stack there are: one page.
pub(crate) const STACK: u32 = 256;

/// For each function in a call cycle, the bytes of hardware stack its body
/// may push before anything it calls checks again; nothing for the rest.
/// A program whose calls cannot go round has nothing for every function.
pub(crate) fn reserves(program: &Program) -> Vec<Option<u16>> {
    let callees = callees(program);
    let cycles = cycles(&callees);
    let nothing = vec![0; callees.len()];
    let mut walk = Walk::new(&callees, &cycles, &nothing, RETURN_ADDRESS);
    (0..callees.len())
        .map(|at| {
            cycles[at].then(|| {
                let pushed = walk.from(at).bytes;
                u16::try_from(pushed).unwrap_or(u16::MAX)
            })
        })
        .collect()
}

/// The deepest a chain of calls goes, by some measure: how many bytes it
/// takes, and the last function on it with a body.
#[derive(Clone, Copy)]
pub(crate) struct Chain {
    pub(crate) bytes: u32,
    pub(crate) ends: FunctionId,
}

/// How deep calls from the entry go in a program whose calls cannot go
/// round.
pub(crate) struct Depth {
    /// The return addresses its body pushes at once, the entry's own aside.
    pub(crate) pushed: Chain,
    /// The bytes of frames held at once, the entry's own among them, where
    /// `sizes` says how large each function's is.
    pub(crate) framed: Chain,
}

/// How deep calls from the entry go, where they cannot go round; nothing
/// where they can, since then a function in a cycle checks as it runs.
pub(crate) fn depth(program: &Program, sizes: &[u32]) -> Option<Depth> {
    let callees = callees(program);
    let cycles = cycles(&callees);
    if cycles.iter().any(|&round| round) {
        return None;
    }
    let entry = program.entry().index();
    let nothing = vec![0; callees.len()];
    let pushed = Walk::new(&callees, &cycles, &nothing, RETURN_ADDRESS).from(entry);
    let framed = Walk::new(&callees, &cycles, sizes, 0).from(entry);
    Some(Depth { pushed, framed })
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

/// Which functions are in a call cycle.
fn cycles(callees: &[Vec<Option<usize>>]) -> Vec<bool> {
    (0..callees.len())
        .map(|at| reaches_itself(callees, at))
        .collect()
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

/// Chains of calls, measured as `step` bytes for each call and `own` for
/// each body. A chain ends where it reaches a function that checks, which
/// is one in a cycle, or a routine the simulator answers.
struct Walk<'a> {
    callees: &'a [Vec<Option<usize>>],
    cycles: &'a [bool],
    own: &'a [u32],
    step: u32,
    /// The deepest chain from each function that does not check, worked
    /// out the first time it is asked for.
    below: Vec<Option<Chain>>,
}

impl<'a> Walk<'a> {
    fn new(
        callees: &'a [Vec<Option<usize>>],
        cycles: &'a [bool],
        own: &'a [u32],
        step: u32,
    ) -> Self {
        Self {
            callees,
            cycles,
            own,
            step,
            below: vec![None; callees.len()],
        }
    }

    /// The deepest chain from a function's body: its own bytes, and the most
    /// any call adds, a step for the call and below one to a function that
    /// does not check, that one's deepest chain. Functions outside every
    /// cycle call round nothing, so this comes to an end.
    fn from(&mut self, function: usize) -> Chain {
        let mut most = Chain {
            bytes: 0,
            ends: FunctionId::at(function),
        };
        let callees = self.callees;
        for &callee in &callees[function] {
            let beneath = match callee {
                Some(at) if !self.cycles[at] => self.unchecked(at),
                _ => Chain {
                    bytes: 0,
                    ends: FunctionId::at(function),
                },
            };
            let reach = self.step.saturating_add(beneath.bytes);
            if reach > most.bytes {
                most = Chain {
                    bytes: reach,
                    ends: beneath.ends,
                };
            }
        }
        let own = self.own[function];
        Chain {
            bytes: own.saturating_add(most.bytes),
            ends: most.ends,
        }
    }

    /// The deepest chain from a function that does not check, worked out the
    /// first time it is asked for.
    fn unchecked(&mut self, function: usize) -> Chain {
        if let Some(known) = self.below[function] {
            return known;
        }
        let found = self.from(function);
        self.below[function] = Some(found);
        found
    }
}
