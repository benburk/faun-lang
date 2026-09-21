//! The simplest programs there are, written where a program is written.
//!
//! Barb is the tier a program arrives at, whether somebody wrote it in the
//! surface or built it here, so a question about what the whole compiler
//! does has to be asked from there. The rest of `programs` is written at the
//! tier a target reads, which answers a different question: what a backend
//! does with IR it was handed.
//!
//! Each of these is nearly the least a program can do, and the next does one
//! thing more. What they are for is the question "is this as small as it can
//! be", which nobody can answer about a program doing four things at once.

use crate::barb::{FnId, Program, TypeId};
use crate::platform::Routines;

/// What every program here is read against.
///
/// `Host` has one constructor and no fields, so it carries nothing and is
/// only ever something a program was handed. `Never` has no constructors at
/// all, which is what says a name answering it does not answer.
struct Ground {
    program: Program,
    host: TypeId,
    nat: TypeId,
    never: TypeId,
    exit: FnId,
    argc: FnId,
}

/// The same declarations the surface makes before it reads anything.
fn ground(routines: &Routines) -> Ground {
    let mut program = Program::default();
    let host = program.declare_type("Host");
    program.define_type(host, &[("Host", &[])]);
    let never = program.declare_type("Never");
    program.define_type(never, &[]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);

    let reached = |program: &mut Program, name: &str, takes: &[TypeId], result| {
        let id = program.declare(name, takes, result);
        if let Some(bounds) = routines.get(name).expect("a routine to reach").bounds() {
            program.bound(id, bounds);
        }
        id
    };
    let exit = reached(&mut program, "exit!", &[host, nat], never);
    let argc = reached(&mut program, "argc!", &[host], nat);
    Ground {
        program,
        host,
        nat,
        never,
        exit,
        argc,
    }
}

/// Leave, with a number known before the program ran.
///
/// The least a program can do. Nothing is worked out and nothing is asked of
/// the machine, so what a target writes is the status and the way out.
///
/// # Panics
/// If `status` does not fit the declared natural shape.
#[must_use]
pub fn exits_with_a_constant(routines: &Routines, status: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground(routines);
    let main = program.declare("main!", &[host], never);
    program.define(main, |b, args| {
        let held = b.number(nat, status).expect("the declared natural shape");
        let held = b.known(held);
        b.call(exit, &[args[0], held])
    });
    program.set_entry(main);
    program
}

/// Leave with what the world handed the program.
///
/// The count is the one thing every machine can be asked, and in a program
/// this small it is the only number not known before it runs.
#[must_use]
pub fn exits_with_the_count(routines: &Routines) -> Program {
    let Ground {
        mut program,
        host,
        never,
        exit,
        argc,
        ..
    } = ground(routines);
    let main = program.declare("main!", &[host], never);
    program.define(main, |b, args| {
        let count = b.call(argc, &[args[0]]);
        b.call(exit, &[args[0], count])
    });
    program.set_entry(main);
    program
}

/// The same, with something worked out from it: the count, and `more` past
/// it.
///
/// A count is as wide as the machine, so a number past one needs a bit the
/// machine has not got. The guard is what buys that bit back, which is why
/// no program reading a count does arithmetic on it without one.
///
/// # Panics
/// If `limit` does not fit the declared natural shape.
#[must_use]
pub fn exits_with_the_count_and_more(routines: &Routines, limit: u64, more: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        argc,
    } = ground(routines);
    let truth = program.declare_type("Bool");
    program.define_type(truth, &[("False", &[]), ("True", &[])]);
    let (no, _) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let succ = program.ctor_at(nat, 1);
    let below = comparing(&mut program, nat, truth);

    let main = program.declare("main!", &[host], never);
    program.define(main, |b, args| {
        let host = args[0];
        let count = b.call(argc, &[host]);
        let ceiling = b.number(nat, limit).expect("the declared natural shape");
        let ceiling = b.known(ceiling);
        let under = b.call(below, &[count, ceiling]);
        // Below the ceiling the count is the count; at or above it there is
        // nothing left to say, so the program leaves with nought.
        let kept = b.match_(under, truth, |b, ctor, _| {
            if ctor == no {
                let nought = b.number(nat, 0).expect("the declared natural shape");
                let nought = b.known(nought);
                b.call(exit, &[host, nought])
            } else {
                count
            }
        });
        let mut total = kept;
        for _ in 0..more {
            total = b.con(succ, &[total]);
        }
        b.call(exit, &[host, total])
    });
    program.set_entry(main);
    program
}

/// Whether the first of two counts is under the second, by counting both of
/// them down together.
///
/// Nothing here is recognised by its name. What the tier below reads is the
/// induction equation this definition is, so this is written the way the
/// equation is written and not the way it is easiest to write.
fn comparing(program: &mut Program, nat: TypeId, truth: TypeId) -> FnId {
    let (no, yes) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let id = program.declare("less_than", &[nat, nat], truth);
    program.define(id, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(left, nat, |b, _, counted| {
            let Some(&under) = counted.first() else {
                // Nought is under anything but nought.
                return b.match_(right, nat, |b, _, counted| {
                    b.con(if counted.is_empty() { no } else { yes }, &[])
                });
            };
            b.match_(right, nat, move |b, _, counted| match counted.first() {
                // Nothing is under nought.
                None => b.con(no, &[]),
                Some(&over) => b.call(id, &[under, over]),
            })
        })
    });
    id
}

/// Every rung, smallest first, each named as the size baselines name it.
///
/// `limit` and `more` are small enough that what the guard proves is a few
/// bits rather than a machine word, which is what a program reading a count
/// and adding to it looks like when it is written to be compiled.
#[must_use]
pub fn every(routines: &Routines) -> Vec<(&'static str, Program)> {
    vec![
        ("a constant", exits_with_a_constant(routines, 0)),
        ("the count", exits_with_the_count(routines)),
        (
            "the count and more",
            exits_with_the_count_and_more(routines, 4, 4),
        ),
    ]
}
