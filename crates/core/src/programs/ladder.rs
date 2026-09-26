//! The simplest programs there are, written where a program is written.
//!
//! Barb is the tier a program arrives at, whether a frontend wrote it or
//! it was built here, so a question about what the whole compiler
//! does has to be asked from there. The rest of `programs` is written at the
//! tier a target reads, which answers a different question: what a backend
//! does with IR it was handed.
//!
//! Each of these is nearly the least a program can do, and the next does one
//! thing more. What they are for is the question "is this as small as it can
//! be", which nobody can answer about a program doing four things at once.

use crate::barb::{FnId, Program, TypeId};

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
}

/// The declarations every program here starts from: authority, an empty
/// type, numbers, and the host routine it reaches. None of it says how
/// wide anything is: what a routine answers and what the entry is handed
/// are the target's to say, when the program is lowered for one.
fn ground() -> Ground {
    let mut program = Program::default();
    let host = program.declare_type("Host");
    program.define_type(host, &[("Host", &[])]);
    let never = program.declare_type("Never");
    program.define_type(never, &[]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);

    let exit = program.declare("exit!", &[host, nat], never);
    Ground {
        program,
        host,
        nat,
        never,
        exit,
    }
}

/// `main!`, handed authority and the count its target produces at startup,
/// which is a parameter named for it.
fn counted_main(program: &mut Program, ground: (TypeId, TypeId, TypeId)) -> FnId {
    let (host, nat, never) = ground;
    program.declare_named("main!", &[("host", host), ("argc", nat)], never)
}

/// Leave, with a number known before the program ran.
///
/// The least a program can do. Nothing is worked out and nothing is asked of
/// the machine, so what a target writes is the status and the way out.
///
/// # Panics
/// If `status` does not fit the declared natural shape.
#[must_use]
pub fn exits_with_a_constant(status: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
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
pub fn exits_with_the_count() -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let main = counted_main(&mut program, (host, nat, never));
    program.define(main, |b, args| b.call(exit, &[args[0], args[1]]));
    program.set_entry(main);
    program
}

/// The same, with something worked out from it: the count, and `more` past
/// it.
///
/// A count is as wide as the machine, so a number past one needs a bit the
/// machine has not got. The guard is what buys that bit back, which is the
/// other answer to the one a remainder gives: prove the bit is not needed
/// rather than say it may go.
///
/// A `more` of nought is the guard on its own, with nothing worked out past
/// it, which is the rung between the two.
///
/// # Panics
/// If `limit` does not fit the declared natural shape.
#[must_use]
pub fn exits_with_the_count_and_more(limit: u64, more: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let truth = program.declare_type("Bool");
    program.define_type(truth, &[("False", &[]), ("True", &[])]);
    let (no, _) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let succ = program.ctor_at(nat, 1);
    let below = comparing(&mut program, nat, truth);

    let main = counted_main(&mut program, (host, nat, never));
    program.define(main, |b, args| {
        let (host, count) = (args[0], args[1]);
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

/// Leave with a sum in which one intermediate is read twice.
///
/// The guard and first addition are already on earlier rungs. This adds a
/// fork to the value graph: `a` feeds both `b` and the final addition. A target
/// with one accumulator has to choose which side of that final addition to
/// load first, and need not store the side it already holds.
///
/// # Panics
/// If `limit` or three does not fit the declared natural shape.
#[must_use]
pub fn exits_with_a_shared_intermediate(limit: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let truth = program.declare_type("Bool");
    program.define_type(truth, &[("False", &[]), ("True", &[])]);
    let (no, _) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let below = comparing(&mut program, nat, truth);
    let adding = adds(&mut program, nat);
    let [ceiling, three] =
        [limit, 3].map(|n| program.intern_number(nat, n).expect("the natural shape"));

    let main = counted_main(&mut program, (host, nat, never));
    program.define(main, |b, args| {
        let (host, count) = (args[0], args[1]);
        let ceiling = b.known(ceiling);
        let under = b.call(below, &[count, ceiling]);
        let kept = b.match_(under, truth, |b, ctor, _| {
            if ctor == no {
                let nought = b.number(nat, 0).expect("the declared natural shape");
                let nought = b.known(nought);
                b.call(exit, &[host, nought])
            } else {
                count
            }
        });
        let three = b.known(three);
        let a = b.call(adding, &[kept, three]);
        let b_value = b.call(adding, &[a, kept]);
        let answer = b.call(adding, &[a, b_value]);
        b.call(exit, &[host, answer])
    });
    program.set_entry(main);
    program
}

/// Leave with the count and a number known before the program ran, keeping
/// only the bits below `bits`.
///
/// One thing more than leaving with the count, and the smallest program that
/// does arithmetic on something it was handed. A count is as wide as the
/// machine, so the sum needs a bit the machine has not got; asking for the
/// remainder says that bit may go, where a guard would buy it back. Nothing
/// branches, so what a target writes is a load, an addition and the way out.
///
/// # Panics
/// If `bits` or `more` does not describe something the declared shape holds.
#[must_use]
pub fn exits_with_the_count_and_a_constant(bits: u32, more: u64) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let truth = program.declare_type("Bool");
    program.define_type(truth, &[("False", &[]), ("True", &[])]);
    let adding = adds(&mut program, nat);
    let remainder = remainders(&mut program, nat, truth, adding);
    let modulus = program
        .intern_number(nat, 1 << bits)
        .expect("the declared natural shape");
    // Counting onto the count rather than the other way about: what `add`
    // goes round on is its second argument, and the one that is known is the
    // one whose steps can be run together before anything runs.
    let more = program
        .intern_number(nat, more)
        .expect("the declared natural shape");

    let main = counted_main(&mut program, (host, nat, never));
    program.define(main, |b, args| {
        let (host, count) = (args[0], args[1]);
        let more = b.known(more);
        let sum = b.call(adding, &[count, more]);
        let modulus = b.known(modulus);
        let low = b.call(remainder, &[sum, modulus]);
        b.call(exit, &[host, low])
    });
    program.set_entry(main);
    program
}

/// Leave with the low byte of a sum.
///
/// A number counting without a last step says eight-bit wrapping arithmetic
/// by adding and asking for the remainder modulo two hundred and fifty-six.
/// Read the other way round that is two arbitrary-precision numbers, a heap
/// to hold them, and a division to finish; read as what it says, it is one
/// addition that throws its carry away.
///
/// # Panics
/// If `bits` does not describe a power of two the declared shape holds.
#[must_use]
pub fn exits_with_the_low_bits_of_a_sum(bits: u32) -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let truth = program.declare_type("Bool");
    program.define_type(truth, &[("False", &[]), ("True", &[])]);
    let adding = adds(&mut program, nat);
    let remainder = remainders(&mut program, nat, truth, adding);
    let modulus = program
        .intern_number(nat, 1 << bits)
        .expect("the declared natural shape");

    let main = counted_main(&mut program, (host, nat, never));
    program.define(main, |b, args| {
        let (host, count) = (args[0], args[1]);
        let sum = b.call(adding, &[count, count]);
        let modulus = b.known(modulus);
        let low = b.call(remainder, &[sum, modulus]);
        b.call(exit, &[host, low])
    });
    program.set_entry(main);
    program
}

/// Say something known before the program ran, then leave.
///
/// The least a program can do that someone sees. The words are known, so
/// they lie where the image puts them and are handed out from there; what a
/// target writes is the write and the way out, and nothing to hold them in.
/// What the write answers is not asked, so nothing is made of it either.
///
/// # Panics
/// If the greeting does not fit the declared shapes.
#[must_use]
pub fn greets() -> Program {
    let Ground {
        mut program,
        host,
        nat,
        never,
        exit,
        ..
    } = ground();
    let bytes = program.declare_type("Bytes");
    program.define_type(bytes, &[("Nil", &[]), ("Cons", &[nat, bytes])]);
    // Standard output is what the first descriptor past input names.
    let put = program.declare("fd_put!", &[nat, bytes], nat);
    let greeting = program
        .intern_byte_spine(bytes, b"Hello, world!")
        .expect("the declared byte shape");

    let main = program.declare("main!", &[host], never);
    program.define(main, |b, args| {
        let output = b.number(nat, 1).expect("the declared natural shape");
        let output = b.known(output);
        let greeting = b.known(greeting);
        b.call(put, &[output, greeting]);
        let nought = b.number(nat, 0).expect("the declared natural shape");
        let nought = b.known(nought);
        b.call(exit, &[args[0], nought])
    });
    program.set_entry(main);
    program
}

/// The sum of two counts, by counting one of them onto the other.
fn adds(program: &mut Program, nat: TypeId) -> FnId {
    let succ = program.ctor_at(nat, 1);
    let id = program.declare("add", &[nat, nat], nat);
    program.define(id, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(right, nat, |b, _, counted| match counted.first() {
            // Nothing added to it is it.
            None => left,
            Some(&less) => {
                let rest = b.call(id, &[left, less]);
                b.con(succ, &[rest])
            }
        })
    });
    id
}

/// What is left of one count after as many of another as fit.
///
/// Recursion on the dividend, so that what stops it is the shape of the
/// number rather than anything worked out while going round.
fn remainders(program: &mut Program, nat: TypeId, truth: TypeId, adding: FnId) -> FnId {
    let _ = adding;
    let (zero, succ) = (program.ctor_at(nat, 0), program.ctor_at(nat, 1));
    let (no, _) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let same = alike(program, nat, truth);

    // One more than what is left, unless what is left has reached the
    // divisor, when nothing is.
    let step = program.declare("mod_step", &[truth, nat], nat);
    program.define(step, |b, args| {
        b.match_(args[0], truth, |b, ctor, _| {
            if ctor == no {
                b.con(succ, &[args[1]])
            } else {
                b.con(zero, &[])
            }
        })
    });

    let id = program.declare("mod", &[nat, nat], nat);
    program.define(id, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(right, nat, move |b, _, divisor| {
            // Nothing goes into it no times, leaving all of it.
            let Some(&less) = divisor.first() else {
                return left;
            };
            b.match_(left, nat, move |b, _, counted| {
                let Some(&fewer) = counted.first() else {
                    return b.con(zero, &[]);
                };
                let rest = b.call(id, &[fewer, right]);
                let reached = b.call(same, &[rest, less]);
                b.call(step, &[reached, rest])
            })
        })
    });
    id
}

/// Whether two counts are the same count, by counting both down together.
fn alike(program: &mut Program, nat: TypeId, truth: TypeId) -> FnId {
    let (no, yes) = (program.ctor_at(truth, 0), program.ctor_at(truth, 1));
    let id = program.declare("equals", &[nat, nat], truth);
    program.define(id, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(left, nat, move |b, _, counted| {
            let Some(&fewer) = counted.first() else {
                return b.match_(right, nat, |b, _, counted| {
                    b.con(if counted.is_empty() { yes } else { no }, &[])
                });
            };
            b.match_(right, nat, move |b, _, counted| match counted.first() {
                None => b.con(no, &[]),
                Some(&other) => b.call(id, &[fewer, other]),
            })
        })
    });
    id
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

/// Every rung, in the order each does one thing more than the last, and each
/// named as the size baselines name it.
///
/// Arithmetic comes before branching: the two wrapping rungs work something
/// out from the count without asking anything about it, and the two guarded
/// ones ask. `limit` and `more` are small enough that what the guard proves
/// is a few bits rather than a machine word, which is what a program reading
/// a count and adding to it looks like when it is written to be compiled.
#[must_use]
pub fn every() -> Vec<(&'static str, Program)> {
    vec![
        ("a constant", exits_with_a_constant(0)),
        ("the count", exits_with_the_count()),
        (
            "the count and a constant",
            exits_with_the_count_and_a_constant(8, 4),
        ),
        ("the low bits of a sum", exits_with_the_low_bits_of_a_sum(8)),
        (
            "the count under a guard",
            exits_with_the_count_and_more(4, 0),
        ),
        ("the count and more", exits_with_the_count_and_more(4, 4)),
        (
            "a shared intermediate",
            exits_with_a_shared_intermediate(32),
        ),
        ("a greeting", greets()),
    ]
}
