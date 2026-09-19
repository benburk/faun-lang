//! Programs at the tier a target reads, for the things a language cannot
//! say yet.
//!
//! `examples/` holds programs somebody wrote, and everything in one of
//! those is something the language has a spelling for. These are the rest:
//! the heap, a global counted in place, a byte stored and read back, an arm
//! that leaves. A target has to lay all of it out whether or not anything
//! above can ask for it.
//!
//! Nothing here names a machine. What each becomes is a question for
//! whichever target is handed one, and every target is handed all of them.

use crate::ir::Class::Word;
use crate::ir::{Binary, Builder, Class, Offset, Program, Relation, Width};

const MESSAGE: &[u8] = b"Hello, World!\n";

#[must_use]
pub fn hello_world() -> Program {
    let (mut program, main) = Program::new("main");
    let message = program.intern(MESSAGE);
    let write = program.platform("write");

    program.define(main, |b, _| {
        let buf = b.address_of(message);
        let len = b.data_len(message);
        b.platform_call(write, &[buf, len]);

        let status = b.constant(Word, 0);
        b.ret(&[status])
    });

    program
}

/// `2 + 2`, written in barb.
///
/// `Nat` is the inductive type it is, so addition recurses on its second
/// argument and the literal is a known value. Nothing here says a number is
/// a word; the machine tier decides that when it lowers this.
#[must_use]
pub fn two_and_two_in_barb() -> crate::barb::Program {
    let mut program = crate::barb::Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);

    let add = program.declare("add", &[nat, nat], nat);
    program.define(add, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(right, nat, |b, ctor, fields| match fields {
            [] => left,
            [k] => {
                let rest = b.call(add, &[left, *k]);
                b.con(ctor, &[rest])
            }
            _ => unreachable!("Nat takes at most one field"),
        })
    });

    let two = program.intern_number(nat, 2);
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let value = b.known(nat, two);
        b.call(add, &[value, value])
    });
    program.set_entry(main);
    program
}

/// Two exits from one entry, one of them with nought. Whatever a target
/// makes of the second, the first has to leave with the status it says.
#[must_use]
pub fn exits_from_a_branch(taken: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let exit = program.platform("exit");

    program.define(main, |b, _| {
        let value = b.constant(Word, taken);
        let zero = b.constant(Word, 0);
        let nought = b.compare(Relation::Equal, value, zero);
        b.if_(
            nought,
            &[],
            // Neither arm comes back, so neither reaches the join.
            |b| {
                let status = b.constant(Word, 0);
                b.platform_call(exit, &[status]);
                crate::ir::Terminator::UNREACHABLE
            },
            |b| {
                let status = b.constant(Word, 5);
                b.platform_call(exit, &[status]);
                crate::ir::Terminator::UNREACHABLE
            },
        );
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// An arm too long to reach over with a byte of displacement.
///
/// Which is the one
/// thing that makes a layout take more than a guess and a confirmation.
/// Which arm is long decides which branch cannot reach: the one jumping
/// over it to the join, or the one testing the condition.
///
/// The long arm is the arm that runs, so the answer is `steps` either way
/// and a branch landing anywhere else answers something else.
#[must_use]
pub fn a_branch_over_a_long_arm(steps: u64, first: bool) -> Program {
    fn counts(b: &mut Builder, steps: u64) -> crate::ir::Terminator {
        let mut total = b.constant(Word, 0);
        for _ in 0..steps {
            let one = b.constant(Word, 1);
            total = b.binary(Binary::Add, total, one);
        }
        b.yield_(&[total])
    }
    fn nothing(b: &mut Builder) -> crate::ir::Terminator {
        let held = b.constant(Word, 0);
        b.yield_(&[held])
    }

    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        // Worked out rather than written, so no target folds the branch away
        // and lays the arms out as one run.
        let zero = b.constant(Word, 0);
        let held = b.constant(Word, u64::from(!first));
        let taken = b.compare(Relation::Equal, zero, held);
        let answer = if first {
            b.if_(taken, &[Word], |b| counts(b, steps), nothing)
        } else {
            b.if_(taken, &[Word], nothing, |b| counts(b, steps))
        };
        b.ret(&answer)
    });
    program
}

/// Both sides worked out, where every comparison here has had one side
/// written. A target with one accumulator has to hold the left somewhere
/// while it reads the right, and that is a different instruction.
#[must_use]
pub fn compares_two_worked_out_values() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let one = b.constant(Word, 1);
        let two = b.binary(Binary::Add, one, one);
        let three = b.binary(Binary::Add, two, one);
        let answer = b.compare(Relation::Less, two, three);
        b.ret(&[answer])
    });
    program
}

/// A condition that is not the comparison just made: a flag read back out
/// of storage, which a target has to test for itself.
#[must_use]
pub fn branches_on_a_flag_it_read() -> Program {
    let (mut program, main) = Program::new("main");
    let flag = program.global(&[1, 0, 0, 0, 0, 0, 0, 0]);

    program.define(main, |b, _| {
        let at = b.address_of(flag);
        let held = b.load(Width::Word, at, Offset::Words(0));
        let answer = b.if_(
            held,
            &[Word],
            |b| {
                let held = b.constant(Word, 7);
                b.yield_(&[held])
            },
            |b| {
                let held = b.constant(Word, 9);
                b.yield_(&[held])
            },
        );
        b.ret(&answer)
    });
    program
}

/// "hi\n" again, with the length worked out as well as the bytes.
///
/// Neither of the routine's arguments is then a constant a target can lay
/// down.
///
/// # Panics
///
/// If the message outgrew what a word on the smallest target holds.
#[must_use]
pub fn writes_a_length_it_worked_out() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");
    let write = program.platform("write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let one = b.constant(Word, 1);
        let two = b.constant(Word, 2);
        let length = b.binary(Binary::Add, one, two);
        b.platform_call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// A loop carrying a total that nothing in the body itself reads.
///
/// Both the
/// arm that leaves with it and the arm that adds to it are inside the `if`,
/// so whether it is still wanted is a question about the arms.
#[must_use]
pub fn carries_a_total_into_an_arm(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        let total = b.constant(Word, 0);
        let answer = b.loop_(&[start, total], &[Word], |b, params| {
            let (n, total) = (params[0], params[1]);
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[total]),
                |b| {
                    let one = b.constant(Word, 1);
                    let next = b.binary(Binary::Sub, n, one);
                    let more = b.binary(Binary::Add, total, one);
                    b.continue_(&[next, more])
                },
            );
            crate::ir::Terminator::UNREACHABLE
        });
        b.ret(&answer)
    });
    program
}

/// The countdown again, with the step worked out in the body.
///
/// Rather than in
/// the arm that goes round. Nothing in the body reads it -- the `if` sits
/// between the step and the `continue` carrying it -- so whether the step
/// may be left until last is a question about what the arms read.
#[must_use]
pub fn counts_down_before_it_branches(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let tick = program.intern(b"tick\n".as_slice());
    let write = program.platform("write");

    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        b.loop_(&[start], &[], |b, params| {
            let n = params[0];
            let one = b.constant(Word, 1);
            let next = b.binary(Binary::Sub, n, one);
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[]),
                |b| {
                    let buf = b.address_of(tick);
                    let len = b.constant(Word, 5);
                    b.platform_call(write, &[buf, len]);
                    b.yield_(&[])
                },
            );
            b.continue_(&[next])
        });

        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// Nothing at all. A target's floor: headers, and whatever it takes to stop.
#[must_use]
pub fn empty() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

#[must_use]
pub fn two_and_two() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let two = b.constant(Word, 2);
        let sum = b.binary(Binary::Add, two, two);
        b.ret(&[sum])
    });
    program
}

/// `main` calls `double(21)` and exits with it. The point is the call, so
/// the answer is the exit status rather than anything printed.
#[must_use]
pub fn calls_a_function() -> Program {
    let (mut program, main) = Program::new("main");
    let double = program.declare("double", &[Word], &[Word]);
    program.define(double, |b, params| {
        let n = params[0];
        let doubled = b.binary(Binary::Add, n, n);
        b.ret(&[doubled])
    });

    program.define(main, |b, _| {
        let twenty_one = b.constant(Word, 21);
        let answer = b.call(double, &[twenty_one]);
        b.ret(&answer)
    });
    program
}

/// `sum(n)` recurses, so the call graph has a cycle and the callee needs a
/// frame that survives its own recursive call. 1 + 2 + 3 = 6.
#[must_use]
pub fn recurses() -> Program {
    let (mut program, main) = Program::new("main");
    let sum = program.declare("sum", &[Word], &[Word]);
    program.define(sum, |b, params| {
        let n = params[0];
        let zero = b.constant(Word, 0);
        let done = b.compare(Relation::Equal, n, zero);
        let answer = b.if_(
            done,
            &[Word],
            |b| {
                let zero = b.constant(Word, 0);
                b.yield_(&[zero])
            },
            |b| {
                let one = b.constant(Word, 1);
                let less = b.binary(Binary::Sub, n, one);
                let rest = b.call(sum, &[less]);
                let total = b.binary(Binary::Add, n, rest[0]);
                b.yield_(&[total])
            },
        );
        b.ret(&answer)
    });

    program.define(main, |b, _| {
        let three = b.constant(Word, 3);
        let answer = b.call(sum, &[three]);
        b.ret(&answer)
    });
    program
}

/// Ask the platform for a page, write two words into it, read one back.
/// Exits with what it read, so nothing but real memory can make it pass.
#[must_use]
pub fn uses_the_heap() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        let answer = b.constant(Word, 42);
        let decoy = b.constant(Word, 7);
        b.store(Width::Word, page, Offset::Words(0), decoy);
        b.store(Width::Word, page, Offset::Words(1), answer);

        let answer = b.load(Width::Word, page, Offset::Words(1));
        b.ret(&[answer])
    });
    program
}

/// Several values still wanted after a call, and a callee greedy enough to
/// take every pair it can. Anything the caller fails to hand back shows up
/// in the answer.
///
/// `clobber(x)` is `x + 2` through three intermediates; `outer(10, 3)` is
/// `13 + 7 + 12 + 10 + 3`.
#[must_use]
pub fn values_survive_a_call() -> Program {
    let (mut program, main) = Program::new("main");
    let clobber = program.declare("clobber", &[Word], &[Word]);
    let outer = program.declare("outer", &[Word, Word], &[Word]);

    program.define(clobber, |b, params| {
        let x = params[0];
        let one = b.constant(Word, 1);
        let two = b.constant(Word, 2);
        let three = b.constant(Word, 3);
        let up = b.binary(Binary::Add, x, one);
        let down = b.binary(Binary::Sub, up, two);
        let back = b.binary(Binary::Add, down, three);
        b.ret(&[back])
    });

    program.define(outer, |b, params| {
        let (a, second) = (params[0], params[1]);
        let p = b.binary(Binary::Add, a, second);
        let q = b.binary(Binary::Sub, a, second);
        let r = b.call(clobber, &[a])[0];
        // Every one of these was computed before the call.
        let total = b.binary(Binary::Add, p, q);
        let total = b.binary(Binary::Add, total, r);
        let total = b.binary(Binary::Add, total, a);
        let total = b.binary(Binary::Add, total, second);
        b.ret(&[total])
    });

    program.define(main, |b, _| {
        let ten = b.constant(Word, 10);
        let three = b.constant(Word, 3);
        let answer = b.call(outer, &[ten, three]);
        b.ret(&answer)
    });
    program
}

/// Writes through an address the program worked out for itself.
///
/// Which is the case a target cannot answer with a block of constants.
///
/// # Panics
///
/// If the message outgrew what a word on the smallest target holds.
#[must_use]
pub fn writes_from_the_heap() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");
    let write = program.platform("write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        // "hi\n", a byte at a time, since the bytes are computed too.
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let length = b.constant(Word, 3);
        b.platform_call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// A byte store must not disturb its neighbour, and a byte above 127 must
/// come back zero-extended rather than as a very large word. Answers
/// `(first == 200) + second`, so both have to hold to reach 8.
#[must_use]
pub fn stores_a_byte() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        let high = b.constant(Word, 200);
        b.store(Width::Byte, page, Offset::Bytes(0), high);
        let neighbour = b.constant(Word, 7);
        b.store(Width::Byte, page, Offset::Bytes(1), neighbour);

        let first = b.load(Width::Byte, page, Offset::Bytes(0));
        let second = b.load(Width::Byte, page, Offset::Bytes(1));
        let expected = b.constant(Word, 200);
        let intact = b.compare(Relation::Equal, first, expected);
        let answer = b.binary(Binary::Add, intact, second);
        b.ret(&[answer])
    });
    program
}

/// A counter in a writable datum, bumped by a function called three times.
/// Nothing but storage outliving a call can answer 3.
#[must_use]
pub fn counts_in_a_global() -> Program {
    let (mut program, main) = Program::new("main");
    let counter = program.global(&[0; 8]);

    let bump = program.declare("bump", &[], &[]);
    program.define(bump, |b, _| {
        let at = b.address_of(counter);
        let seen = b.load(Width::Word, at, Offset::Words(0));
        let one = b.constant(Word, 1);
        let next = b.binary(Binary::Add, seen, one);
        b.store(Width::Word, at, Offset::Words(0), next);
        b.ret(&[])
    });

    program.define(main, |b, _| {
        b.call(bump, &[]);
        b.call(bump, &[]);
        b.call(bump, &[]);
        let at = b.address_of(counter);
        let answer = b.load(Width::Word, at, Offset::Words(0));
        b.ret(&[answer])
    });
    program
}

/// `Fixed { bits: 8 }` is arithmetic in Z/256, so 250 + 10 is 4 on every
/// target: free on a machine with eight-bit registers, a mask on the two
/// that are wider.
#[must_use]
pub fn wraps_at_eight_bits() -> Program {
    let byte = Class::Fixed { bits: 8 };
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let left = b.constant(byte, 250);
        let right = b.constant(byte, 10);
        let sum = b.binary(Binary::Add, left, right);
        // The entry returns a word, and this is where the width changes.
        let answer = b.convert(Word, sum);
        b.ret(&[answer])
    });
    program
}

/// `Relation::Less` is unsigned, and both targets carry an arm for it that
/// nothing else exercises.
#[must_use]
pub fn less(left: u64, right: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let left = b.constant(Word, left);
        let right = b.constant(Word, right);
        let answer = b.compare(Relation::Less, left, right);
        b.ret(&[answer])
    });
    program
}

/// `while n != 0 { print "tick"; n -= 1 }`, written the way the IR has it:
/// a loop carrying `n`, and an `if` that either breaks or goes round again.
#[must_use]
pub fn countdown(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let tick = program.intern(b"tick\n".as_slice());
    let write = program.platform("write");

    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        b.loop_(&[start], &[], |b, params| {
            let n = params[0];
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[]),
                |b| {
                    let buf = b.address_of(tick);
                    let len = b.constant(Word, 5);
                    b.platform_call(write, &[buf, len]);
                    let one = b.constant(Word, 1);
                    let next = b.binary(Binary::Sub, n, one);
                    b.continue_(&[next])
                },
            );
            crate::ir::Terminator::UNREACHABLE
        });

        let status = b.constant(Word, 0);
        b.ret(&[status])
    });

    program
}
