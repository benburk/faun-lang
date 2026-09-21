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

pub mod abi;
pub mod arithmetic;
pub mod control;
pub mod external;
pub mod ladder;

use crate::ir::Class::Word;
use crate::ir::{Binary, Builder, Class, Offset, Program, Relation, Width};

const MESSAGE: &[u8] = b"Hello, World!\n";

#[must_use]
pub fn hello_world() -> Program {
    let (mut program, main) = Program::new("main");
    let message = program.intern(MESSAGE);
    let write = crate::platform::Routines::builtin().declare(&mut program, "write");

    program.define(main, |b, _| {
        let buf = b.address_of(message);
        let len = b.data_len(message);
        b.call(write, &[buf, len]);

        let status = b.constant(Word, 0);
        b.ret(&[status]);
    });

    program
}

/// `2 + 2`, written in barb.
///
/// `Nat` is the inductive type it is, so addition recurses on its second
/// argument and the literal is a known value. Nothing here says a number is
/// a word; the machine tier decides that when it lowers this.
///
/// # Panics
/// If the fixture's declarations do not describe a natural-number type.
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

    let two = program
        .intern_number(nat, 2)
        .expect("the declared natural shape");
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let value = b.known(two);
        b.call(add, &[value, value])
    });
    program.set_entry(main);
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
    fn counts(b: &mut Builder, steps: u64) {
        let mut total = b.constant(Word, 0);
        for _ in 0..steps {
            let one = b.constant(Word, 1);
            total = b.binary(Binary::Add, total, one);
        }
        b.yield_(&[total]);
    }
    fn nothing(b: &mut Builder) {
        let held = b.constant(Word, 0);
        b.yield_(&[held]);
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
        b.ret(&answer);
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
        b.ret(&[answer]);
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
                b.yield_(&[held]);
            },
            |b| {
                let held = b.constant(Word, 9);
                b.yield_(&[held]);
            },
        );
        b.ret(&answer);
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
    let grow = crate::platform::Routines::builtin().declare(&mut program, "grow");
    let write = crate::platform::Routines::builtin().declare(&mut program, "write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.call_one(grow, &[size]);
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let one = b.constant(Word, 1);
        let two = b.constant(Word, 2);
        let length = b.binary(Binary::Add, one, two);
        b.call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status]);
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
                    b.continue_(&[next, more]);
                },
            );
        });
        b.ret(&answer);
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
    let write = crate::platform::Routines::builtin().declare(&mut program, "write");

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
                    b.call(write, &[buf, len]);
                    b.yield_(&[]);
                },
            );
            b.continue_(&[next]);
        });

        let status = b.constant(Word, 0);
        b.ret(&[status]);
    });
    program
}

/// Nothing at all. A target's floor: headers, and whatever it takes to stop.
#[must_use]
pub fn empty() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let status = b.constant(Word, 0);
        b.ret(&[status]);
    });
    program
}

#[must_use]
pub fn two_and_two() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let two = b.constant(Word, 2);
        let sum = b.binary(Binary::Add, two, two);
        b.ret(&[sum]);
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
        b.ret(&[doubled]);
    });

    program.define(main, |b, _| {
        let twenty_one = b.constant(Word, 21);
        let answer = b.call(double, &[twenty_one]);
        b.ret(&answer);
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
                b.yield_(&[zero]);
            },
            |b| {
                let one = b.constant(Word, 1);
                let less = b.binary(Binary::Sub, n, one);
                let rest = b.call(sum, &[less]);
                let total = b.binary(Binary::Add, n, rest[0]);
                b.yield_(&[total]);
            },
        );
        b.ret(&answer);
    });

    program.define(main, |b, _| {
        let three = b.constant(Word, 3);
        let answer = b.call(sum, &[three]);
        b.ret(&answer);
    });
    program
}

/// Ask the platform for a page, write two words into it, read one back.
/// Exits with what it read, so nothing but real memory can make it pass.
#[must_use]
pub fn uses_the_heap() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = crate::platform::Routines::builtin().declare(&mut program, "grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.call_one(grow, &[size]);

        let answer = b.constant(Word, 42);
        let decoy = b.constant(Word, 7);
        b.store(Width::Word, page, Offset::Words(0), decoy);
        b.store(Width::Word, page, Offset::Words(1), answer);

        let answer = b.load(Width::Word, page, Offset::Words(1));
        b.ret(&[answer]);
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
        b.ret(&[back]);
    });

    program.define(outer, |b, params| {
        let (a, second) = (params[0], params[1]);
        let p = b.binary(Binary::Add, a, second);
        let q = b.binary(Binary::Sub, a, second);
        let r = b.call_one(clobber, &[a]);
        // Every one of these was computed before the call.
        let total = b.binary(Binary::Add, p, q);
        let total = b.binary(Binary::Add, total, r);
        let total = b.binary(Binary::Add, total, a);
        let total = b.binary(Binary::Add, total, second);
        b.ret(&[total]);
    });

    program.define(main, |b, _| {
        let ten = b.constant(Word, 10);
        let three = b.constant(Word, 3);
        let answer = b.call(outer, &[ten, three]);
        b.ret(&answer);
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
    let grow = crate::platform::Routines::builtin().declare(&mut program, "grow");
    let write = crate::platform::Routines::builtin().declare(&mut program, "write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.call_one(grow, &[size]);

        // "hi\n", a byte at a time, since the bytes are computed too.
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let length = b.constant(Word, 3);
        b.call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status]);
    });
    program
}

/// A byte store must not disturb its neighbour, and a byte above 127 must
/// come back zero-extended rather than as a very large word. Answers
/// `(first == 200) + second`, so both have to hold to reach 8.
#[must_use]
pub fn stores_a_byte() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = crate::platform::Routines::builtin().declare(&mut program, "grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.call_one(grow, &[size]);

        let high = b.constant(Word, 200);
        b.store(Width::Byte, page, Offset::Bytes(0), high);
        let neighbour = b.constant(Word, 7);
        b.store(Width::Byte, page, Offset::Bytes(1), neighbour);

        let first = b.load(Width::Byte, page, Offset::Bytes(0));
        let second = b.load(Width::Byte, page, Offset::Bytes(1));
        let expected = b.constant(Word, 200);
        let intact = b.compare(Relation::Equal, first, expected);
        let answer = b.binary(Binary::Add, intact, second);
        b.ret(&[answer]);
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
        b.ret(&[]);
    });

    program.define(main, |b, _| {
        b.call(bump, &[]);
        b.call(bump, &[]);
        b.call(bump, &[]);
        let at = b.address_of(counter);
        let answer = b.load(Width::Word, at, Offset::Words(0));
        b.ret(&[answer]);
    });
    program
}

/// `Fixed { bits: 8 }` is arithmetic in Z/256, so 250 + 10 is 4 on every
/// target: free on a machine with eight-bit registers, a mask on the two
/// that are wider.
#[must_use]
pub fn wraps_at_eight_bits() -> Program {
    let byte = Class::Fixed { bits: 8 };
    let wide = Class::Fixed { bits: 9 };
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let left = b.constant(wide, 250);
        let right = b.constant(wide, 10);
        let sum = b.binary(Binary::Add, left, right);
        // Fixed is a fit requirement. Only this explicit conversion wraps.
        let wrapped = b.convert(byte, sum);
        let answer = b.convert(Word, wrapped);
        b.ret(&[answer]);
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
        b.ret(&[answer]);
    });
    program
}

/// `while n != 0 { print "tick"; n -= 1 }`, written the way the IR has it:
/// a loop carrying `n`, and an `if` that either breaks or goes round again.
#[must_use]
pub fn countdown(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let tick = program.intern(b"tick\n".as_slice());
    let write = crate::platform::Routines::builtin().declare(&mut program, "write");

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
                    b.call(write, &[buf, len]);
                    let one = b.constant(Word, 1);
                    let next = b.binary(Binary::Sub, n, one);
                    b.continue_(&[next]);
                },
            );
        });

        let status = b.constant(Word, 0);
        b.ret(&[status]);
    });

    program
}

/// A program read from text, against what a compiler knows.
fn read(text: &str) -> Program {
    crate::read(text, &crate::platform::Routines::builtin())
        .unwrap_or_else(|error| panic!("{error}\n{text}"))
}

/// Every program here and what it leaves with.
///
/// What a program answers is a fact about the program, so it is said here
/// rather than once per machine. A target is handed all of them and has to
/// answer the same as every other, which is the whole of what it means for
/// two targets to agree.
#[must_use]
pub fn running() -> Vec<(&'static str, Program, i32)> {
    let mut held = answers_built();
    held.extend(answers_written());
    held.extend(answers_counted());
    held.extend(answers_leaving());
    held.extend(answers_tagged());
    held.extend(arithmetic_cases());
    held.push(("a runtime guard exits early", rejected_count(), 7));
    held
}

/// The ones built here, which are what the language has no spelling for.
fn answers_built() -> Vec<(&'static str, Program, i32)> {
    vec![
        ("two and two", two_and_two(), 4),
        ("a long arm first", a_branch_over_a_long_arm(40, true), 40),
        ("a long arm last", a_branch_over_a_long_arm(40, false), 40),
        ("a global", counts_in_a_global(), 3),
        ("eight bits", wraps_at_eight_bits(), 4),
        ("values across a call", values_survive_a_call(), 45),
        ("a comparison", compares_two_worked_out_values(), 1),
        ("a flag it read", branches_on_a_flag_it_read(), 7),
        ("a total into an arm", carries_a_total_into_an_arm(3), 3),
    ]
}

/// And the ones written, which are what it does.
fn answers_written() -> Vec<(&'static str, Program, i32)> {
    vec![
        (
            "exit zero",
            read(
                "type Nat Zero Succ(Nat)

                  main!(h) -> exit!(h Zero)",
            ),
            0,
        ),
        (
            "a status it was told",
            read(
                "type Nat Zero Succ(Nat)

                  main!(h) -> exit!(h Succ(Succ(Succ(Zero))))",
            ),
            3,
        ),
        (
            "a name that leaves",
            read(
                "type Nat Zero Succ(Nat)

                  die!(h n) -> exit!(h n)

                  main!(h) -> die!(h Succ(Succ(Zero)))",
            ),
            2,
        ),
        (
            "a tag from a count",
            read(
                "type Nat Succ(Nat) Zero
                  type Bool True False

                  count(False) -> Zero
                  count(True) -> Succ(Zero)

                  main!(h) -> exit!(h count(True))",
            ),
            1,
        ),
    ]
}

/// The rest of them, arithmetic and what the world handed over.
fn answers_counted() -> Vec<(&'static str, Program, i32)> {
    vec![
        (
            "how many arguments",
            read(
                "type Nat Zero Succ(Nat)

                  add(a Zero) -> a
                  add(a Succ(k)) -> Succ(add(a k))

                  type Bool False True
                  less_than(Zero Zero) -> False
                  less_than(Zero Succ(b)) -> True
                  less_than(Succ(a) Zero) -> False
                  less_than(Succ(a) Succ(b)) -> less_than(a b)
                  bounded!(h True n) -> n
                  bounded!(h False n) -> exit!(h Zero)

                  main!(h) ->
                    count = argc!(h)
                    n = bounded!(h less_than(count Succ(Succ(Zero))) count)
                    exit!(h add(n n))",
            ),
            2,
        ),
        (
            "two and two from text",
            read(
                "type Nat Zero Succ(Nat)

                  add(a Zero) -> a
                  add(a Succ(k)) -> Succ(add(a k))

                  main!(h) -> exit!(h add(Succ(Succ(Zero)) Succ(Succ(Zero))))",
            ),
            4,
        ),
    ]
}

/// An arm that leaves, reached and not reached. What the other arms answer
/// is not measured against one that never comes back.
fn answers_leaving() -> Vec<(&'static str, Program, i32)> {
    let mut held = Vec::new();
    let leaving = "type Nat Zero Succ(Nat)

                   pick!(h Zero) -> exit!(h Succ(Zero))
                   pick!(h Succ(k)) -> k

                   main!(h) ->
                     held = pick!(h WHICH)
                     exit!(h Succ(held))";
    held.push((
        "an arm that comes back",
        read(&leaving.replace("WHICH", "Succ(Succ(Zero))")),
        2,
    ));
    held.push((
        "an arm that leaves",
        read(&leaving.replace("WHICH", "Zero")),
        1,
    ));
    held
}

/// A tag read back as the constructor it is, and two columns matched at
/// once. Subtraction stops at nought rather than wrapping, which is what
/// the second column buys: the arm for `Succ(m) Zero` is the one saying so.
fn answers_tagged() -> Vec<(&'static str, Program, i32)> {
    let mut held = Vec::new();
    let ordering = "type Nat Zero Succ(Nat)
                    type Order Lt Eq Gt

                    rank(Lt) -> Zero
                    rank(Eq) -> Succ(Zero)
                    rank(Gt) -> Succ(Succ(Zero))

                    pick(Zero) -> Lt
                    pick(Succ(k)) -> Gt

                    main!(h) -> exit!(h rank(pick(WHICH)))";
    for (which, answer) in [("Zero", 0), ("Succ(Zero)", 2)] {
        held.push(("a tag", read(&ordering.replace("WHICH", which)), answer));
    }

    let arithmetic = "type Nat Zero Succ(Nat)
                      type Order Lt Eq Gt

                      sub(Zero b) -> Zero
                      sub(Succ(m) Zero) -> Succ(m)
                      sub(Succ(m) Succ(n)) -> sub(m n)

                      cmp(Zero Zero) -> Eq
                      cmp(Zero Succ(n)) -> Lt
                      cmp(Succ(m) Zero) -> Gt
                      cmp(Succ(m) Succ(n)) -> cmp(m n)

                      rank(Lt) -> Zero
                      rank(Eq) -> Succ(Zero)
                      rank(Gt) -> Succ(Succ(Zero))

                      three(n) -> Succ(Succ(Succ(n)))

                      main!(h) -> exit!(h ANSWER)";
    for (answer, want) in [
        ("sub(three(Zero) Succ(Zero))", 2),
        ("sub(Succ(Zero) three(Zero))", 0),
        ("rank(cmp(Succ(Zero) three(Zero)))", 0),
        ("rank(cmp(three(Zero) three(Zero)))", 1),
        ("rank(cmp(three(Zero) Succ(Zero)))", 2),
    ] {
        held.push((
            "two columns",
            read(&arithmetic.replace("ANSWER", answer)),
            want,
        ));
    }
    held
}

fn rejected_count() -> Program {
    let library = include_str!("../../../standard/nat.fn");
    let source = format!(
        "{library}\n
        bounded!(h True n) -> n
        bounded!(h False n) -> exit!(h Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))))
        main!(h) ->
            count = argc!(h)
            n = bounded!(h less_than(count Succ(Zero)) count)
            exit!(h n)"
    );
    read(&source)
}

/// Runtime arithmetic: the count cannot fold, and the guard is what makes
/// its subsequent arithmetic fit even on the smallest target.
#[must_use]
pub fn arithmetic_cases() -> Vec<(&'static str, Program, i32)> {
    let library = include_str!("../../../standard/nat.fn");
    let setup = "
        bounded!(h True n) -> n
        bounded!(h False n) -> exit!(h Zero)
        four(n) -> Succ(Succ(Succ(Succ(n))))
        rank(False) -> Zero
        rank(True) -> Succ(Zero)
        main!(h) ->
            count = argc!(h)
            n = bounded!(h less_than(count Succ(Succ(Zero))) count)
            a = add(n four(four(Zero)))
            b = Succ(n)
            z = sub(n n)
            exit!(h ANSWER)";
    [
        ("runtime addition", "add(a b)", 11),
        ("runtime monus", "sub(a b)", 7),
        ("runtime underflow", "sub(b a)", 0),
        ("runtime multiplication", "mul(a b)", 18),
        ("runtime division", "div(a b)", 4),
        ("runtime remainder", "mod(a b)", 1),
        ("runtime division by zero", "div(a z)", 0),
        ("runtime remainder by zero", "mod(a z)", 9),
        ("runtime less than", "rank(less_than(b a))", 1),
        ("runtime equality", "rank(equals(a a))", 1),
        ("runtime inequality", "rank(equals(a b))", 0),
    ]
    .into_iter()
    .map(|(name, answer, want)| {
        let source = format!("{library}\n{}", setup.replace("ANSWER", answer));
        (name, read(&source), want)
    })
    .collect()
}

/// Every program here that writes, and what it writes.
#[must_use]
pub fn printing() -> Vec<(&'static str, Program, String)> {
    vec![
        ("hello world", hello_world(), "Hello, World!\n".to_owned()),
        (
            "a computed length",
            writes_a_length_it_worked_out(),
            "hi\n".to_owned(),
        ),
        (
            "writing the heap",
            writes_from_the_heap(),
            "hi\n".to_owned(),
        ),
        (
            "ticks",
            counts_down_before_it_branches(3),
            "tick\n".repeat(3),
        ),
    ]
}
