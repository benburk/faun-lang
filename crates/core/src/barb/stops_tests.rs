//! Which rounds of calls [`unproved`] shows stop, built with the builder.
//! A program the frontend writes reaches the same shapes; what is written
//! here is the least of each that says what is shown and what is not.

use super::tests::types;
use super::*;

/// The names of each round nothing shows stops, in the order written.
fn unshown(program: &Program) -> Vec<Vec<String>> {
    unproved(program)
        .iter()
        .map(|round| {
            round
                .functions
                .iter()
                .map(|&id| program.name(program.function(id).name).to_owned())
                .collect()
        })
        .collect()
}

/// Give `program` an entry answering `called(n)`.
fn enter(program: &mut Program, nat: TypeId, called: FnId, n: u64) {
    let n = program.intern_number(nat, n).unwrap();
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let n = b.known(n);
        b.call(called, &[n])
    });
    program.set_entry(main);
}

/// Constructor distances survive partial reconstruction: the recursive value
/// below removes two constructors and puts one back.
#[test]
fn two_constructors_taken_and_one_rebuilt_is_a_decrease() {
    let (mut program, nat, _, _) = types();
    let zero = program.ctor_at(nat, 0);
    let successor = program.ctor_at(nat, 1);
    let descend = program.declare("descend", &[nat], nat);
    program.define(descend, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            b.match_(fields[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(zero, &[])
                } else {
                    let predecessor = b.con(successor, &[fields[0]]);
                    b.call(descend, &[predecessor])
                }
            })
        })
    });
    program.set_entry(descend);

    assert!(unshown(&program).is_empty(), "{:?}", unshown(&program));
}

/// Weak arithmetic bounds are not strict decreases. Dividing by one and
/// taking a remainder with nought therefore cannot disguise an unchanged
/// recursive argument.
#[test]
fn dividing_by_one_and_a_remainder_by_nought_are_no_decrease() {
    let mut lib = fixture::Library::new();
    let (nat, zero, succ) = (lib.nat, lib.zero, lib.succ);
    let (div, modulo) = (lib.div, lib.modulo);
    let p = &mut lib.program;
    // stall(Zero) -> Zero
    // stall(Succ(n)) -> value = Succ(n) one = Succ(Zero) stall_mod(div(value, one))
    // stall_mod(n) -> zero = Zero stall(mod(n, zero))
    let stall = p.declare("stall", &[nat], nat);
    let stall_mod = p.declare("stall_mod", &[nat], nat);
    p.define(stall, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            let value = b.con(succ, &[fields[0]]);
            let nought = b.con(zero, &[]);
            let one = b.con(succ, &[nought]);
            let divided = b.call(div, &[value, one]);
            b.call(stall_mod, &[divided])
        })
    });
    p.define(stall_mod, |b, args| {
        let nought = b.con(zero, &[]);
        let remainder = b.call(modulo, &[args[0], nought]);
        b.call(stall, &[remainder])
    });
    enter(p, nat, stall, 0);
    assert_eq!(unshown(p), [["stall", "stall_mod"]]);
}

/// Monus of two positives is below its dividend, so `m - 1` descends where
/// `m` was matched as a successor; monus by nought does not.
#[test]
fn monus_of_positives_is_a_decrease_and_by_nought_is_not() {
    let unshown_by = |subtrahend: u64| {
        let mut lib = fixture::Library::new();
        let (nat, zero, succ, sub) = (lib.nat, lib.zero, lib.succ, lib.sub);
        let p = &mut lib.program;
        // count(Zero) -> Zero
        // count(Succ(n)) -> count(sub(Succ(n) subtrahend))
        let by = p.intern_number(nat, subtrahend).unwrap();
        let count = p.declare("count", &[nat], nat);
        p.define(count, |b, args| {
            b.match_(args[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                let value = b.con(succ, &[fields[0]]);
                let by = b.known(by);
                let less = b.call(sub, &[value, by]);
                b.call(count, &[less])
            })
        });
        enter(p, nat, count, 3);
        unshown(p)
    };
    assert!(unshown_by(1).is_empty(), "{:?}", unshown_by(1));
    assert_eq!(unshown_by(0), [["count"]]);
}

/// A round of three is shown to stop where it takes something apart each
/// time round, and reported whole, every name in it, where it goes round on
/// what it was handed.
#[test]
fn a_round_of_three_stops_where_each_takes_a_part() {
    // one(Zero) -> Zero    one(Succ(k)) -> two(k)
    // two(Zero) -> Zero    two(Succ(k)) -> three(k)
    // three(Zero) -> Zero  three(Succ(k)) -> one(k)
    let mut lib = fixture::Library::new();
    let (nat, zero) = (lib.nat, lib.zero);
    let p = &mut lib.program;
    let round = ["one", "two", "three"].map(|name| p.declare(name, &[nat], nat));
    for (at, &id) in round.iter().enumerate() {
        let next = round[(at + 1) % round.len()];
        p.define(id, |b, args| {
            b.match_(args[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(zero, &[])
                } else {
                    b.call(next, &[fields[0]])
                }
            })
        });
    }
    enter(p, nat, round[0], 3);
    assert!(unshown(p).is_empty(), "{:?}", unshown(p));

    // The same three, going round on what they were handed.
    // one(n) -> add(Zero two(n)), and so on round.
    let mut lib = fixture::Library::new();
    let (nat, zero, add) = (lib.nat, lib.zero, lib.add);
    let p = &mut lib.program;
    let round = ["one", "two", "three"].map(|name| p.declare(name, &[nat], nat));
    for (at, &id) in round.iter().enumerate() {
        let next = round[(at + 1) % round.len()];
        p.define(id, |b, args| {
            let nought = b.con(zero, &[]);
            let again = b.call(next, &[args[0]]);
            b.call(add, &[nought, again])
        });
    }
    enter(p, nat, round[0], 0);
    assert_eq!(unshown(p), [["one", "two", "three"]]);
}

/// Size-change termination follows each repeatable path rather than demanding
/// that one argument decrease at every recursive call site.
#[test]
fn each_way_round_may_descend_on_a_different_argument() {
    let (mut program, _, _, list) = types();
    let choice = program.declare_type("Choice");
    program.define_type(choice, &[("Left", &[]), ("Right", &[])]);

    let merge = program.declare("merge", &[list, list, choice], list);
    let left_choice = program.ctor_at(choice, 0);
    program.define(merge, |b, args| {
        let (left, right, choose) = (args[0], args[1], args[2]);
        b.match_(choose, choice, |b, ctor, _| {
            if ctor == left_choice {
                b.match_(left, list, |b, _, fields| match fields {
                    [] => right,
                    [_, tail] => b.call(merge, &[*tail, right, choose]),
                    _ => unreachable!("a list has zero or two fields"),
                })
            } else {
                b.match_(right, list, |b, _, fields| match fields {
                    [] => left,
                    [_, tail] => b.call(merge, &[left, *tail, choose]),
                    _ => unreachable!("a list has zero or two fields"),
                })
            }
        })
    });
    program.set_entry(merge);

    assert!(unshown(&program).is_empty(), "{:?}", unshown(&program));
}

/// A decrease somewhere in a matrix is not enough: only a strict diagonal in
/// every idempotent composition shows repeated calls run out.
#[test]
fn an_unchanged_permutation_is_no_decrease() {
    let (mut program, nat, _, _) = types();
    let swap = program.declare("swap", &[nat, nat], nat);
    program.define(swap, |b, args| b.call(swap, &[args[1], args[0]]));
    program.set_entry(swap);

    assert_eq!(unshown(&program), [["swap"]]);
}

/// Rebuilding what was taken apart hands on the same size, whichever
/// constructor it was, and a round reaching nothing outside is pure.
#[test]
fn rebuilding_what_was_taken_apart_is_no_decrease() {
    let mut library = fixture::Library::new();
    let (nat, zero, succ) = (library.nat, library.zero, library.succ);
    let program = &mut library.program;
    // forever(Zero) -> Succ(forever(Zero))
    // forever(Succ(n)) -> Succ(forever(Succ(n)))
    let forever = program.declare("forever", &[nat], nat);
    program.define(forever, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            let again = if ctor == zero {
                b.con(zero, &[])
            } else {
                b.con(succ, &[fields[0]])
            };
            let rest = b.call(forever, &[again]);
            b.con(succ, &[rest])
        })
    });
    enter(program, nat, forever, 0);
    let unproved = unproved(program);
    assert_eq!(unproved.len(), 1, "{unproved:?}");
    assert_eq!(unproved[0].functions, [forever]);
    assert!(unproved[0].pure);
}

/// What a way no value takes calls goes round on itself, and is not asked
/// whether it stops; a written definition doing the same is, and so is one
/// of that name answering a type with values, which nothing but a frontend
/// writing it as it does would have.
#[test]
fn only_the_way_no_value_takes_is_not_asked_whether_it_stops() {
    let unshown_as = |name: &str, empty: bool| {
        let (mut program, nat, _, list) = types();
        let nothing = program.declare_type("Empty");
        program.define_type(nothing, &[]);
        let answer = if empty { nothing } else { nat };
        let spin = program.declare(name, &[list], answer);
        program.define(spin, |b, args| b.call(spin, &[args[0]]));
        program.set_entry(spin);
        unshown(&program)
    };
    assert!(unshown_as(UNREACHED, true).is_empty());
    assert_eq!(unshown_as("unreachable", true), [["unreachable"]]);
    assert_eq!(unshown_as(UNREACHED, false), [[UNREACHED]]);
}

/// A walk handing on its rest with an element written over goes round on
/// something shorter, as an element written over leaves a list as long as
/// it was; with one appended, as long as it was, it does not.
#[test]
fn an_element_written_over_keeps_a_length_and_one_appended_adds_one() {
    let unshown_by = |appending: bool| {
        let (mut program, nat, byte, list) = types();
        let (nil, cons) = (program.ctor_at(list, 0), program.ctor_at(list, 1));
        let reverse = sequence::write_reverse_onto(&mut program, list);
        let prepend = sequence::write_prepend(&mut program, list, reverse);
        let append = sequence::write_append(&mut program, list, byte, prepend);
        let replace = sequence::write_replace(&mut program, list, nat);
        let nought = program.intern_number(nat, 0).unwrap();
        // walk(Nil) -> Nil
        // walk(Cons(x, rest)) -> walk(append(rest, x)) or walk(replace(rest, 0, x))
        let walk = program.declare("walk", &[list], list);
        program.define(walk, |b, args| {
            b.match_(args[0], list, |b, ctor, fields| {
                if ctor == nil {
                    return b.con(nil, &[]);
                }
                debug_assert_eq!(ctor, cons);
                let (head, rest) = (fields[0], fields[1]);
                let handed = if appending {
                    b.call(append, &[rest, head])
                } else {
                    let at = b.known(nought);
                    b.call(replace, &[rest, at, head])
                };
                b.call(walk, &[handed])
            })
        });
        program.set_entry(walk);
        unshown(&program)
    };
    assert!(unshown_by(false).is_empty(), "{:?}", unshown_by(false));
    assert_eq!(unshown_by(true), [["walk"]]);
}
