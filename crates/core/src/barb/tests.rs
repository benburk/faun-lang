use super::*;

/// `Nat`, `U8`, and `List_U8`, which between them reach every case the
/// encoding has.
pub(super) fn types() -> (Program, TypeId, TypeId, TypeId) {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let byte = program.declare_type("U8");
    program.define_type(byte, &[("Zero", &[]), ("Succ", &[byte])]);
    let list = program.declare_type("List_U8");
    program.define_type(list, &[("Nil", &[]), ("Cons", &[byte, list])]);
    (program, nat, byte, list)
}

pub(super) fn nat(program: &Program, id: TypeId, value: u64) -> Value {
    let mut term = Value(program.ctor_at(id, 0), Vec::new());
    for _ in 0..value {
        term = Value(program.ctor_at(id, 1), vec![term]);
    }
    term
}

#[test]
fn a_spine_is_recognised_and_a_branching_type_is_not() {
    let (mut program, nat, _, list) = types();
    assert!(matches!(shape(&program, nat), Shape::Spine { .. }));
    assert!(matches!(shape(&program, list), Shape::Spine { .. }));

    let tree = program.declare_type("Tree");
    program.define_type(tree, &[("Leaf", &[]), ("Node", &[tree, tree])]);
    assert_eq!(shape(&program, tree), Shape::Tagged, "two recursive fields");

    let extra = program.declare_type("Three");
    program.define_type(extra, &[("A", &[]), ("B", &[extra]), ("C", &[])]);
    assert_eq!(shape(&program, extra), Shape::Tagged, "a third constructor");
}

#[test]
fn runtime_shapes_distinguish_sequences_from_other_spines_and_aggregates() {
    let (mut program, nat, byte, list) = types();
    assert!(matches!(
        type_shape(&program, nat),
        TypeShape::Natural { .. }
    ));
    assert!(matches!(
        type_shape(&program, list),
        TypeShape::Sequence { element, .. } if element == byte
    ));

    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let unit = program.declare_type("Unitish");
    program.define_type(unit, &[("Only", &[])]);
    let wrapper = program.declare_type("Wrapped");
    program.define_type(wrapper, &[("Wrap", &[nat])]);
    let product = program.declare_type("Pair");
    program.define_type(product, &[("Pair", &[nat, nat])]);
    let enumeration = program.declare_type("Choice");
    program.define_type(enumeration, &[("Left", &[]), ("Right", &[])]);
    let sum = program.declare_type("Maybe");
    program.define_type(sum, &[("None", &[]), ("Some", &[nat])]);
    let wide = program.declare_type("WideSpine");
    program.define_type(wide, &[("Push", &[wide, nat, nat]), ("Empty", &[])]);

    assert_eq!(type_shape(&program, empty), TypeShape::Uninhabited);
    assert!(matches!(type_shape(&program, unit), TypeShape::Unit { .. }));
    assert!(matches!(
        type_shape(&program, wrapper),
        TypeShape::Wrapper { field, .. } if field == nat
    ));
    assert!(matches!(
        type_shape(&program, product),
        TypeShape::Product { .. }
    ));
    assert_eq!(type_shape(&program, enumeration), TypeShape::Enumeration);
    assert_eq!(type_shape(&program, sum), TypeShape::Sum);
    assert!(matches!(
        type_shape(&program, wide),
        TypeShape::Spine { .. }
    ));
}

#[test]
fn addition_is_recognised_and_its_near_miss_is_not() {
    let program = crate::programs::two_and_two_in_barb();
    let facts = analyzed(&program);
    let add = FnId::at(0);
    assert_eq!(program.name(program.function(add).name), "add");
    assert_eq!(facts.operation(add), Some(Operation::Add));
    assert_eq!(
        facts.operation(FnId::at(1)),
        None,
        "main takes no arguments"
    );

    // The same shape, answering the argument it counted down rather than the
    // one it kept. That is the identity on its second argument, not addition.
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let wrong = program.declare("wrong", &[nat, nat], nat);
    program.define(wrong, |b, args| {
        let right = args[1];
        b.match_(right, nat, |b, ctor, fields| match fields {
            [] => right,
            [k] => {
                let rest = b.call(wrong, &[args[0], *k]);
                b.con(ctor, &[rest])
            }
            _ => unreachable!("Nat takes at most one field"),
        })
    });
    assert_eq!(analyzed(&program).operation(wrong), None);
}

/// Recognized arithmetic works on the compact magnitude, not the unary tree.
#[test]
fn large_arithmetic_does_not_expand_constructor_spines() {
    let mut program = Program::default();
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

    let held = |magnitude| {
        let mut program = program.clone();
        let number = program.intern_number(nat, magnitude).unwrap();
        let main = program.declare("main", &[], nat);
        program.define(main, |b, _| {
            let value = b.known(number);
            b.call(add, &[value, value])
        });
        program.set_entry(main);
        fold(&mut program);
        program.render()
    };

    // Small enough to work out: what is left is the answer, and nothing to
    // work it out with.
    let small = held(3);
    assert!(small.contains("\n  6\n"), "{small}");
    assert!(!small.contains("add(v0, v0)"), "{small}");

    let large = held(4_000_000);
    assert!(large.contains("\n  8000000\n"), "{large}");
    assert!(!large.contains("add(v0, v0)"), "{large}");
}

/// Constructor distances survive partial reconstruction: the recursive value
/// below removes two constructors and puts one back.
#[test]
fn size_change_accepts_reconstructed_subterms() {
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

    validate(&program).expect("two constructors taken and one rebuilt is a decrease");
}

/// Weak arithmetic bounds are not strict decreases. Dividing by one and
/// taking a remainder with zero therefore cannot disguise an unchanged
/// recursive argument.
#[test]
fn size_change_rejects_non_decreasing_arithmetic() {
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
    let refused = validate(p).unwrap_err();
    assert!(
        refused
            .message
            .contains("nothing here shows `stall`, `stall_mod` stops"),
        "{refused}"
    );
}

/// Monus of two positives is below its dividend, so `m - 1` descends where
/// `m` was matched as a successor; monus by nought does not.
#[test]
fn size_change_reads_monus_of_positives_as_a_decrease() {
    let refusal = |subtrahend: u64| {
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
        validate(p).err()
    };
    assert!(refusal(1).is_none(), "{:?}", refusal(1));
    let refused = refusal(0).expect("monus by nought is no decrease");
    assert!(
        refused.message.contains("nothing here shows `count` stops"),
        "{refused}"
    );
}

/// Names that go round together are one round, however many of them there
/// are and whichever of them is reached first. What every definition in one
/// reaches is every other, so a round is found the way a program's calls
/// make it rather than by asking each pair in turn.
#[test]
fn a_round_is_every_name_that_goes_round_together() {
    // Three deep, taking a part each time round, which stops.
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
    validate(p).expect("a round that takes something apart");

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
    let refused = validate(p).unwrap_err();
    assert!(
        refused.message.contains("`one`, `two`, `three` stops"),
        "{refused}"
    );
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

/// Size-change termination follows each repeatable path rather than demanding
/// that one argument decrease at every recursive call site.
#[test]
fn size_change_accepts_descent_on_alternative_arguments() {
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

    validate(&program).expect("each path through merge descends on one list");
}

/// A decrease somewhere in a matrix is not enough: only a strict diagonal in
/// every idempotent composition proves that repeated calls run out.
#[test]
fn size_change_rejects_an_unchanged_permutation() {
    let (mut program, nat, _, _) = types();
    let swap = program.declare("swap", &[nat, nat], nat);
    program.define(swap, |b, args| b.call(swap, &[args[1], args[0]]));
    program.set_entry(swap);

    let refused = validate(&program).unwrap_err();
    assert!(
        refused.message.contains("nothing here shows `swap` stops"),
        "{refused}"
    );
}
