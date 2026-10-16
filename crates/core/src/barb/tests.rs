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
    let facts = program.analyze();
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
    assert_eq!(program.analyze().operation(wrong), None);
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

/// Nothing asks whether a definition stops: one going round on what it was
/// handed, which never comes back, is a program all the same.
#[test]
fn a_definition_that_never_stops_is_valid() {
    let (mut program, nat, _, _) = types();
    let swap = program.declare("swap", &[nat, nat], nat);
    program.define(swap, |b, args| b.call(swap, &[args[1], args[0]]));
    program.set_entry(swap);

    validate(&program).expect("stopping is not asked");
}

/// Names that go round together are one round, however many of them there
/// are and whichever of them is reached first, and each is read after what
/// it calls but those it goes round with. Of a round of three calling each
/// other in a ring, one is kept whole so the other two may be copied in.
#[test]
fn a_round_is_every_name_that_goes_round_together() {
    // one(n) -> two(n), two(n) -> three(n), three(n) -> one(n), and a
    // main calling one.
    let mut lib = fixture::Library::new();
    let nat = lib.nat;
    let p = &mut lib.program;
    let round = ["one", "two", "three"].map(|name| p.declare(name, &[nat], nat));
    for (at, &id) in round.iter().enumerate() {
        let next = round[(at + 1) % round.len()];
        p.define(id, |b, args| b.call(next, &[args[0]]));
    }
    let main = p.declare("main", &[nat], nat);
    p.define(main, |b, args| b.call(round[0], &[args[0]]));
    p.set_entry(main);

    let order = calls::callees_first(p);
    let at = |id: FnId| order.iter().position(|&held| held == id).unwrap();
    assert!(round.iter().all(|&id| at(id) < at(main)), "{order:?}");

    let breakers = calls::breakers(p);
    let kept = round.iter().filter(|id| breakers[id.index()]).count();
    assert_eq!(kept, 1, "{breakers:?}");
    assert!(!breakers[main.index()]);
}
