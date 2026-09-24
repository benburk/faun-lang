use super::budget::Budget;
use super::constant::Held;
use super::evaluate::{CannotFold, Evaluator};

fn budget(work: u64) -> Budget {
    Budget::new(FoldLimits {
        work,
        max_depth: 512,
        ..FoldLimits::default()
    })
}
use super::*;
use num_bigint::BigUint;

const LIBRARY: &str = include_str!("../../../../crates/simple/standard/nat.fn");

fn source(library: &str) -> Program {
    crate::simple::parse(
        &format!("{library}\nmain!(h) -> exit!(h Zero)"),
        &crate::platform::Routines::builtin(),
    )
    .unwrap()
}
fn named(program: &Program, name: &str) -> FnId {
    FnId::at(
        program
            .functions()
            .iter()
            .position(|f| program.name(f.name) == name)
            .unwrap(),
    )
}
fn number(program: &Program, owner: TypeId, n: u64) -> Held {
    Held::number(program.type_info(), owner, &BigUint::from(n))
}

#[test]
fn library_equations_are_recognized_before_and_after_folding() {
    let mut program = source(LIBRARY);
    validate(&program).unwrap();
    for _ in 0..2 {
        let facts = analyze(&program);
        for (name, op) in [
            ("add", Operation::Add),
            ("sub", Operation::Monus),
            ("mul", Operation::Mul),
            ("div", Operation::Div),
            ("mod", Operation::Mod),
        ] {
            assert_eq!(
                facts.operation(named(&program, name)),
                Some(op),
                "{name}\n{}",
                program.render()
            );
        }
        assert!(matches!(
            facts.operation(named(&program, "equals")),
            Some(Operation::Equals { .. })
        ));
        assert!(matches!(
            facts.operation(named(&program, "less_than")),
            Some(Operation::LessThan { .. })
        ));
        fold(&mut program);
    }
}

#[test]
fn recognition_is_structural_and_zero_divisor_near_misses_are_not_operations() {
    let library = LIBRARY
        .replace("Nat", "Count")
        .replace("Zero Succ(Count)", "Succ(Count) Zero")
        .replace("False True", "True False")
        .replace("add", "plus");
    let program = source(&library);
    assert_eq!(
        analyze(&program).operation(named(&program, "plus")),
        Some(Operation::Add)
    );
    assert_eq!(
        analyze(&program).operation(named(&program, "mod")),
        Some(Operation::Mod)
    );
    for (old, new, name) in [
        ("div(a Zero) -> Zero", "div(a Zero) -> a", "div"),
        ("mod(a Zero) -> a", "mod(a Zero) -> Zero", "mod"),
        ("sub(Zero b) -> Zero", "sub(Zero b) -> b", "sub"),
        ("mul(a Zero) -> Zero", "mul(a Zero) -> a", "mul"),
        (
            "equals(Zero Succ(b)) -> False",
            "equals(Zero Succ(b)) -> True",
            "equals",
        ),
    ] {
        let program = source(&LIBRARY.replace(old, new));
        assert_eq!(
            analyze(&program).operation(named(&program, name)),
            None,
            "{name}"
        );
    }
}

#[test]
fn structural_evaluation_matches_arithmetic_for_small_inputs() {
    let program = source(LIBRARY);
    let operations = arithmetic::recognise(&program);
    let unknown = vec![None; program.functions().len()];
    for name in ["add", "sub", "mul", "div", "mod", "equals", "less_than"] {
        let id = named(&program, name);
        let ty = program.params(id)[0];
        for a in 0..12 {
            for b in 0..8 {
                let args = vec![Ok(number(&program, ty, a)), Ok(number(&program, ty, b))];
                let body = program.function(id).body().unwrap();
                let baseline = Evaluator {
                    program: &program,
                    operations: &unknown,
                }
                .body(body, args.clone(), &mut budget(1_000_000))
                .unwrap_or_else(|reason| panic!("baseline {name}({a}, {b}): {reason:?}"));
                // Evaluate a call so the recognized fast path is exercised at
                // the root too, including zero-divisor and comparison cases.
                let mut caller = program.clone();
                let test = caller.declare("test", &[ty, ty], caller.function(id).result);
                caller.define(test, |builder, args| builder.call(id, args));
                let mut ops = operations.clone();
                ops.push(None);
                let fast = Evaluator {
                    program: &caller,
                    operations: &ops,
                }
                .body(
                    caller.function(test).body().unwrap(),
                    args,
                    &mut budget(1000),
                )
                .unwrap();
                assert_eq!(baseline.owner(), fast.owner());
                assert_eq!(baseline.encoded(), fast.encoded(), "{name}({a}, {b})");
            }
        }
    }
}

#[test]
fn folded_values_are_not_limited_to_u64() {
    let mut program = source(LIBRARY);
    let mul = named(&program, "mul");
    let ty = program.params(mul)[0];
    let n = BigUint::from(1u8) << 100usize;
    let value = program.intern_natural(ty, &n).unwrap();
    let test = program.declare("huge", &[], ty);
    program.define(test, |b, _| {
        let n = b.known(value);
        b.call(mul, &[n, n])
    });
    fold(&mut program);
    let Expr::Static(value) = program.expr(program.function(test).body().unwrap().tail) else {
        panic!("not folded")
    };
    let ConstantView::Natural(number) = program.constant(value).view() else {
        panic!("a natural");
    };
    assert_eq!(number.to_biguint(), &n * &n);
    assert_eq!(number.try_u64(), Err(TooWide));
    assert!(program.render().contains(&(&n * &n).to_string()));
}

#[test]
fn an_early_exit_refines_the_continuation() {
    let routines = crate::platform::Routines::builtin();
    let text = format!(
        "{LIBRARY}\nbounded!(h True n) -> n\nbounded!(h False n) -> exit!(h Zero)\nmain!(h) -> count = argc!(h) n = bounded!(h less_than(count Succ(Succ(Zero))) count) exit!(h add(n n))"
    );
    let mut program = crate::simple::parse(&text, &routines).unwrap();
    normalize_with_limits(&mut program, InlineLimits::default());
    fold(&mut program);
    let facts = analyze(&program);
    let body = program.function(program.entry().unwrap()).body().unwrap();
    let sum = program.bindings(body.bindings).iter().copied().find(|expr| {
        matches!(program.expr(*expr), Expr::Call(called, _) if facts.operation(called) == Some(Operation::Add))
    }).expect("runtime addition");
    assert_eq!(
        facts.held(sum),
        Bounds {
            low: 0,
            high: Some(2)
        }
    );
    let machine = crate::ir::lower(&program, &facts, &routines).unwrap();
    assert!(
        (0..machine.values_count())
            .all(|at| machine.class(crate::ir::ValueId::at(at)) != crate::ir::Class::Natural)
    );
}

#[test]
fn unrecognized_recursion_still_has_an_evaluation_budget() {
    let program = source(&format!(
        "{LIBRARY}\ncount(Zero) -> Zero\ncount(Succ(n)) -> count(n)"
    ));
    let id = named(&program, "count");
    let ty = program.params(id)[0];
    let operations = arithmetic::recognise(&program);
    assert_eq!(operations[id.index()], None);
    let result = Evaluator {
        program: &program,
        operations: &operations,
    }
    .body(
        program.function(id).body().unwrap(),
        vec![Ok(number(&program, ty, 1_000_000))],
        &mut budget(32),
    );
    assert_eq!(result.unwrap_err(), CannotFold::Limit(LimitExceeded::Work));
}

#[test]
fn range_propagation_observes_earlier_answers_in_the_same_round() {
    let (mut program, nat, _, _) = tests::types();
    let seven = program.intern_number(nat, 7).unwrap();
    let first = program.declare("first", &[], nat);
    program.define(first, |b, _| b.known(seven));
    let mut previous = first;
    // Longer than the round limit: moving the snapshot to a whole round
    // would lose precision here. Each walk reads the current result table.
    let mut chain = vec![first];
    for at in 0..64 {
        let id = program.declare(&format!("forward_{at}"), &[], nat);
        program.define(id, |b, _| b.call(previous, &[]));
        chain.push(id);
        previous = id;
    }
    program.set_entry(previous);
    validate(&program).unwrap();
    let facts = analyze(&program);
    for id in chain {
        assert_eq!(facts.answers(id), Bounds::at(7));
    }
}

#[test]
fn arithmetic_interval_bounds_contain_every_small_answer() {
    for a0 in 0..5 {
        for a1 in a0..6 {
            for b0 in 0..5 {
                for b1 in b0..6 {
                    let a = Bounds {
                        low: a0,
                        high: Some(a1),
                    };
                    let b = Bounds {
                        low: b0,
                        high: Some(b1),
                    };
                    for (op, bounds) in [
                        (Operation::Add, a.plus(b)),
                        (Operation::Monus, a.monus(b)),
                        (Operation::Mul, a.times(b)),
                        (Operation::Div, a.quotient(b)),
                        (Operation::Mod, a.remainder(b)),
                    ] {
                        for x in a0..=a1 {
                            for y in b0..=b1 {
                                let n = op.calculate(&BigUint::from(x), &BigUint::from(y)).unwrap();
                                assert!(n >= BigUint::from(bounds.low), "{op:?}: {a:?}, {b:?}");
                                assert!(
                                    bounds.high.is_none_or(|high| n <= BigUint::from(high)),
                                    "{op:?}: {a:?}, {b:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(Bounds::at(u64::MAX).plus(Bounds::at(1)).high, None);
    assert_eq!(Bounds::ANY.times(Bounds::at(0)), Bounds::at(0));
    assert_eq!(Bounds::ANY.remainder(Bounds::at(0)), Bounds::ANY);
    assert_eq!(Bounds::ANY.quotient(Bounds::at(0)), Bounds::at(0));
}

/// A sum taken modulo a power of two is worked out modulo that power of two
/// throughout, which is how a number counting without a last step says a
/// machine word.
#[test]
fn a_sum_modulo_a_power_of_two_is_a_sum_of_remainders() {
    // One side reduced, added to itself, and that reduced: both sides being
    // the same side, one remainder of it does for both.
    let held = reduced("mod(add(n n) two_fifty_six)");
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
    assert!(held.contains("add(v"), "{held}");

    // A side known before the program runs, and under the modulus, is
    // already every bit of itself the modulus keeps. Only the count takes a
    // remainder of its own; the constant is added as it stands, and wrapping
    // it in one would have the tier below reading a number widened to the
    // modulus and narrowed straight back.
    let held = reduced("mod(add(n four) two_fifty_six)");
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
    assert!(held.contains("add(v"), "{held}");

    // Under it is what buys that, not being known: one as big as the modulus
    // loses something to it, so it takes a remainder like anything else.
    let held = reduced("mod(add(n sixteen) sixteen)");
    assert_eq!(held.matches("mod(").count(), 3, "{held}");
}

/// A product too, for the same reason.
#[test]
fn a_product_modulo_a_power_of_two_is_a_product_of_remainders() {
    let held = reduced("mod(mul(n n) two_fifty_six)");
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
}

/// Not by anything else. Reducing each side first leaves three divisions
/// where there was one, and divides nothing away.
#[test]
fn a_sum_modulo_anything_else_is_left_as_it_stands() {
    let held = reduced("mod(add(n n) ten)");
    assert_eq!(held.matches("mod(").count(), 1, "{held}");
}

/// And not truncated subtraction, which stops at nought rather than
/// carrying through a remainder, nor the division or remainder themselves.
#[test]
fn only_what_carries_through_a_remainder_is_pushed_inside_one() {
    // Two different values, so that nothing collapses for being the same.
    for held in ["sub(n four)", "div(n four)", "mod(n four)"] {
        let rendered = reduced(&format!("mod({held} two_fifty_six)"));
        let wanted = usize::from(held.starts_with("mod")) + 1;
        assert_eq!(
            rendered.matches("mod(").count(),
            wanted,
            "{held}: {rendered}"
        );
    }
}

/// `main!` as the optimizer leaves it, for a program working `held` out of
/// the count it was handed.
fn reduced(held: &str) -> String {
    let source = format!(
        "{LIBRARY}
         main!(h) ->
           n = argc!(h)
           two = Succ(Succ(Zero))
           four = mul(two two)
           sixteen = mul(four four)
           two_fifty_six = mul(sixteen sixteen)
           ten = add(four add(four two))
           exit!(h {held})"
    );
    let program = crate::read_barb_with_options(
        &source,
        &crate::platform::Routines::builtin(),
        &OptimizeOptions::default(),
    )
    .expect("a program");
    let rendered = program.render();
    let (_, main) = rendered.split_once("main!(v0: Host)").expect("an entry");
    main.to_owned()
}

/// A field holds what was built into it: reading one back answers no more
/// than the values some construction put there.
#[test]
fn a_field_holds_what_was_built_into_it() {
    let mut program = Program::default();
    let order = program.declare_type("Order");
    program.define_type(order, &[("Lt", &[]), ("Eq", &[]), ("Gt", &[])]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[order, nat])]);
    let outcome = program.declare("outcome", &[pair], order);
    program.define(outcome, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[0])
    });
    let count = program.declare("count", &[pair], nat);
    program.define(count, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[1])
    });
    let (gt, zero) = (program.ctor_at(order, 2), program.ctor_at(nat, 0));
    let pair_ctor = program.ctor_at(pair, 0);
    let main = program.declare("main", &[], order);
    program.define(main, |b, _| {
        let fields = [b.con(gt, &[]), b.con(zero, &[])];
        let held = b.con(pair_ctor, &fields);
        b.call(count, &[held]);
        b.call(outcome, &[held])
    });
    program.set_entry(main);
    let facts = analyze(&program);
    assert_eq!(facts.answers(outcome), Bounds::at(2));
    assert_eq!(facts.answers(count), Bounds::at(0));
    assert_eq!(facts.field(&program, pair_ctor, 0), Bounds::at(2));
}

/// A value handed in at the entry was built out of sight, so its fields
/// could hold anything -- except that a field whose type is a run of bare
/// tags is still one of them: the type says that much alone.
#[test]
fn a_field_built_out_of_sight_is_known_only_by_its_type() {
    let mut program = Program::default();
    let order = program.declare_type("Order");
    program.define_type(order, &[("Lt", &[]), ("Eq", &[]), ("Gt", &[])]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[order, nat])]);
    let pair_ctor = program.ctor_at(pair, 0);
    let main = program.declare_named("main", &[("handed", pair)], order);
    program.define(main, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[0])
    });
    program.set_entry(main);
    let facts = analyze(&program);
    assert_eq!(
        facts.answers(main),
        Bounds {
            low: 0,
            high: Some(2)
        }
    );
    assert_eq!(facts.field(&program, pair_ctor, 1), Bounds::ANY);
}
