use super::evaluate::{Budget, Evaluator, Held};

fn budget(work: u64) -> Budget {
    Budget::new(FoldLimits {
        work,
        max_depth: 512,
        ..FoldLimits::default()
    })
}
use super::*;
use num_bigint::BigUint;

const LIBRARY: &str = include_str!("../../../../standard/nat.fn");

fn source(library: &str) -> Program {
    crate::surface::parse(
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
fn number(owner: TypeId, n: u64) -> Held {
    let mut bytes = vec![];
    constant::write_natural(&BigUint::from(n), &mut bytes);
    Held { owner, bytes }
}

#[test]
fn library_equations_are_recognized_before_and_after_folding() {
    let mut program = source(LIBRARY);
    validate(&program).unwrap();
    for _ in 0..2 {
        let facts = recognise(&program);
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
        recognise(&program).operation(named(&program, "plus")),
        Some(Operation::Add)
    );
    assert_eq!(
        recognise(&program).operation(named(&program, "mod")),
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
            recognise(&program).operation(named(&program, name)),
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
                let args = vec![Some(number(ty, a)), Some(number(ty, b))];
                let body = program.function(id).body.unwrap();
                let baseline = Evaluator {
                    program: &program,
                    operations: &unknown,
                }
                .body(body, args.clone(), &mut budget(1_000_000))
                .unwrap_or_else(|| panic!("baseline budget for {name}({a}, {b})"));
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
                .body(caller.function(test).body.unwrap(), args, &mut budget(1000))
                .unwrap();
                assert_eq!(baseline.owner, fast.owner);
                assert_eq!(baseline.bytes, fast.bytes, "{name}({a}, {b})");
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
    let value = program.intern_natural(ty, &n);
    let test = program.declare("huge", &[], ty);
    program.define(test, |b, _| {
        let n = b.known(ty, value);
        b.call(mul, &[n, n])
    });
    fold(&mut program);
    let Expr::Static(owner, value) = program.expr(program.function(test).body.unwrap().tail) else {
        panic!("not folded")
    };
    assert_eq!(
        as_natural(&program, owner, program.known_bytes(value)),
        Some(&n * &n)
    );
    assert!(as_number(&program, owner, program.known_bytes(value)).is_none());
    assert!(program.render().contains(&(&n * &n).to_string()));
}

#[test]
fn an_early_exit_refines_the_continuation() {
    let routines = crate::platform::Routines::builtin();
    let text = format!(
        "{LIBRARY}\nbounded!(h True n) -> n\nbounded!(h False n) -> exit!(h Zero)\nmain!(h) -> count = argc!(h) n = bounded!(h less_than(count Succ(Succ(Zero))) count) exit!(h add(n n))"
    );
    let mut program = crate::surface::parse(&text, &routines).unwrap();
    normalize(&mut program);
    fold(&mut program);
    let facts = recognise(&program);
    let body = program.function(program.entry().unwrap()).body.unwrap();
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
        program.function(id).body.unwrap(),
        vec![Some(number(ty, 1_000_000))],
        &mut budget(32),
    );
    assert!(result.is_none());
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
