use super::*;
use num_bigint::BigUint;

#[test]
fn unknown_or_overflowing_bounds_never_choose_a_machine_word() {
    for magnitude in [BigUint::from(u64::MAX), BigUint::from(1u8) << 100usize] {
        let mut source = crate::programs::two_and_two_in_barb();
        let add = barb::FnId::at(0);
        let nat = source.params(add)[0];
        let value = source.intern_natural(nat, &magnitude).unwrap();
        let zero = source.intern_number(nat, 0).unwrap();
        source.define(source.entry(), |b, _| {
            let n = b.known(value);
            let sum = b.call(add, &[n, n]);
            b.match_(sum, nat, |b, _, _| b.known(zero))
        });
        let machine = lower(&source, &crate::platform::Routines::builtin()).unwrap();
        let body = machine.function(machine.entry()).body().unwrap();
        assert!(machine.walk(body).any(|(op, results)| {
            matches!(
                op,
                Op::Binary {
                    op: Binary::Add,
                    ..
                }
            ) && machine.class(results[0]) == Class::Natural
        }));
        if magnitude.bits() > 64 {
            assert!(
                machine
                    .every(body)
                    .any(|op| matches!(op, Op::NaturalConstant(_)))
            );
        }
    }
}

#[test]
fn an_unbounded_entry_result_is_not_silently_truncated() {
    let mut source = crate::programs::two_and_two_in_barb();
    let nat = source.params(barb::FnId::at(0))[0];
    let value = source
        .intern_natural(nat, &(BigUint::from(1u8) << 100usize))
        .unwrap();
    source.define(source.entry(), |b, _| b.known(value));
    let error = lower(&source, &crate::platform::Routines::builtin()).unwrap_err();
    assert!(error.contains("unbounded"), "{error}");
}

#[test]
fn a_natural_constant_is_compact_and_does_not_alias_a_word() {
    let (mut program, main) = Program::new("main");
    let magnitude = BigUint::from(1u8) << 200usize;
    program.define(main, |b, _| {
        let value = b.natural(&magnitude);
        assert_eq!(b.class(value), Class::Natural);
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    assert_eq!(program.data(), magnitude.to_bytes_le());
    assert!(!Class::Natural.fits(Class::Word));
    assert!(!Class::Word.fits(Class::Natural), "promotion is explicit");
    validate(&program).unwrap();
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "build, lower and inspect each operation's program"
)]
fn runtime_arithmetic_survives_barb_lowering_as_operations() {
    let routines = crate::platform::Routines::builtin();
    for (name, expected) in [
        ("sub", Binary::Monus),
        ("mul", Binary::Mul),
        ("div", Binary::Div),
        ("mod", Binary::Mod),
    ] {
        let mut library = barb::fixture::Library::new();
        let operation = match expected {
            Binary::Monus => library.sub,
            Binary::Mul => library.mul,
            Binary::Div => library.div,
            _ => library.modulo,
        };
        let (nat, less_than) = (library.nat, library.less_than);
        let two = library.number(2);
        let world = tests::host(&mut library.program, nat);
        let bounded = tests::bounded(&mut library, &world);
        let program = &mut library.program;
        let main = program.declare_named("main!", &[("host", world.host)], world.never);
        program.define(main, |b, args| {
            let count = b.call(world.input, &[args[0]]);
            let two = b.known(two);
            let small = b.call(less_than, &[count, two]);
            let n = b.call(bounded, &[args[0], small, count]);
            let answer = b.call(operation, &[n, n]);
            b.call(world.exit, &[args[0], answer])
        });
        program.set_entry(main);
        barb::validate(program).unwrap();
        // Isolate lowering from laws such as mod(n, n) = 0.
        barb::test_support::structural(program);
        barb::test_support::normalize_with_limits(program, barb::InlineLimits::default());
        barb::test_support::fold(program);
        let machine = crate::lower_to_machine_ir(program, &routines).unwrap();
        validate(&machine).unwrap();
        let body = machine.function(machine.entry()).body().unwrap();
        assert!(
            machine
                .every(body)
                .any(|op| matches!(op, Op::Binary { op, .. } if *op == expected)),
            "{name}"
        );
        assert!(
            !machine.every(body).any(|op| matches!(op, Op::Loop { .. })),
            "{name} must not become a portable value-counting loop"
        );
        assert_eq!(
            machine
                .every(body)
                .filter(|op| matches!(op, Op::If { .. }))
                .count(),
            1,
            "{name}: only the count's guard branches; a monus needs none of its own"
        );
        assert!(
            (0..machine.values_count())
                .all(|index| machine.class(ValueId::at(index)) != Class::Natural)
        );
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "the guard, its entry and the lowering check are one program"
)]
fn an_early_exit_refines_the_continuation() {
    let routines = crate::platform::Routines::builtin();
    let mut library = barb::fixture::Library::new();
    let two = library.number(2);
    let nought = library.number(0);
    let (nat, bool_, true_) = (library.nat, library.bool_, library.true_);
    let (add, less_than) = (library.add, library.less_than);
    let p = &mut library.program;
    let host = p.declare_type("Host");
    p.define_type(host, &[("Host", &[])]);
    let never = p.declare_type("Never");
    p.define_type(never, &[]);
    let exit = p.declare("exit!", &[host, nat], never);
    let input = p.declare("read_byte!", &[host], nat);
    // bounded!(h, True, n) -> n
    // bounded!(h, False, n) -> exit!(h, Zero)
    let bounded = p.declare("bounded!", &[host, bool_, nat], nat);
    p.define(bounded, |b, args| {
        b.match_(args[1], bool_, |b, ctor, _| {
            if ctor == true_ {
                args[2]
            } else {
                let nought = b.known(nought);
                b.call(exit, &[args[0], nought])
            }
        })
    });
    let main = p.declare_named("main!", &[("host", host)], never);
    p.define(main, |b, args| {
        let count = b.call(input, &[args[0]]);
        let two = b.known(two);
        let below = b.call(less_than, &[count, two]);
        let n = b.call(bounded, &[args[0], below, count]);
        let sum = b.call(add, &[n, n]);
        b.call(exit, &[args[0], sum])
    });
    p.set_entry(main);
    let mut program = library.program;
    barb::validate(&program).unwrap();
    barb::test_support::normalize_with_limits(&mut program, barb::InlineLimits::default());
    barb::test_support::fold(&mut program);
    let facts = program.analyze();
    let body = program.function(program.entry()).body().unwrap();
    let sum = program.bindings(body.bindings).iter().copied().find(|expr| {
        matches!(program.expr(*expr), barb::Expr::Call(called, _) if facts.operation(called) == Some(barb::Operation::Add))
    }).expect("runtime addition");
    assert_eq!(
        facts.held(sum),
        barb::Bounds {
            low: 0,
            high: Some(2)
        }
    );
    let machine = lower(&program, &routines).unwrap();
    assert!((0..machine.values_count()).all(|at| machine.class(ValueId::at(at)) != Class::Natural));
}
