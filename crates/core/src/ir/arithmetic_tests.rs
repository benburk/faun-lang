use super::*;
use crate::barb;
use num_bigint::BigUint;

#[test]
fn unknown_or_overflowing_bounds_never_choose_a_machine_word() {
    for magnitude in [BigUint::from(u64::MAX), BigUint::from(1u8) << 100usize] {
        let mut source = crate::programs::two_and_two_in_barb();
        let add = barb::FnId::at(0);
        let nat = source.params(add)[0];
        let value = source.intern_natural(nat, &magnitude).unwrap();
        let zero = source.intern_number(nat, 0).unwrap();
        source.define(source.entry().unwrap(), |b, _| {
            let n = b.known(value);
            let sum = b.call(add, &[n, n]);
            b.match_(sum, nat, |b, _, _| b.known(zero))
        });
        let machine = lower(source.analyze(), &crate::platform::Routines::builtin()).unwrap();
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
    source.define(source.entry().unwrap(), |b, _| b.known(value));
    let error = lower(source.analyze(), &crate::platform::Routines::builtin()).unwrap_err();
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
        ("mul", Binary::Mul),
        ("div", Binary::Div),
        ("mod", Binary::Mod),
    ] {
        let mut library = barb::fixture::Library::new();
        let operation = match expected {
            Binary::Mul => library.mul,
            Binary::Div => library.div,
            _ => library.modulo,
        };
        let (nat, less_than) = (library.nat, library.less_than);
        let two = library.number(2);
        let world = tests::host(&mut library.program, nat, &routines);
        let bounded = tests::bounded(&mut library, &world);
        let program = &mut library.program;
        let main = program.declare_named("main!", &[("host", world.host)], world.never);
        program.define(main, |b, args| {
            let count = b.call(world.argc, &[args[0]]);
            let two = b.known(two);
            let small = b.call(less_than, &[count, two]);
            let n = b.call(bounded, &[args[0], small, count]);
            let answer = b.call(operation, &[n, n]);
            b.call(world.exit, &[args[0], answer])
        });
        program.set_entry(main);
        barb::validate(program).unwrap();
        // Isolate lowering from laws such as mod(n, n) = 0.
        barb::structural(program);
        barb::normalize_with_limits(program, barb::InlineLimits::default());
        barb::fold(program);
        let machine = crate::machine(program, &routines).unwrap();
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
        assert!(
            (0..machine.values_count())
                .all(|index| machine.class(ValueId::at(index)) != Class::Natural)
        );
    }
}
