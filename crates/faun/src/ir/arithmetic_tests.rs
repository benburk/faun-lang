use super::*;
use crate::barb;
use num_bigint::BigUint;

#[test]
fn unknown_or_overflowing_bounds_never_choose_a_machine_word() {
    for magnitude in [BigUint::from(u64::MAX), BigUint::from(1u8) << 100usize] {
        let mut source = crate::programs::two_and_two_in_barb();
        let add = barb::FnId::at(0);
        let nat = source.params(add)[0];
        let value = source.intern_natural(nat, &magnitude);
        let zero = source.intern_number(nat, 0);
        source.define(source.entry().unwrap(), |b, _| {
            let n = b.known(nat, value);
            let sum = b.call(add, &[n, n]);
            b.match_(sum, nat, |b, _, _| b.known(nat, zero))
        });
        let facts = barb::recognise(&source);
        let machine = lower(&source, &facts, &crate::platform::Routines::builtin()).unwrap();
        let body = machine.functions()[0].body;
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
    let value = source.intern_natural(nat, &(BigUint::from(1u8) << 100usize));
    source.define(source.entry().unwrap(), |b, _| b.known(nat, value));
    let error = lower(
        &source,
        &barb::recognise(&source),
        &crate::platform::Routines::builtin(),
    )
    .unwrap_err();
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
        b.ret(&[zero])
    });
    assert_eq!(program.data(), magnitude.to_bytes_le());
    assert!(!Class::Natural.fits(Class::Word));
    assert!(!Class::Word.fits(Class::Natural), "promotion is explicit");
    validate(&program).unwrap();
}

#[test]
fn runtime_arithmetic_survives_barb_lowering_as_operations() {
    for (name, expected) in [
        ("mul", Binary::Mul),
        ("div", Binary::Div),
        ("mod", Binary::Mod),
    ] {
        let text = format!(
            "{}\nbounded!(h True n) -> n\nbounded!(h False n) -> exit!(h Zero)\n\
             main!(h) ->\n  count = argc!(h)\n\
               n = bounded!(h less_than(count Succ(Succ(Zero))) count)\n\
               exit!(h {name}(n n))",
            include_str!("../../../../standard/nat.fn")
        );
        let machine = crate::read(&text, &crate::platform::Routines::builtin()).unwrap();
        validate(&machine).unwrap();
        let body = machine.functions()[0].body;
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
