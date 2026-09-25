use super::evaluate::{Config, Error, Evaluation, RejectHost, evaluate};
use super::*;
use num_bigint::BigUint;

fn run(
    program: &Program,
    function: FunctionId,
    args: &[u64],
    bits: u16,
) -> Result<Evaluation, Error> {
    evaluate(
        program,
        function,
        &args.iter().copied().map(BigUint::from).collect::<Vec<_>>(),
        Config {
            word_bits: bits,
            ..Config::default()
        },
        &mut RejectHost,
    )
}

fn division_program() -> (Program, FunctionId) {
    let (mut p, _) = Program::new("main");
    let divmod = p.declare(
        "divmod",
        &[Class::Word, Class::Word],
        &[Class::Word, Class::Word],
    );
    p.define(divmod, |b, args| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let is_zero = b.compare(Relation::Equal, args[1], zero);
        b.if_(is_zero, &[], |b| b.ret(&[zero, args[0]]), |b| b.yield_(&[]));
        let answer = b.loop_(&[zero, args[0]], &[Class::Word, Class::Word], |b, state| {
            let done = b.compare(Relation::Less, state[1], args[1]);
            b.if_(
                done,
                &[],
                |b| b.break_(state),
                |b| {
                    let q = b.binary(Binary::Add, state[0], one);
                    let r = b.binary(Binary::Sub, state[1], args[1]);
                    b.continue_(&[q, r]);
                },
            );
        });
        b.ret(&answer);
    });
    (p, divmod)
}

#[test]
fn loops_and_nested_exits_match_total_division_model_at_every_width() {
    let (p, divmod) = division_program();
    for bits in [16, 32, 64] {
        for left in 0u64..20 {
            for right in 0..8 {
                let expected = vec![
                    left.checked_div(right).unwrap_or(0),
                    left.checked_rem(right).unwrap_or(left),
                ];
                assert_eq!(
                    run(&p, divmod, &[left, right], bits)
                        .unwrap()
                        .returned()
                        .unwrap(),
                    expected.into_iter().map(BigUint::from).collect::<Vec<_>>()
                );
            }
        }
    }
}

#[test]
fn words_wrap_at_the_configured_width_not_the_host_width() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let max = b.binary(Binary::Sub, zero, one);
        b.ret(&[max]);
    });
    for bits in [16, 32, 64] {
        let max = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![max]
        );
    }
    for bits in [16, 32, 64] {
        p.define(main, |b, _| {
            let max = b.constant(Class::Word, u64::MAX >> (64 - bits));
            let one = b.constant(Class::Word, 1);
            let zero = b.binary(Binary::Add, max, one);
            b.ret(&[zero]);
        });
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
    }
}

fn binary_program(class: Class, op: Binary) -> (Program, FunctionId) {
    let (mut p, _) = Program::new("main");
    let f = p.declare("binary", &[class, class], &[class]);
    p.define(f, |b, args| {
        let result = b.binary(op, args[0], args[1]);
        b.ret(&[result]);
    });
    (p, f)
}

fn natural_model(op: Binary, left: &BigUint, right: &BigUint) -> BigUint {
    match op {
        Binary::Monus if left < right => BigUint::default(),
        Binary::Monus => left - right,
        Binary::Mul => left * right,
        Binary::Div => {
            if right == &BigUint::default() {
                BigUint::default()
            } else {
                left / right
            }
        }
        Binary::Mod => {
            if right == &BigUint::default() {
                left.clone()
            } else {
                left % right
            }
        }
        _ => unreachable!(),
    }
}

#[test]
fn direct_natural_operations_preserve_full_magnitudes_and_total_zero_semantics() {
    let large = (BigUint::from(1u8) << 200usize) + BigUint::from(17u8);
    let small = (BigUint::from(1u8) << 100usize) + BigUint::from(3u8);
    let cases = [
        BigUint::default(),
        BigUint::from(1u8),
        BigUint::from(u64::MAX),
        small,
        large,
    ];
    for op in [Binary::Monus, Binary::Mul, Binary::Div, Binary::Mod] {
        let (p, f) = binary_program(Class::Natural, op);
        for left in &cases {
            for right in &cases {
                let expected = natural_model(op, left, right);
                for word_bits in [16, 32, 64] {
                    let result = evaluate(
                        &p,
                        f,
                        &[left.clone(), right.clone()],
                        Config {
                            word_bits,
                            ..Config::default()
                        },
                        &mut RejectHost,
                    )
                    .unwrap();
                    assert_eq!(result.returned().unwrap(), vec![expected.clone()]);
                }
            }
        }
    }
}

#[test]
fn a_monus_saturates_and_answers_at_its_own_class() {
    let (mut p, _) = Program::new("main");
    let check = p.declare(
        "check",
        &[Class::fixed(9), Class::fixed(9)],
        &[Class::fixed(5)],
    );
    // What the answer can be is narrower than either operand, as a bound
    // proved above this tier can say.
    p.define(check, |b, args| {
        let answer = b.binary_at(Class::fixed(5), Binary::Monus, args[0], args[1]);
        b.ret(&[answer]);
    });
    for (left, right, answer) in [(281, 255, 26u8), (255, 255, 0), (250, 255, 0), (0, 511, 0)] {
        assert_eq!(
            run(&p, check, &[left, right], 16)
                .unwrap()
                .returned()
                .unwrap(),
            vec![BigUint::from(answer)],
            "{left} {right}"
        );
    }
    assert_eq!(
        run(&p, check, &[511, 0], 16),
        Err(Error::DoesNotFit(Class::fixed(5)))
    );
}

#[test]
fn shared_native_backend_arithmetic_fixtures_agree_with_interpreter() {
    use crate::programs::{arithmetic, wraps_at_eight_bits};
    for bits in [16, 32, 64] {
        for op in [Binary::Mul, Binary::Div, Binary::Mod] {
            let p = arithmetic::boundaries(bits, op);
            validate(&p).unwrap();
            assert_eq!(
                run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
                vec![BigUint::default()]
            );
        }
        let p = arithmetic::odd_conversion();
        assert_eq!(
            run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
        let p = wraps_at_eight_bits();
        assert_eq!(
            run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(4u8)]
        );
        let p = arithmetic::preserves_host_count();
        assert_eq!(
            run(&p, p.entry(), &[1], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
    }
}
