use num_bigint::BigUint;

use super::{Binary, Class, Offset, Op, Program, Width, common::common, evaluate, validate};

struct Silent;
impl evaluate::Host for Silent {
    fn call(
        &mut self,
        name: &str,
        _: &[BigUint],
        _: &mut evaluate::Memory<'_>,
    ) -> Result<evaluate::HostResult, evaluate::Error> {
        Err(evaluate::Error::Host(name.to_owned()))
    }
}

fn checked(source: &Program) -> Program {
    let result = common(source);
    let answers: Vec<_> = [source, &result]
        .into_iter()
        .map(|p| {
            validate(p).unwrap();
            evaluate::evaluate(p, p.entry(), &[], evaluate::Config::default(), &mut Silent)
                .unwrap()
                .returned()
                .unwrap()
                .to_vec()
        })
        .collect();
    assert_eq!(answers[0], answers[1]);
    result
}

fn count(p: &Program, wanted: impl Fn(&Op) -> bool) -> usize {
    p.every(p.function(p.entry()).body().unwrap())
        .filter(|op| wanted(op))
        .count()
}

#[test]
fn identical_element_addresses_share_arithmetic_but_not_literal_instructions() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let start = b.constant(Class::Word, 9);
        let stride = b.constant(Class::Word, 56);
        let first = b.binary(Binary::Mul, start, stride);
        let first = b.binary(Binary::Add, first, stride);
        let stride = b.constant(Class::Word, 56);
        let second = b.binary(Binary::Mul, start, stride);
        let second = b.binary(Binary::Add, second, stride);
        let sum = b.binary(Binary::Add, first, second);
        b.ret(&[sum]);
    });
    let held = checked(&p);
    assert_eq!(
        count(&held, |op| matches!(
            op,
            Op::Binary {
                op: Binary::Mul,
                ..
            }
        )),
        1
    );
    assert_eq!(
        count(&held, |op| matches!(
            op,
            Op::Binary {
                op: Binary::Add,
                ..
            }
        )),
        2
    );
    assert_eq!(
        count(&held, |op| matches!(op, Op::Constant { value: 56 })),
        2
    );
}

#[test]
fn sibling_arms_and_their_join_do_not_share_local_values() {
    for condition in [0, 1] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let value = b.constant(Class::Word, 9);
            let condition = b.constant(Class::Word, condition);
            let chosen = b.if_(
                condition,
                &[Class::Word],
                |b| {
                    let squared = b.binary(Binary::Mul, value, value);
                    b.yield_(&[squared]);
                },
                |b| {
                    let squared = b.binary(Binary::Mul, value, value);
                    b.yield_(&[squared]);
                },
            )[0];
            let squared = b.binary(Binary::Mul, value, value);
            let sum = b.binary(Binary::Add, chosen, squared);
            b.ret(&[sum]);
        });
        let held = checked(&p);
        assert_eq!(
            count(&held, |op| matches!(
                op,
                Op::Binary {
                    op: Binary::Mul,
                    ..
                }
            )),
            3
        );
    }
}

#[test]
fn loads_stay_distinct_across_stores() {
    let (mut p, main) = Program::new("main");
    let data = p.global(&[0; 8]);
    p.define(main, |b, _| {
        let address = b.address_of(data);
        let one = b.constant(Class::Word, 1);
        let two = b.constant(Class::Word, 2);
        b.store(Width::Word, address, Offset::Bytes(0), one);
        let first = b.load(Width::Word, address, Offset::Bytes(0));
        b.store(Width::Word, address, Offset::Bytes(0), two);
        let second = b.load(Width::Word, address, Offset::Bytes(0));
        let sum = b.binary(Binary::Add, first, second);
        b.ret(&[sum]);
    });
    let held = checked(&p);
    assert_eq!(count(&held, |op| matches!(op, Op::Load { .. })), 2);
    assert_eq!(count(&held, |op| matches!(op, Op::Store { .. })), 2);
}

#[test]
fn calls_are_not_common_expressions_even_with_the_same_operands() {
    let (mut p, main) = Program::new("main");
    let opaque = p.declare("opaque", &[Class::Word], &[Class::Word]);
    p.define(opaque, |b, args| b.ret(&[args[0]]));
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 42);
        let first = b.call_one(opaque, &[value]);
        let second = b.call_one(opaque, &[value]);
        let sum = b.binary(Binary::Add, first, second);
        b.ret(&[sum]);
    });
    let held = checked(&p);
    assert_eq!(count(&held, |op| matches!(op, Op::Call { .. })), 2);
}

#[test]
fn widths_are_part_of_an_expressions_identity() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 300);
        let byte = b.convert(Class::fixed(8), value);
        let short = b.convert(Class::fixed(16), value);
        let byte = b.convert(Class::Word, byte);
        let short = b.convert(Class::Word, short);
        let sum = b.binary(Binary::Add, byte, short);
        b.ret(&[sum]);
    });
    let held = checked(&p);
    assert_eq!(count(&held, |op| matches!(op, Op::Convert { .. })), 4);
}

#[test]
fn float_expressions_share_only_with_the_same_operand_order() {
    use crate::float::{Float, Format, Operation};
    let subtract = Float {
        format: Format::Binary64,
        operation: Operation::Sub,
    };
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let a = b.constant(Class::fixed(64), 1.0f64.to_bits());
        let c = b.constant(Class::fixed(64), 2.0f64.to_bits());
        let first = b.float(subtract, &[a, c]);
        let repeated = b.float(subtract, &[a, c]);
        let reversed = b.float(subtract, &[c, a]);
        let sum = b.binary(Binary::Xor, first, repeated);
        let sum = b.binary(Binary::Xor, sum, reversed);
        b.ret(&[sum]);
    });
    let held = checked(&p);
    assert_eq!(count(&held, |op| matches!(op, Op::Float { .. })), 2);
}
