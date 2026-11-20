use num_bigint::BigUint;
use num_traits::ToPrimitive;

use super::budget::Budget;
use super::constant::Held;
use super::{ConstantView, FoldLimits, Program, TooWide, TypeId, Value, decode};

#[test]
fn bounded_queries_agree_with_bigints_at_every_bit_boundary() {
    let (mut program, nat, _, _) = super::tests::types();
    for bit in 0usize..=256 {
        let power = BigUint::from(1u8) << bit;
        for value in [&power - 1u8, power.clone(), power + 1u8] {
            let id = program.intern_natural(nat, &value).unwrap();
            let ConstantView::Natural(number) = program.constant(id).view() else {
                panic!("a natural");
            };
            assert_eq!(number.try_u64(), value.to_u64().ok_or(TooWide), "bit {bit}");
            assert_eq!(number.to_biguint(), value);
        }
    }
}

fn check_view(program: &mut Program, owner: TypeId, value: &Value) {
    let id = program.intern(owner, value).unwrap();
    let view = program.constant(id);
    assert_eq!(view.owner(), owner);
    assert_eq!(view.constructor(), value.0);
    let mut budget = Budget::new(FoldLimits::default());
    let (ctor, fields) = view.parts(&mut budget).unwrap();
    assert_eq!(ctor, value.0);
    assert_eq!(fields.len(), value.1.len());
    for ((field, expected), &ty) in fields.iter().zip(&value.1).zip(program.fields(ctor)) {
        assert_eq!(field.owner(), ty);
        assert_eq!(
            decode(program, ty, field.encoded()),
            (expected.clone(), field.encoded().len())
        );
    }
    let rebuilt = Held::build(program.type_info(), ctor, &fields, &mut budget).unwrap();
    assert_eq!(rebuilt.owner(), owner);
    assert_eq!(rebuilt.encoded(), view.encoded());
    if let ConstantView::Constructor(ctor) = view.view() {
        let borrowed = ctor.fields(&mut budget).unwrap();
        assert_eq!(borrowed.len(), fields.len());
        for (borrowed, owned) in borrowed.iter().zip(&fields) {
            assert_eq!(borrowed.owner(), owned.owner());
            assert_eq!(borrowed.encoded(), owned.encoded());
        }
    }
}

#[test]
fn views_agree_with_the_tree_codec_for_products_sums_and_nested_spines() {
    let (mut program, nat, _, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    let choice = program.declare_type("Choice");
    program.define_type(choice, &[("Absent", &[]), ("Present", &[pair])]);
    let list = program.declare_type("Chain");
    // Empty constructor last; recursive field between two payload fields.
    program.define_type(list, &[("Link", &[nat, list, choice]), ("End", &[])]);
    let n = |n| super::tests::nat(&program, nat, n);
    let pair_value = Value(program.ctor_at(pair, 0), vec![n(128), n(3)]);
    let absent = Value(program.ctor_at(choice, 0), vec![]);
    let present = Value(program.ctor_at(choice, 1), vec![pair_value.clone()]);
    let end = Value(program.ctor_at(list, 1), vec![]);
    let mut chain = end.clone();
    for item in [absent.clone(), present.clone()] {
        chain = Value(program.ctor_at(list, 0), vec![n(4), chain, item]);
    }
    for (owner, value) in [
        (nat, n(0)),
        (nat, n(128)),
        (pair, pair_value),
        (choice, absent),
        (choice, present),
        (list, end),
        (list, chain),
    ] {
        check_view(&mut program, owner, &value);
    }
}
