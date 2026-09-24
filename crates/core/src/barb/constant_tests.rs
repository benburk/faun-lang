use num_bigint::BigUint;
use num_traits::ToPrimitive;

use super::budget::Budget;
use super::constant::Held;
use super::{
    ByteView, ConstantView, ConstructionError, FoldLimits, LimitExceeded, Program, TooWide, TypeId,
    Value, decode,
};

#[test]
fn numeric_construction_rejects_bad_types_without_mutating_storage() {
    let (mut program, nat, _, list) = super::tests::types();
    let unit = program.declare_type("Unit");
    program.define_type(unit, &[("Only", &[])]);
    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let pending = program.declare_type("Pending");
    let before = program.clone();
    for (owner, error) in [
        (list, ConstructionError::NotNatural(list)),
        (unit, ConstructionError::NotNatural(unit)),
        (empty, ConstructionError::NotNatural(empty)),
        (pending, ConstructionError::UndefinedType(pending)),
        (
            TypeId::at(999),
            ConstructionError::UndefinedType(TypeId::at(999)),
        ),
    ] {
        assert_eq!(program.intern_number(owner, 42), Err(error.clone()));
        assert_eq!(
            program.intern_natural(owner, &(BigUint::from(1u8) << 200usize)),
            Err(error)
        );
        assert_eq!(program, before);
    }
    let zero = program.intern_number(nat, 0).unwrap();
    let before = program.constants.clone();
    let function = program.declare("literal", &[], nat);
    program.define(function, |b, _| {
        assert_eq!(b.number(unit, 42), Err(ConstructionError::NotNatural(unit)));
        b.known(zero)
    });
    assert_eq!(program.constants, before);
}

#[test]
fn byte_spine_construction_checks_shape_before_mutating_storage() {
    let (mut program, nat, _, list) = super::tests::types();
    let unit = program.declare_type("Unit");
    program.define_type(unit, &[("Only", &[])]);
    let pending = program.declare_type("Pending");
    let before = program.clone();
    for (owner, error) in [
        (nat, ConstructionError::NotByteSpine(nat)),
        (unit, ConstructionError::NotByteSpine(unit)),
        (pending, ConstructionError::UndefinedType(pending)),
    ] {
        assert_eq!(program.intern_byte_spine(owner, b"hello"), Err(error));
        assert_eq!(program, before);
    }
    let value = program.intern_byte_spine(list, b"hello").unwrap();
    let ConstantView::Spine(value) = program.constant(value).view() else {
        panic!("a byte spine");
    };
    assert_eq!(value.to_bytes().as_deref(), Some(b"hello".as_slice()));
}

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

#[test]
fn bounded_queries_respect_structure_not_constructor_order_or_names() {
    let (mut program, _, _, list) = super::tests::types();
    let reversed = program.declare_type("Reversed");
    program.define_type(reversed, &[("Next", &[reversed]), ("Empty", &[])]);
    let number = program.intern_number(reversed, 128).unwrap();
    let ConstantView::Natural(n) = program.constant(number).view() else {
        panic!("a natural");
    };
    assert_eq!(n.try_u64(), Ok(128));
    assert_eq!(
        program.constant(number).constructor(),
        program.ctor_at(reversed, 0)
    );
    let zero = program.intern_number(reversed, 0).unwrap();
    assert_eq!(
        program.constant(zero).constructor(),
        program.ctor_at(reversed, 1)
    );
    let flag = program.declare_type("Flag");
    program.define_type(flag, &[("Off", &[]), ("On", &[])]);
    let empty = program.intern_byte_spine(list, b"").unwrap();
    assert!(matches!(
        program.constant(empty).view(),
        ConstantView::Spine(_)
    ));
    let on = program.ctor_at(flag, 1);
    let id = program.intern(flag, &Value(on, vec![])).unwrap();
    let ConstantView::Constructor(ctor) = program.constant(id).view() else {
        panic!("a sum");
    };
    assert_eq!(ctor.constructor(), on);
}

#[test]
fn byte_views_borrow_their_bytes_and_wide_numbers_are_too_wide() {
    let (mut program, nat, _, list) = super::tests::types();
    let id = program.intern_byte_spine(list, b"abc").unwrap();
    let ConstantView::Spine(spine) = program.constant(id).view() else {
        panic!("a spine");
    };
    assert_eq!(spine.length(), BigUint::from(3u8));
    assert_eq!(spine.byte_slice(), ByteView::Borrowed(b"abc"));
    let id = program
        .intern_natural(nat, &(BigUint::from(1u8) << 64usize))
        .unwrap();
    let ConstantView::Natural(number) = program.constant(id).view() else {
        panic!("a natural");
    };
    assert_eq!(number.try_u64(), Err(TooWide));
}

#[test]
fn definitions_are_immutable_and_an_undefined_type_is_not_an_empty_type() {
    let (mut program, nat, _, _) = super::tests::types();
    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let zero = program.intern_number(nat, 0).unwrap();
    let before = program.clone();
    for owner in [nat, empty] {
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || program.define_type(owner, &[("Replacement", &[])])
            ))
            .is_err()
        );
        assert_eq!(program, before);
    }
    let pending = program.declare_type("Pending");
    let entry = program.declare("main", &[], nat);
    program.define(entry, |b, _| b.known(zero));
    program.set_entry(entry);
    assert!(super::validate(&program).unwrap_err().contains("Pending"));
    program.define_type(pending, &[]);
    super::validate(&program).unwrap();
    assert_eq!(
        program.constant(zero).constructor(),
        program.ctor_at(nat, 0)
    );
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

#[test]
fn natural_views_take_a_huge_predecessor_without_materializing_the_spine() {
    let mut program = Program::default();
    let nat = program.declare_type("Count");
    program.define_type(nat, &[("Next", &[nat]), ("End", &[])]);
    let large = BigUint::from(1u8) << 200usize;
    let id = program.intern_natural(nat, &large).unwrap();
    let view = program.constant(id);
    let ConstantView::Natural(number) = view.view() else {
        panic!("a natural");
    };
    assert_eq!(number.try_u64(), Err(TooWide));
    assert_eq!(number.to_biguint(), large);
    assert_eq!(view.constructor(), program.ctor_at(nat, 0));
    let mut budget = Budget::new(FoldLimits::default());
    let (ctor, fields) = view.parts(&mut budget).unwrap();
    assert_eq!(fields.len(), 1);
    let ConstantView::Natural(predecessor) = fields[0].as_constant(program.type_info()).view()
    else {
        panic!("a natural");
    };
    assert_eq!(predecessor.to_biguint(), &large - 1u8);
    let rebuilt = Held::build(program.type_info(), ctor, &fields, &mut budget).unwrap();
    assert_eq!(rebuilt.encoded(), program.known_bytes(id));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "exact work and size boundaries for both codec operations"
)]
fn constant_construction_and_decomposition_keep_their_exact_budget_charges() {
    let (mut program, nat, _, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    let one_two = pair_value(&program, pair, nat);
    let id = program.intern(pair, &one_two).unwrap();
    let view = program.constant(id);
    let mut budget = Budget::new(FoldLimits {
        work: 6,
        ..FoldLimits::default()
    });
    // Two copied bytes, two fields, and two field-extent visits.
    let (ctor, fields) = view.parts(&mut budget).unwrap();
    assert_eq!(budget.remaining, 0);
    let mut short = Budget::new(FoldLimits {
        work: 5,
        ..FoldLimits::default()
    });
    assert_eq!(view.parts(&mut short).unwrap_err(), LimitExceeded::Work);
    assert_eq!(short.remaining, 0);
    let mut small = Budget::new(FoldLimits {
        work: 100,
        max_bytes: 1,
        ..FoldLimits::default()
    });
    assert_eq!(
        view.parts(&mut small).unwrap_err(),
        LimitExceeded::ValueSize
    );
    assert_eq!(small.remaining, 100);
    // Construction still reserves payload + five, even for a tagless product.
    let mut budget = Budget::new(FoldLimits {
        work: 7,
        ..FoldLimits::default()
    });
    assert_eq!(
        Held::build(program.type_info(), ctor, &fields, &mut budget)
            .unwrap()
            .encoded(),
        [1, 2]
    );
    assert_eq!(budget.remaining, 0);
    let mut small = Budget::new(FoldLimits {
        work: 100,
        max_bytes: 6,
        ..FoldLimits::default()
    });
    assert_eq!(
        Held::build(program.type_info(), ctor, &fields, &mut small).unwrap_err(),
        ConstructionError::Limit(LimitExceeded::ValueSize)
    );
    assert_eq!(small.remaining, 100);
}

#[test]
fn field_scans_share_evaluation_depth_and_restore_it_after_refusal() {
    let (mut program, nat, _, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    let outer = program.declare_type("Outer");
    program.define_type(outer, &[("Outer", &[pair])]);
    let mut budget = Budget::new(FoldLimits {
        work: 100,
        max_depth: 1,
        ..FoldLimits::default()
    });
    let one_two = pair_value(&program, pair, nat);
    let wrapped = Value(program.ctor_at(outer, 0), vec![one_two.clone()]);
    let id = program.intern(outer, &wrapped).unwrap();
    assert_eq!(
        program.constant(id).parts(&mut budget).unwrap_err(),
        LimitExceeded::Depth
    );
    assert_eq!(budget.remaining, 95);
    let pair = program.intern(pair, &one_two).unwrap();
    let ConstantView::Constructor(pair) = program.constant(pair).view() else {
        panic!("a product");
    };
    assert_eq!(pair.fields(&mut budget).unwrap().len(), 2);
    assert_eq!(budget.remaining, 89);
    assert_eq!(
        budget.descend(|budget| pair.fields(budget)).unwrap_err(),
        LimitExceeded::Depth
    );
    assert_eq!(pair.fields(&mut budget).unwrap().len(), 2);
    assert_eq!(budget.remaining, 77);
}

/// `Pair(1 2)`, which encodes as the two bytes `[1, 2]`.
fn pair_value(program: &Program, pair: TypeId, nat: TypeId) -> Value {
    Value(
        program.ctor_at(pair, 0),
        vec![
            super::tests::nat(program, nat, 1),
            super::tests::nat(program, nat, 2),
        ],
    )
}
