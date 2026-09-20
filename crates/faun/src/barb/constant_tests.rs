use num_bigint::BigUint;
use num_traits::ToPrimitive;

use super::budget::Budget;
use super::constant::Held;
use super::{
    ByteView, ConstantView, ConstructionError, DecodeError, FoldLimits, LimitExceeded, Program,
    TooWide, TypeId, Value, constant, decode,
};

#[test]
fn bounded_queries_agree_with_bigints_at_every_bit_boundary() {
    let (mut program, nat, _, _) = super::tests::types();
    for bit in 0usize..=256 {
        let power = BigUint::from(1u8) << bit;
        for value in [&power - 1u8, power.clone(), power + 1u8] {
            let mut bytes = vec![];
            constant::write_natural(&value, &mut bytes);
            let id = program
                .decode_constant(nat, &bytes, &mut Budget::new(FoldLimits::default()))
                .unwrap();
            let ConstantView::Natural(number) = program.constant(id).view() else {
                panic!("a natural");
            };
            assert_eq!(number.try_u64(), value.to_u64().ok_or(TooWide), "bit {bit}");
            assert_eq!(number.to_biguint(), value);
        }
    }
}

#[test]
fn padded_fields_are_bounded_and_imports_reject_trailing_bytes() {
    let (mut program, nat, _, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    for value in [0, 1, 127, 128, u64::MAX] {
        let mut bytes = vec![];
        constant::write_number(value, &mut bytes);
        *bytes.last_mut().unwrap() |= 0x80;
        bytes.extend([0x80; 1024]);
        bytes.push(0);
        let length = bytes.len();
        bytes.push(7);
        let id = program
            .decode_constant(pair, &bytes, &mut Budget::new(FoldLimits::default()))
            .unwrap();
        let ConstantView::Constructor(ctor) = program.constant(id).view() else {
            panic!("a product");
        };
        let fields = ctor
            .fields(&mut Budget::new(FoldLimits::default()))
            .unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].encoded().len(), length);
        assert_eq!(fields[1].encoded(), &[7]);
        let ConstantView::Natural(number) = fields[0].view() else {
            panic!("a natural");
        };
        assert_eq!(number.try_u64(), Ok(value));
        assert_eq!(number.to_biguint(), BigUint::from(value));
        bytes.truncate(length);
        bytes.extend([0xff; 3]); // A separate malformed value must not be scanned.
        assert_eq!(
            program.decode_constant(nat, &bytes, &mut Budget::new(FoldLimits::default())),
            Err(DecodeError::TrailingBytes)
        );
    }
}

#[test]
fn bounded_queries_respect_structure_not_constructor_order_or_names() {
    let (mut program, _, _, list) = super::tests::types();
    let reversed = program.declare_type("Reversed");
    program.define_type(reversed, &[("Next", &[reversed]), ("Empty", &[])]);
    let number = program.intern_number(reversed, 128);
    let ConstantView::Natural(n) = program.constant(number).view() else {
        panic!("a natural");
    };
    assert_eq!(n.try_u64(), Ok(128));
    assert_eq!(
        program.constant(number).constructor(),
        program.ctor_at(reversed, 0)
    );
    let zero = program.intern_number(reversed, 0);
    assert_eq!(
        program.constant(zero).constructor(),
        program.ctor_at(reversed, 1)
    );
    let flag = program.declare_type("Flag");
    program.define_type(flag, &[("Off", &[]), ("On", &[])]);
    let empty = program
        .decode_constant(list, &[0], &mut Budget::new(FoldLimits::default()))
        .unwrap();
    assert!(matches!(
        program.constant(empty).view(),
        ConstantView::Spine(_)
    ));
    let (value, took) = decode(&program, flag, &[0x81, 0]);
    let id = program
        .decode_constant(flag, &[0x81, 0], &mut Budget::new(FoldLimits::default()))
        .unwrap();
    let ConstantView::Constructor(ctor) = program.constant(id).view() else {
        panic!("a sum");
    };
    assert_eq!(ctor.constructor(), value.0);
    assert_eq!(value.0, program.ctor_at(flag, 1));
    assert_eq!(took, 2);
}

#[test]
fn bounded_counts_preserve_byte_views_and_reject_unmaterializable_counts() {
    let (mut program, nat, _, list) = super::tests::types();
    let id = program
        .decode_constant(
            list,
            b"\x83\x00abc",
            &mut Budget::new(FoldLimits::default()),
        )
        .unwrap();
    let ConstantView::Spine(spine) = program.constant(id).view() else {
        panic!("a spine");
    };
    assert_eq!(spine.length(), BigUint::from(3u8));
    assert_eq!(spine.byte_slice(), ByteView::Borrowed(b"abc"));
    assert_eq!(
        program.decode_constant(list, b"\x02abc", &mut Budget::new(FoldLimits::default())),
        Err(DecodeError::TrailingBytes)
    );
    let (value, took) = decode(&program, nat, &[0x82, 0]);
    assert_eq!(value, super::tests::nat(&program, nat, 2));
    assert_eq!(took, 2);
    let mut overflow = vec![];
    constant::write_natural(&(BigUint::from(1u8) << 64usize), &mut overflow);
    let id = program
        .decode_constant(nat, &overflow, &mut Budget::new(FoldLimits::default()))
        .unwrap();
    let ConstantView::Natural(number) = program.constant(id).view() else {
        panic!("a natural");
    };
    assert_eq!(number.try_u64(), Err(TooWide));
    assert_eq!(
        program.decode_constant(list, &overflow, &mut Budget::new(FoldLimits::default())),
        Err(DecodeError::Limit(LimitExceeded::Work))
    );
}

#[test]
fn malformed_headers_are_rejected_even_after_overflow_without_mutating_the_pool() {
    let (mut program, nat, _, list) = super::tests::types();
    let before = program.clone();
    for bytes in [&[][..], &[0x80], &[0xff; 20]] {
        for owner in [nat, list] {
            assert_eq!(
                program.decode_constant(owner, bytes, &mut Budget::new(FoldLimits::default())),
                Err(DecodeError::UnterminatedHeader)
            );
            assert_eq!(program, before);
        }
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "table of malformed and resource-limited imports with the same atomicity assertion"
)]
fn checked_imports_distinguish_invalid_shapes_from_resource_refusal() {
    let (mut program, nat, _, list) = super::tests::types();
    let flag = program.declare_type("Flag");
    program.define_type(flag, &[("Off", &[]), ("On", &[])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let pending = program.declare_type("Pending");
    let before = program.clone();
    for (owner, bytes, error) in [
        (flag, &[2][..], DecodeError::InvalidTag(flag)),
        (
            flag,
            &[
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0,
            ][..],
            DecodeError::InvalidTag(flag),
        ),
        (empty, &[0][..], DecodeError::InvalidTag(empty)),
        (pending, &[0][..], DecodeError::UndefinedType(pending)),
        (pair, &[1][..], DecodeError::UnterminatedHeader),
        (list, &[2, 1][..], DecodeError::UnterminatedHeader),
    ] {
        assert_eq!(
            program.decode_constant(owner, bytes, &mut Budget::new(FoldLimits::default())),
            Err(error)
        );
        assert_eq!(program, before);
    }
    for (limits, refusal) in [
        (
            FoldLimits {
                work: 0,
                ..FoldLimits::default()
            },
            LimitExceeded::Work,
        ),
        (
            FoldLimits {
                max_bytes: 0,
                ..FoldLimits::default()
            },
            LimitExceeded::ValueSize,
        ),
        (
            FoldLimits {
                max_depth: 0,
                ..FoldLimits::default()
            },
            LimitExceeded::Depth,
        ),
    ] {
        assert_eq!(
            program.decode_constant(nat, &[1], &mut Budget::new(limits)),
            Err(DecodeError::Limit(refusal))
        );
        assert_eq!(program, before);
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "checked construction boundaries reject bad inputs without changing the pool"
)]
fn construction_checks_type_identity_and_arity_before_mutating_the_pool() {
    let (mut program, nat, byte, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[nat, nat])]);
    let ctor = program.ctor_at(pair, 0);
    let one = program.intern_number(nat, 1);
    let two = program.intern_number(nat, 2);
    let octet = program.intern_number(byte, 1);
    // Identical shapes and identical bytes are not interchangeable types.
    assert_eq!(program.known_bytes(one), program.known_bytes(octet));
    let before = program.clone();
    let mut budget = Budget::new(FoldLimits::default());
    assert_eq!(
        program.construct(ctor, &[one], &mut budget),
        Err(ConstructionError::FieldCount {
            expected: 2,
            actual: 1
        })
    );
    assert_eq!(
        program.construct(ctor, &[one, octet], &mut budget),
        Err(ConstructionError::FieldType {
            expected: nat,
            actual: byte
        })
    );
    let missing = super::ConstId::at(999);
    assert_eq!(
        program.construct(ctor, &[one, missing], &mut budget),
        Err(ConstructionError::UnknownConstant(missing))
    );
    let missing = super::CtorId::at(999);
    assert_eq!(
        program.construct(missing, &[], &mut budget),
        Err(ConstructionError::UnknownConstructor(missing))
    );
    let wrong = Value(
        ctor,
        vec![
            super::tests::nat(&program, nat, 1),
            super::tests::nat(&program, byte, 1),
        ],
    );
    assert_eq!(
        program.intern(pair, &wrong),
        Err(ConstructionError::FieldType {
            expected: nat,
            actual: byte
        })
    );
    assert_eq!(
        program.intern(pair, &Value(ctor, vec![])),
        Err(ConstructionError::FieldCount {
            expected: 2,
            actual: 0
        })
    );
    assert_eq!(program, before);
    let mut tiny = Budget::new(FoldLimits {
        max_bytes: 1,
        ..FoldLimits::default()
    });
    assert_eq!(
        program.construct(ctor, &[one, two], &mut tiny),
        Err(ConstructionError::Limit(LimitExceeded::ValueSize))
    );
    assert_eq!(program, before);
    let id = program.construct(ctor, &[one, two], &mut budget).unwrap();
    assert_eq!(program.constant(id).owner(), pair);
    assert_eq!(program.known_bytes(id), &[1, 2]);
    let entry = program.declare("pair", &[], pair);
    program.define(entry, |b, _| b.known(id));
    assert_eq!(
        program.expr(program.function(entry).body().unwrap().tail),
        super::Expr::Static(id)
    );
}

#[test]
fn definitions_are_immutable_and_an_undefined_type_is_not_an_empty_type() {
    let (mut program, nat, _, _) = super::tests::types();
    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let zero = program.intern_number(nat, 0);
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
    let rebuilt = Held::build(program, ctor, &fields, &mut budget).unwrap();
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
    let id = program.intern_natural(nat, &large);
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
    let ConstantView::Natural(predecessor) = fields[0].as_constant(&program).view() else {
        panic!("a natural");
    };
    assert_eq!(predecessor.to_biguint(), &large - 1u8);
    let rebuilt = Held::build(&program, ctor, &fields, &mut budget).unwrap();
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
    let id = program
        .decode_constant(pair, &[1, 2], &mut Budget::new(FoldLimits::default()))
        .unwrap();
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
        Held::build(&program, ctor, &fields, &mut budget)
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
        Held::build(&program, ctor, &fields, &mut small).unwrap_err(),
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
    let id = program
        .decode_constant(outer, &[1, 2], &mut Budget::new(FoldLimits::default()))
        .unwrap();
    assert_eq!(
        program.constant(id).parts(&mut budget).unwrap_err(),
        LimitExceeded::Depth
    );
    assert_eq!(budget.remaining, 95);
    let pair = program
        .decode_constant(pair, &[1, 2], &mut Budget::new(FoldLimits::default()))
        .unwrap();
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
