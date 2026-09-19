use num_bigint::BigUint;
use num_traits::ToPrimitive;

use super::{as_bytes, as_natural, as_number, constant, decode};

#[test]
fn bounded_queries_agree_with_bigints_at_every_bit_boundary() {
    let (program, nat, _, _) = super::tests::types();
    for bit in 0usize..=256 {
        let power = BigUint::from(1u8) << bit;
        for value in [&power - 1u8, power.clone(), power + 1u8] {
            let mut bytes = vec![];
            constant::write_natural(&value, &mut bytes);
            assert_eq!(
                as_number(&program, nat, &bytes),
                value.to_u64(),
                "bit {bit}"
            );
            assert_eq!(as_natural(&program, nat, &bytes), Some(value));
        }
    }
}

#[test]
fn bounded_queries_accept_padding_and_stop_before_the_next_value() {
    let (program, nat, _, _) = super::tests::types();
    for value in [0, 1, 127, 128, u64::MAX] {
        let mut bytes = vec![];
        constant::write_number(value, &mut bytes);
        *bytes.last_mut().unwrap() |= 0x80;
        bytes.extend([0x80; 1024]);
        bytes.push(0);
        bytes.extend([0xff; 3]); // A separate, malformed value must not be read.
        assert_eq!(as_number(&program, nat, &bytes), Some(value));
        assert_eq!(
            as_natural(&program, nat, &bytes),
            Some(BigUint::from(value))
        );
    }
}

#[test]
fn bounded_queries_respect_structure_not_constructor_order_or_names() {
    let (mut program, _, _, list) = super::tests::types();
    let reversed = program.declare_type("Reversed");
    program.define_type(reversed, &[("Next", &[reversed]), ("Empty", &[])]);
    assert_eq!(as_number(&program, reversed, &[0x80, 1]), Some(128));
    let flag = program.declare_type("Flag");
    program.define_type(flag, &[("Off", &[]), ("On", &[])]);
    // Non-naturals return None without trying to decode the bytes.
    assert_eq!(as_number(&program, list, &[]), None);
    assert_eq!(as_number(&program, flag, &[]), None);
    assert_eq!(as_bytes(&program, flag, &[]), None);
    let (value, took) = decode(&program, flag, &[0x81, 0]);
    assert_eq!(value.0, program.ctor_at(flag, 1));
    assert_eq!(took, 2);
}

#[test]
fn bounded_counts_preserve_byte_views_and_reject_unmaterializable_counts() {
    let (program, nat, _, list) = super::tests::types();
    assert_eq!(as_bytes(&program, list, b"\x83\x00abc"), Some(&b"abc"[..]));
    assert_eq!(as_bytes(&program, list, b"\x02abc"), None);
    let (value, took) = decode(&program, nat, &[0x82, 0]);
    assert_eq!(value, super::tests::nat(&program, nat, 2));
    assert_eq!(took, 2);
    let mut overflow = vec![];
    constant::write_natural(&(BigUint::from(1u8) << 64usize), &mut overflow);
    assert_eq!(as_number(&program, nat, &overflow), None);
    assert_eq!(as_bytes(&program, list, &overflow), None);
    assert!(std::panic::catch_unwind(|| decode(&program, nat, &overflow)).is_err());
}

#[test]
fn unterminated_counts_still_panic_even_after_overflow() {
    let (program, nat, _, list) = super::tests::types();
    for bytes in [&[][..], &[0x80], &[0xff; 20]] {
        assert!(std::panic::catch_unwind(|| as_number(&program, nat, bytes)).is_err());
        assert!(std::panic::catch_unwind(|| as_bytes(&program, list, bytes)).is_err());
        assert!(std::panic::catch_unwind(|| decode(&program, nat, bytes)).is_err());
    }
}
