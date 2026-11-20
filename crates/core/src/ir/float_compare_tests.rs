//! The same IEEE boundary matrix exercises portable and native comparison lowering.
use super::{Class, Program, evaluate, validate};
use barb::float::Format;
use num_bigint::BigUint;

fn patterns(format: Format) -> Vec<u64> {
    let (infinity, one) = match format {
        Format::Binary32 => (0x7f80_0000, u64::from(1.0f32.to_bits())),
        Format::Binary64 => (0x7ff0_0000_0000_0000, 1.0f64.to_bits()),
    };
    let sign = 1 << (format.bits() - 1);
    [
        0,
        1,
        one - 1,
        one,
        one + 1,
        infinity - 1,
        infinity,
        infinity + 1,
    ]
    .into_iter()
    .flat_map(|n| [n, n | sign])
    .collect()
}

#[test]
fn unordered_comparison_preserves_ieee_boundaries() {
    for format in [Format::Binary32, Format::Binary64] {
        let class = Class::fixed(format.bits());
        let (mut program, entry) =
            Program::new_with_params("compare", &[("left", class), ("right", class)]);
        program.define(entry, |b, args| {
            let result = b.float_not_above(format, args[0], args[1]);
            b.ret(&[result]);
        });
        validate(&program).unwrap();
        for left in patterns(format) {
            for right in patterns(format) {
                let ordered = match format {
                    Format::Binary32 => f32::from_bits(u32::try_from(left).unwrap())
                        .partial_cmp(&f32::from_bits(u32::try_from(right).unwrap())),
                    Format::Binary64 => f64::from_bits(left).partial_cmp(&f64::from_bits(right)),
                };
                let expected = u8::from(ordered != Some(std::cmp::Ordering::Greater));
                let result = evaluate::evaluate(
                    &program,
                    entry,
                    &[BigUint::from(left), BigUint::from(right)],
                    evaluate::Config::default(),
                    &mut evaluate::RejectHost,
                )
                .unwrap();
                assert_eq!(
                    result.returned().unwrap(),
                    &[BigUint::from(expected)],
                    "{format:?}: {left:x}, {right:x}"
                );
            }
        }
    }
}
