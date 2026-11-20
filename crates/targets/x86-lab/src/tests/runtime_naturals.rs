use super::faun;

include!("../../../../core/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    source_check(&crate::X86_64Linux, None);
}

/// Raw acceptance still enforces the native convention; the compilation
/// wrappers fit a program to it first, managed results included.
#[test]
fn compilation_wrappers_fit_programs_to_native_abi_limits() {
    use faun_core::programs::abi;
    let (mut pair_of_naturals, main) = Program::new("main");
    pair_of_naturals.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let pair =
        pair_of_naturals.declare("pair", &[Class::Natural], &[Class::Natural, Class::Natural]);
    pair_of_naturals.define(pair, |b, args| b.ret(&[args[0], args[0]]));
    let target = crate::X86_64Linux;
    for p in [
        pair_of_naturals,
        abi::function(6, 1),
        abi::function(7, 1),
        abi::function(0, 2),
        abi::pointer_pair(),
        abi::region(abi::Transfer::LoopState, 3),
    ] {
        let prepared = target.prepare(&p).unwrap();
        target.accepts(&prepared).unwrap();
        target.compile_machine_ir(&p).unwrap();
    }
}

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&crate::X86_64Linux, None);
}

/// Naturals passed as words where they only reach comparisons, and kept
/// where they do not, order alike on this machine.
#[test]
fn comparisons_of_naturals_passed_as_words_answer_as_the_naturals_do() {
    use faun_core::programs::comparisons;
    for (p, answer) in [
        (comparisons::of_words().0, 3),
        (comparisons::one_past_a_word(), 5),
        (comparisons::a_compared_peer_escapes(), 1),
    ] {
        assert_eq!(
            super::shared::status(&super::TARGET.prepare(&p).unwrap()),
            answer
        );
    }
}

const ROTATE_PROGRAM: &str = r#"
import std.host {Host}

main! : Host -> []
main!(host) -> (
  read = host.stdin.read!(2)
  read is Ok(Data(bytes)) else return host.exit!(1)
  x = bytes.get(0).ok_or(0).to_nat()
  n = bytes.get(1).ok_or(0).to_nat()
  a = U8.of_nat(x)
  b = U16.of_nat(x * 256 + 5)
  c = U32.of_nat(x * 16777216 + 5)
  d = U64.of_nat(x * 72057594037927936 + 5)
  host.print!([a.rotate_left(n).to_str(), b.rotate_left(n).to_str(),
    c.rotate_left(n).to_str(), d.rotate_left(7).to_str()].join(","))
  host.exit!(0)
)
"#;

#[test]
fn source_rotates_select_native_widths_and_wrap_the_count() {
    use crate::machine::Inst;
    let target = crate::X86_64Linux;
    let prepared = target
        .prepare(&faun::lower(ROTATE_PROGRAM, &target).unwrap())
        .unwrap();
    let code = crate::selected::select_and_allocate(&prepared).unwrap();
    for (width, count) in [(8, None), (16, None), (32, None), (64, Some(7))] {
        assert!(
            code.instructions().iter().any(
                |i| matches!(i, Inst::RotateLeft { bits, by, .. } if (*bits, *by) == (width, count))
            ),
            "missing {width}-bit ROL"
        );
    }
    for n in [0, 1, 7, 8, 15, 16, 31, 32, 33, 255] {
        let input = [0x81, n];
        let n = u32::from(n);
        let expected = format!(
            "{},{},{},{}",
            0x81_u8.rotate_left(n),
            0x8105_u16.rotate_left(n),
            0x8100_0005_u32.rotate_left(n),
            0x8100_0000_0000_0005_u64.rotate_left(7)
        );
        assert_eq!(
            super::shared::execute_with_input(&prepared, &input),
            (0, expected)
        );
    }
}

#[test]
fn unsigned_comparisons_at_the_sign_bit_test_the_full_operand_width() {
    use crate::machine::{Condition, Inst};
    use faun_core::ir::Relation;
    for bits in [32, 64] {
        let word = Class::fixed(bits);
        let sign_bit = 1_u64 << (bits - 1);
        let (mut p, main) = Program::new("main");
        let below = p.declare("below", &[word], &[Class::Word]);
        p.define(below, |b, args| {
            let limit = b.constant(word, sign_bit);
            let less = b.compare(Relation::Less, args[0], limit);
            b.ret(&[less]);
        });
        p.define(main, |b, _| {
            let mut result = b.constant(Class::Word, 0);
            for value in [0, sign_bit - 1, sign_bit, sign_bit + 1] {
                let next = b.constant(word, value);
                let less = b.call_one(below, &[next]);
                result = b.binary(Binary::Add, result, result);
                result = b.binary(Binary::Add, result, less);
            }
            b.ret(&[result]);
        });
        let prepared = super::TARGET.prepare(&p).unwrap();
        let code = crate::selected::select_and_allocate(&prepared).unwrap();
        assert!(
            code.instructions().iter().any(|inst| matches!(
                inst,
                Inst::SetIf {
                    condition: Condition::NotSign,
                    ..
                }
            )),
            "missing {bits}-bit sign test"
        );
        assert_eq!(super::shared::status(&prepared), 0b1100);
    }
}
