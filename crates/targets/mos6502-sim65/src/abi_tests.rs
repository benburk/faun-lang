use faun_core::ir::{Binary, Class, Program, validate};
use faun_core::programs::abi::{self, Transfer};
use faun_core::targets::Target;

use crate::Mos6502Sim65;

#[test]
fn rejects_valid_ir_outside_the_function_calling_convention() {
    for (params, returns, diagnostic) in [(5, 1, "5 parameters"), (0, 2, "2 results")] {
        let program = abi::function(params, returns);
        validate(&program).unwrap();
        let error = Mos6502Sim65.accepts(&program).unwrap_err();
        assert!(error.contains("mos6502-sim65 function `wide`"), "{error}");
        assert!(error.contains(diagnostic), "{error}");
    }
}

#[test]
fn cannot_silently_drop_a_second_pointer_result() {
    let program = abi::pointer_pair();
    validate(&program).unwrap();
    let error = Mos6502Sim65.accepts(&program).unwrap_err();
    assert!(error.contains("function `pair` has 2 results"), "{error}");
}

#[test]
fn region_transfer_limit_does_not_restrict_function_parameters() {
    let program = abi::function(4, 1);
    validate(&program).unwrap();
    Mos6502Sim65.accepts(&program).unwrap();
    Mos6502Sim65.emit(&program);
    for (kind, diagnostic) in [
        (Transfer::If, "3 if results"),
        (Transfer::LoopState, "3 loop parameters"),
        (Transfer::LoopResults, "3 loop results"),
    ] {
        let program = abi::region(kind, 3);
        validate(&program).unwrap();
        let error = Mos6502Sim65.accepts(&program).unwrap_err();
        assert!(error.contains("function `main` region"), "{error}");
        assert!(error.contains(diagnostic), "{error}");
        let program = abi::region(kind, 2);
        validate(&program).unwrap();
        Mos6502Sim65.accepts(&program).unwrap();
        Mos6502Sim65.emit(&program);
    }
}

/// A function holding `pairs` places at once: that many values worked out,
/// then added up, so each is wanted until its turn comes, and the first sum
/// is wanted beside all of them.
fn frame(pairs: usize) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let held: Vec<_> = (1..pairs)
            .map(|_| b.binary(Binary::Add, zero, zero))
            .collect();
        let total = held[1..]
            .iter()
            .fold(held[0], |total, &value| b.binary(Binary::Add, total, value));
        b.ret(&[total]);
    });
    program
}

#[test]
fn checks_actual_spill_plan_before_emission() {
    // Sixteen home pairs are not part of the byte-indexed software frame,
    // and a slot is held by one value at a time.
    let fitting = frame(16 + 255);
    validate(&fitting).unwrap();
    Mos6502Sim65.accepts(&fitting).unwrap();
    Mos6502Sim65.emit(&fitting);
    let oversized = frame(16 + 256);
    validate(&oversized).unwrap();
    let error = Mos6502Sim65.accepts(&oversized).unwrap_err();
    assert!(
        error.contains("function `main`: frame exceeds 510 bytes"),
        "{error}"
    );
}
