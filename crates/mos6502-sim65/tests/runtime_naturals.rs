use faun_core::ir::{Class, Program};
use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;

/// Raw acceptance still enforces the native convention; the compilation
/// wrappers fit a program to it first, so none of these is refused.
#[test]
fn compilation_wrappers_fit_programs_to_native_abi_and_transfer_limits() {
    use faun_core::programs::abi;
    for p in [
        abi::function(4, 1),
        abi::function(5, 1),
        abi::function(0, 2),
        abi::pointer_pair(),
        abi::region(abi::Transfer::If, 3),
        abi::region(abi::Transfer::LoopState, 3),
        abi::region(abi::Transfer::LoopResults, 3),
    ] {
        let prepared = Mos6502Sim65.prepare(&p).unwrap();
        Mos6502Sim65.accepts(&prepared).unwrap();
        Mos6502Sim65.compile_machine_ir(&p).unwrap();
    }
}

#[test]
fn runtime_images_are_rejected_until_frame_and_image_budgets_are_checked() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 42);
        let natural = b.convert(Class::Natural, value);
        let result = b.convert(Class::Word, natural);
        b.ret(&[result]);
    });
    let error = Mos6502Sim65.compile_machine_ir(&p).unwrap_err();
    assert!(error.contains("checked image/frame limits"), "{error}");
}
