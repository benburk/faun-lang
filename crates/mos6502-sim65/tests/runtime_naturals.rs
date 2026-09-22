use faun_core::ir::{Class, Program};
use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;

#[test]
fn compilation_wrappers_apply_native_abi_and_transfer_limits() {
    use faun_core::programs::abi;
    for (p, accepted) in [
        (abi::function(4, 1), true),
        (abi::function(5, 1), false),
        (abi::function(0, 2), false),
        (abi::pointer_pair(), false),
        (abi::region(abi::Transfer::If, 3), false),
        (abi::region(abi::Transfer::LoopState, 3), false),
        (abi::region(abi::Transfer::LoopResults, 3), false),
    ] {
        assert_eq!(Mos6502Sim65.prepare(&p).is_ok(), accepted);
        assert_eq!(Mos6502Sim65.compile(&p).is_ok(), accepted);
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
    let error = Mos6502Sim65.compile(&p).unwrap_err();
    assert!(error.contains("checked image/frame limits"), "{error}");
}
