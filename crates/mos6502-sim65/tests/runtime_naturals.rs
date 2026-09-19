use faun::ir::{Class, Program};
use faun::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;

#[test]
fn runtime_images_are_rejected_until_frame_and_image_budgets_are_checked() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 42);
        let natural = b.convert(Class::Natural, value);
        let result = b.convert(Class::Word, natural);
        b.ret(&[result])
    });
    let error = Mos6502Sim65.compile(&p).unwrap_err();
    assert!(error.contains("checked image/frame limits"), "{error}");
}
