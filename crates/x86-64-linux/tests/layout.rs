use faun_core::ir::{Class, Program, legalize, natural::Config};
use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;

#[test]
fn checked_native_compilation_rejects_foreign_runtime_layouts() {
    let (mut program, main) = Program::new("seven");
    program.define(main, |b, _| {
        let seven = b.constant(Class::Natural, 7);
        let status = b.convert(Class::Word, seven);
        b.ret(&[status]);
    });
    let foreign = legalize(
        &program,
        Config {
            word_bits: 32,
            heap_bytes: 128,
            grows: false,
        },
    )
    .unwrap();
    for error in [
        X86_64Linux.accepts(&foreign).unwrap_err(),
        X86_64Linux.prepare(&foreign).unwrap_err(),
        X86_64Linux.compile_machine_ir(&foreign).unwrap_err(),
    ] {
        assert!(error.contains("layout"));
    }
    let native = legalize(
        &program,
        Config {
            word_bits: 64,
            heap_bytes: 128,
            grows: false,
        },
    )
    .unwrap();
    assert!(!X86_64Linux.compile_machine_ir(&native).unwrap().is_empty());
}
