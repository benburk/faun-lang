include!("../../faun/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    let text = "type Nat Zero Succ(Nat)\n\
        type Bool False True\n\
        add(a Zero) -> a\n\
        add(a Succ(b)) -> Succ(add(a b))\n\
        less_than(Zero Zero) -> False\n\
        less_than(Zero Succ(b)) -> True\n\
        less_than(Succ(a) Zero) -> False\n\
        less_than(Succ(a) Succ(b)) -> less_than(a b)\n\
        status(False) -> Zero\n\
        status(True) -> Succ(Zero)\n\
        main!(h) -> n = argc!(h) exit!(h status(less_than(n add(n n))))";
    let target = faun_x86_64_linux::X86_64Linux;
    let p = faun::read(text, &target.routines()).expect("bounded effect after runtime computation");
    assert!((0..p.values_count()).any(|at| p.class(faun::ir::ValueId::at(at)) == Class::Natural));
    target.compile(&p).expect("source runtime compilation");
}

#[test]
fn native_compilation_rejects_unimplemented_multiple_return_abi() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero])
    });
    let pair = p.declare("pair", &[Class::Natural], &[Class::Natural, Class::Natural]);
    p.define(pair, |b, args| b.ret(&[args[0], args[0]]));
    let error = faun_x86_64_linux::X86_64Linux.compile(&p).unwrap_err();
    assert!(error.contains("one result"), "{error}");
}

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&faun_x86_64_linux::X86_64Linux, None);
}
