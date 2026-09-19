include!("../../faun/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    source_check(&faun_x86_64_linux::X86_64Linux, None);
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
    assert!(error.contains("at most 1"), "{error}");
}

#[test]
fn compilation_wrappers_apply_native_abi_limits() {
    use faun::programs::abi;
    let target = faun_x86_64_linux::X86_64Linux;
    for (p, accepted) in [
        (abi::function(6, 1), true),
        (abi::function(7, 1), false),
        (abi::function(0, 2), false),
        (abi::pointer_pair(), false),
        (abi::region(abi::Transfer::LoopState, 3), true),
    ] {
        assert_eq!(target.prepare(&p).is_ok(), accepted);
        assert_eq!(target.compile(&p).is_ok(), accepted);
    }
}

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&faun_x86_64_linux::X86_64Linux, None);
}
