#[path = "../../core/tests/support/faun.rs"]
mod faun;

include!("../../core/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    source_check(&faun_x86_64_linux::X86_64Linux, None);
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
    let target = faun_x86_64_linux::X86_64Linux;
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
    check(&faun_x86_64_linux::X86_64Linux, None);
}
