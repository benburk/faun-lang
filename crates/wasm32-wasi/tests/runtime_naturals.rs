include!("../../core/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    source_check(&faun_wasm32_wasi::Wasm32Wasi, Some("wasmtime"));
}

#[test]
fn compilation_wrappers_preserve_supported_multivalue_abis() {
    use faun_core::programs::abi;
    let target = faun_wasm32_wasi::Wasm32Wasi;
    for p in [
        abi::function(7, 3),
        abi::pointer_pair(),
        abi::region(abi::Transfer::LoopState, 3),
    ] {
        target.prepare(&p).expect("wasm ABI supports this shape");
        target.compile(&p).expect("compile has no native-only gate");
    }
}

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&faun_wasm32_wasi::Wasm32Wasi, Some("wasmtime"));
}
