include!("../../faun/tests/support/runtime_naturals.rs");

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&faun_wasm32_wasi::Wasm32Wasi, Some("wasmtime"));
}
