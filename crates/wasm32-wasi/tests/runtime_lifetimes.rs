use faun_core::{ir, targets};

#[path = "../../core/tests/support/runtime_lifetimes.rs"]
mod fixture;

#[test]
fn nested_loops_reuse_a_tiny_heap_and_preserve_full_naturals() {
    for early_return in [false, true] {
        fixture::check(
            &faun_wasm32_wasi::Wasm32Wasi,
            Some("wasmtime"),
            early_return,
        );
    }
}
