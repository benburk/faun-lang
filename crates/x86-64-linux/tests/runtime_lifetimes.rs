use faun_core::{ir, targets};

#[path = "../../core/tests/support/runtime_lifetimes.rs"]
mod fixture;

#[test]
fn nested_loops_reuse_a_tiny_heap_and_preserve_full_naturals() {
    for early_return in [false, true] {
        fixture::check(&faun_x86_64_linux::X86_64Linux, None, early_return);
    }
}
