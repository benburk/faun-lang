#[test]
fn nested_loops_reuse_a_tiny_heap_and_preserve_full_naturals() {
    for early_return in [false, true] {
        crate::lifetime_fixture::check(&crate::X86_64Linux, None, early_return);
    }
}
