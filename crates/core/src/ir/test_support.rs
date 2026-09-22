//! Assertions shared by representation and ownership tests.
use super::{Origin, Program, evaluate::Evaluation, natural::Config};

pub(super) fn word(bytes: &[u8]) -> usize {
    let mut value = [0; 8];
    value[..bytes.len()].copy_from_slice(bytes);
    usize::try_from(u64::from_le_bytes(value)).expect("test size")
}

pub(super) fn no_live_objects(p: &Program, result: &Evaluation, config: Config) {
    assert!(
        result.returned().is_some(),
        "unexpected runtime exhaustion: {result:?}"
    );
    let heap = p
        .spans
        .iter()
        .rev()
        .find(|span| {
            span.origin == Origin::Globals
                && usize::try_from(span.len).unwrap() == config.heap_bytes
        })
        .expect("runtime private heap");
    let width = usize::from(config.word_bits / 8);
    let mut at = usize::try_from(heap.start).unwrap();
    let end = at + config.heap_bytes;
    while at < end {
        assert!(at + 3 * width <= end, "header escapes heap");
        let size = word(&result.globals[at..at + width]);
        assert!(
            size >= 3 * width && size.is_multiple_of(width),
            "bad block at {at}"
        );
        assert!(size <= end - at, "block escapes heap");
        assert_eq!(
            word(&result.globals[at + width..at + 2 * width]),
            0,
            "mortal claim remains at {at} after return"
        );
        at += size;
    }
    assert_eq!(at, end, "heap block chain");
}
