use super::*;

#[test]
fn renders_value_classes_and_resolved_transfers_without_pool_runs() {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let one = b.constant(Class::fixed(1), 1);
        let word = b.convert(Class::Word, one);
        b.ret(&[word]);
    });
    validate(&program).unwrap();
    assert_eq!(
        program.render(),
        concat!(
            "# Classes are per-value representation requirements, not source types.\n",
            "# low..high is every value one can be; it is a fit requirement, not a\n",
            "# wrapping type, and a target holds one in whatever it has that is wide\n",
            "# enough. A narrower sink requires a fit proof or an explicit conversion.\n\n",
            "fn f0 main() -> (word) = r0\n\nr0():\n",
            "  v0: 0..1 = const 1\n",
            "  v1: word = convert v0 to word\n",
            "  Return(v1)\n",
        )
    );
}

#[test]
fn distinguishes_pending_external_unit_and_never() {
    let (mut program, main) = Program::new("main");
    program.external("observe", &[Class::Address], Returns::Values(&[]));
    let stop = program.external("exit", &[Class::Word], Returns::Never);
    let pending = program.render();
    assert!(pending.contains("= pending r0"));
    assert!(pending.contains("observe(v0: address) -> () = external"));
    assert!(pending.contains("exit(v0: word) -> never = external"));
    program.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.call(stop, &[zero]);
    });
    validate(&program).unwrap();
    let rendered = program.render();
    assert!(rendered.contains("call exit(v0)  # f2\n  <no terminator>"));
    assert!(!rendered.contains("pending"));
    assert!(!rendered.contains("Return"));
    assert_eq!(Program::default().render(), "");
}

#[test]
fn named_calls_keep_ids_to_distinguish_duplicate_names() {
    let program = crate::programs::external::interleaved();
    validate(&program).unwrap();
    let text = program.render();
    for fragment in [
        "fn f1 read_byte!() -> (0..511) = external",
        "fn f2 read_byte!(v0: word) -> (word) = r1",
        "fn f5 read_byte!() -> (0..511) = external",
        "call read_byte!()  # f1",
        "call read_byte!()  # f5",
    ] {
        assert!(text.contains(fragment), "missing {fragment:?} in {text}");
    }
    // Both an internal function and an external provider can have this name.
    for (name, id) in [("read_byte!", 2), ("exit!", 4), ("exit!", 6)] {
        assert!(
            text.lines().any(|line| {
                line.contains(&format!("call {name}(")) && line.ends_with(&format!("  # f{id}"))
            }),
            "missing call to {name}, f{id}, in {text}"
        );
    }
}

#[test]
fn renders_data_memory_and_compact_natural_constants() {
    let (mut program, main) = Program::new("main");
    let buffer = program.global(&[0, 0]);
    program.define(main, |b, _| {
        let wide = b.natural(&(num_bigint::BigUint::from(1u8) << 16usize));
        let low = b.convert(Class::Word, wide);
        let address = b.address_of(buffer);
        b.store(Width::Byte, address, Offset::Bytes(1), low);
        let loaded = b.load(Width::Byte, address, Offset::Bytes(1));
        b.ret(&[loaded]);
    });
    validate(&program).unwrap();
    let text = program.render();
    for fragment in [
        "data = [00, 00, 01]",
        "globals = [00, 00]",
        "d0 = Globals[0..2]",
        "d1 = Data[0..3]",
        "v0: natural = natural d1",
        "v2: address = address d0",
        "store.Byte v2, Bytes(1), v1",
        "v3: word = load.Byte v2, Bytes(1)",
    ] {
        assert!(text.contains(fragment), "missing {fragment:?} in {text}");
    }
}

#[test]
fn renders_structured_edges_and_arithmetic_in_execution_order() {
    let program = crate::programs::carries_a_total_into_an_arm(3);
    validate(&program).unwrap();
    let before = format!("{program:?}");
    let text = program.render();
    for fragment in [
        "loop r",
        "if v",
        " then r",
        " else r",
        "Continue(",
        "Break(",
        "Add v",
        "Sub v",
    ] {
        assert!(text.contains(fragment), "missing {fragment:?} in {text}");
    }
    assert!(!text.contains("Range"));
    assert_eq!(
        before,
        format!("{program:?}"),
        "inspection does not rewrite IR"
    );
}
