use crate::X86_64Linux;
use crate::ir::{Class, Program, legalize, natural::Config};
use crate::targets::Target;

#[test]
fn checked_native_compilation_rejects_foreign_runtime_layouts() {
    let (mut program, main) = Program::new("seven");
    program.define(main, |b, _| {
        let seven = b.constant(Class::Natural, 7);
        let status = b.convert(Class::Word, seven);
        b.ret(&[status]);
    });
    let foreign = legalize(
        &program,
        Config {
            word_bits: 32,
            heap_bytes: 128,
            grows: false,
            inline_small: true,
            inline_counts: false,
            join_routines: false,
        },
    )
    .unwrap();
    for error in [
        X86_64Linux.accepts(&foreign).unwrap_err(),
        X86_64Linux.prepare(&foreign).unwrap_err(),
        X86_64Linux.compile_machine_ir(&foreign).unwrap_err(),
    ] {
        assert!(error.contains("layout"));
    }
    let native = legalize(
        &program,
        Config {
            word_bits: 64,
            heap_bytes: 128,
            grows: false,
            inline_small: true,
            inline_counts: false,
            join_routines: false,
        },
    )
    .unwrap();
    assert!(!X86_64Linux.compile_machine_ir(&native).unwrap().is_empty());
}

#[test]
fn short_table_rows_survive_projection_slicing_and_growth() {
    let source = r#"
import std.host {Host}

texts : List(Str)
texts = ["", "éééééééééééé", "abcdefghijklmnopqrstuvw"]

raw : List(List(U8))
raw = [[255, 192], [0, 216], [128]]

main! : Host -> []
main!(host) -> (
  at = host.args.len()
  text = texts.get_or(at, "")
  bytes = raw.get_or(at - 1, [])
  tail = text.to_utf8().drop(22)
  grown = bytes.append(42)
  result = [text, Str.hex(tail), Str.hex(bytes), Str.hex(grown)].join("|")
  host.print!(result)
  host.exit!(0)
)
"#;
    let machine = super::faun::lower(source, &super::TARGET).unwrap();
    let prepared = super::TARGET.prepare(&machine).unwrap();
    assert_eq!(
        super::shared::execute(&prepared),
        (0, "éééééééééééé|c3a9|ffc0|ffc02a".into())
    );
}

#[test]
fn a_loop_builds_its_constant_lookup_table_once_and_can_return_a_row() {
    let source = r#"
import std.host {Host}

names : List(Str)
names = ["ash", "beech", "elm"]

pick : (Nat, List(Str), Str) -> Str
pick(n, table, last) -> (
  next = table.get_or(n % table.len(), "")
  if n == 0 then last.concat(next) else pick(n - 1, table, next)
)

main! : Host -> []
main!(host) -> (
  name = pick(host.args.len() + 4, names, "")
  host.print!(name)
  host.exit!(0)
)
"#;
    let machine = super::faun::lower(source, &super::TARGET).unwrap();
    let entry = machine.function(machine.entry()).body().unwrap();
    // This program has one literal byte buffer, the backing for the rows.
    // Its construction must dominate the loop that looks up each name.
    assert!(
        machine
            .walk(entry)
            .any(|(op, _)| matches!(op, crate::ir::Op::BufferKnown { .. }))
    );
    assert_eq!(
        machine
            .every(entry)
            .filter(|op| matches!(op, crate::ir::Op::BufferKnown { .. }))
            .count(),
        1
    );
    let prepared = super::TARGET.prepare(&machine).unwrap();
    assert_eq!(super::shared::execute(&prepared), (0, "beechash".into()));
}
