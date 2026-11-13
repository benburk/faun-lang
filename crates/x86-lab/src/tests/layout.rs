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

#[test]
fn live_slices_survive_overlapping_reads_and_eof() {
    let source = r"
import std.host {Host}

main! : Host -> []
main!(host) -> (
  first = host.stdin.read!(4)
  first is Ok(Data(a)) else return host.exit!(1)
  kept = a.drop(1)
  second = host.stdin.read!(8)
  second is Ok(Data(b)) else return host.exit!(2)
  third = host.stdin.read!(4)
  third is Ok(Data(c)) else return host.exit!(3)
  last = host.stdin.read!(8)
  last is Ok(End) else return host.exit!(4)
  host.print!(Str.hex(c).concat(Str.hex(b)).concat(Str.hex(kept)))
  host.exit!(0)
)
";
    let machine = super::faun::lower(source, &super::TARGET).unwrap();
    let prepared = super::TARGET.prepare(&machine).unwrap();
    assert_eq!(
        super::shared::execute_with_input(&prepared, b"abcdefghijklmnop"),
        (0, "6d6e6f7065666768696a6b6c626364".into())
    );
}

#[test]
fn input_room_covers_every_count_accepted_at_a_parameter() {
    use crate::ir::{Offset, Width};
    let (mut p, main) = Program::new("main");
    let byte = Class::fixed(8);
    let narrow = Class::Held(crate::facts::Facts::at(128));
    let reserve = p.declare("reserve", &[narrow], &[Class::Buffer]);
    p.define(reserve, |b, args| {
        let shape = b.shape(&[byte]);
        let buf = b.buffer_room(args[0], shape);
        b.ret(&[buf]);
    });
    p.define(main, |b, _| {
        // A 255 literal fits the parameter's eight-bit calling convention.
        let count = b.constant(byte, 255);
        let buf = b.call_one(reserve, &[count]);
        let shape = b.shape(&[byte]);
        let last = b.constant(Class::Word, 254);
        let at = b.buffer_at((buf, last), shape);
        let mark = b.constant(Class::Word, 42);
        b.store(Width::Byte, at, Offset::Bytes(0), mark);
        let back = b.load(Width::Byte, at, Offset::Bytes(0));
        b.keep(buf);
        b.ret(&[back]);
    });
    let prepared = super::TARGET.prepare(&p).unwrap();
    assert!(prepared.globals().len() >= 7 * 8 + 255);
    assert_eq!(super::shared::status(&prepared), 42);
}
