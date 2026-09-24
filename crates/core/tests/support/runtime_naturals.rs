// Shared native-backend runtime bigint fixture (included by integration tests).
use faun_core::ir::{Binary, Class, Offset, Program, Width};
use faun_core::targets::Target;

#[expect(
    clippy::too_many_lines,
    reason = "shared arithmetic graph and full-byte projection"
)]
fn program() -> Program {
    let (mut p, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
    let routines = faun_core::platform::Routines::builtin();
    let write = routines.declare(&mut p, "write!");
    let bytes = p.global(&[0; 80]);
    p.define(main, |b, params| {
        let count = params[0];
        let count = b.convert(Class::Natural, count);
        let max = b.constant(Class::Natural, u64::MAX);
        let one = b.constant(Class::Natural, 1);
        let large = b.binary(Binary::Add, max, one);
        let large = b.binary(Binary::Add, large, count);
        let rhs = b.constant(Class::Natural, 65537);
        let address = b.address_of(bytes);
        let radix = b.constant(Class::Natural, 256);
        let mut powers = vec![one];
        for i in 1..16 {
            powers.push(b.binary(Binary::Mul, powers[i - 1], radix));
        }
        for (index, op) in [
            Binary::Add,
            Binary::Sub,
            Binary::Mul,
            Binary::Div,
            Binary::Mod,
        ]
        .into_iter()
        .enumerate()
        {
            let value = b.binary(op, large, rhs);
            for (digit, &power) in powers.iter().enumerate() {
                let part = b.binary(Binary::Div, value, power);
                let byte = b.convert(Class::fixed(8), part);
                b.store(
                    Width::Byte,
                    address,
                    Offset::Bytes(i32::try_from(index * 16 + digit).unwrap()),
                    byte,
                );
            }
        }
        let length = b.constant(Class::Word, 80);
        b.call(write, &[address, length]);
        let status = b.constant(Class::Word, 0);
        b.ret(&[status]);
    });
    p
}

fn execute(
    p: &Program,
    target: &dyn Target,
    runner: Option<&str>,
    label: &str,
    verify: impl Fn(u128, std::process::Output),
) {
    use std::fs;
    use std::process::Command;
    let image = target.compile(p).expect("runtime compilation");
    let dir = std::env::temp_dir().join(format!(
        "faun-bigint-{label}-{}-{}",
        target.name(),
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let path = target.write(&image, &dir.join("program")).unwrap();
    for extra in [0, 2] {
        let mut command = runner.map_or_else(
            || Command::new(&path),
            |runner| {
                let mut command = Command::new(runner);
                command.arg(&path);
                command
            },
        );
        for _ in 0..extra {
            command.arg("dynamic-input");
        }
        verify(extra, output(&mut command));
    }
    fs::remove_dir_all(dir).unwrap();
}

/// Run it, retrying while the kernel still counts the file as open for
/// writing.
///
/// Tests run beside each other, and a process forked by one of them holds
/// every file the others had open at that moment. The exec of a file so
/// held is refused until that process is on its way, which is a race
/// between tests rather than anything a program did.
fn output(command: &mut std::process::Command) -> std::process::Output {
    for _ in 0..64 {
        match command.output() {
            Err(error) if error.kind() == std::io::ErrorKind::ExecutableFileBusy => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            held => return held.expect("target runner"),
        }
    }
    panic!("the target runner stayed busy")
}

fn check(target: &dyn Target, runner: Option<&str>) {
    let p = program();
    assert!(
        target.accepts(&p).is_err(),
        "raw emission is not bigint legalization"
    );
    execute(&p, target, runner, "full-bytes", |extra, output| {
        assert!(
            output.status.success(),
            "{:?}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let a = (1u128 << 64) + extra + 1;
        let b = 65537;
        let expected: Vec<_> = [a + b, a - b, a * b, a / b, a % b]
            .into_iter()
            .flat_map(u128::to_le_bytes)
            .collect();
        assert_eq!(output.stdout, expected, "full 80-byte arithmetic output");
    });
}

/// Ordinary repeated squaring builds 2^128, then divides it back out of a
/// product with the argument count: the answer is 1 exactly when the count is.
const SQUARES: &str = "import std.host {Host}

                       square : Nat -> Nat
                       square(n) -> n * n

                       main! : Host -> []
                       main!(host) ->
                         a = square(2)
                         b = square(a)
                         c = square(b)
                         d = square(c)
                         e = square(d)
                         f = square(e)
                         huge = square(f)
                         count = host.argc
                         product = huge * count
                         quotient = product / huge
                         host.exit!(quotient.equals(1).to_nat())";

fn source_check(target: &dyn Target, runner: Option<&str>) {
    let p = faun::lower(SQUARES, target).expect("bounded effect after runtime arithmetic");
    for wanted in [Binary::Mul, Binary::Div] {
        assert!(
            p.functions().iter().filter_map(faun_core::ir::Function::body).any(|body| p.every(body).any(|op| {
                matches!(*op, faun_core::ir::Op::Binary { op, left, .. }
                if op == wanted && p.class(left) == Class::Natural)
            })),
            "runtime {wanted:?} must survive source optimization"
        );
    }
    assert!(
        p.functions().iter().filter_map(faun_core::ir::Function::body).any(|body| p.every(body).any(|op| {
            matches!(*op, faun_core::ir::Op::NaturalConstant(data) if p.datum(data).len >= 17)
        })),
        "ordinary repeated squaring must construct at least 2^128"
    );
    execute(&p, target, runner, "source", |extra, output| {
        let expected = i32::from(extra == 0);
        assert_eq!(
            output.status.code(),
            Some(expected),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stdout.is_empty());
    });
}
