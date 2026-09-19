// Shared native-backend runtime bigint fixture (included by integration tests).
use faun::ir::{Binary, Class, Offset, Program, Width};
use faun::targets::Target;

#[expect(
    clippy::too_many_lines,
    reason = "shared arithmetic graph and full-byte projection"
)]
fn program() -> Program {
    let (mut p, main) = Program::new("main");
    let routines = faun::platform::Routines::builtin();
    let argc = routines.declare(&mut p, "argc");
    let write = routines.declare(&mut p, "write");
    let bytes = p.global(&[0; 80]);
    p.define(main, |b, _| {
        let count = b.call_one(argc, &[]);
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
                let byte = b.convert(Class::Fixed { bits: 8 }, part);
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
    let artifact = target.compile(p).expect("runtime compilation").remove(0);
    let dir = std::env::temp_dir().join(format!(
        "faun-bigint-{label}-{}-{}",
        target.name(),
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("program{}", artifact.extension));
    fs::write(&path, artifact.bytes).unwrap();
    #[cfg(unix)]
    if artifact.executable {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    }
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
        verify(extra, command.output().expect("target runner"));
    }
    fs::remove_dir_all(dir).unwrap();
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

fn source_check(target: &dyn Target, runner: Option<&str>) {
    let text = format!(
        "{}\n{}",
        include_str!("../../../../standard/nat.fn"),
        include_str!("runtime_naturals.fn")
    );
    let p = faun::read(&text, &target.routines()).expect("bounded effect after runtime arithmetic");
    for wanted in [Binary::Mul, Binary::Div] {
        assert!(
            p.functions().iter().filter_map(faun::ir::Function::body).any(|body| p.every(body).any(|op| {
                matches!(*op, faun::ir::Op::Binary { op, left, .. }
                if op == wanted && p.class(left) == Class::Natural)
            })),
            "runtime {wanted:?} must survive source optimization"
        );
    }
    assert!(
        p.functions().iter().filter_map(faun::ir::Function::body).any(|body| p.every(body).any(|op| {
            matches!(*op, faun::ir::Op::NaturalConstant(data) if p.datum(data).len >= 17)
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
