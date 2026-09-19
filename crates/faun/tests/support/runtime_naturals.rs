// Shared native-backend runtime bigint fixture (included by integration tests).
use faun::ir::{Binary, Class, Offset, Program, Width};
use faun::targets::Target;

#[expect(
    clippy::too_many_lines,
    reason = "shared arithmetic graph and full-byte projection"
)]
fn program() -> Program {
    let (mut p, main) = Program::new("main");
    let argc = p.platform("argc");
    let write = p.platform("write");
    let bytes = p.global(&[0; 80]);
    p.define(main, |b, _| {
        let count = b.platform_call(argc, &[])[0];
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
        b.platform_call(write, &[address, length]);
        let status = b.constant(Class::Word, 0);
        b.ret(&[status])
    });
    p
}

#[expect(
    clippy::too_many_lines,
    reason = "native file setup, execution and exact byte comparison"
)]
fn check(target: &dyn Target, runner: Option<&str>) {
    use std::fs;
    use std::process::Command;
    let p = program();
    assert!(
        target.accepts(&p).is_err(),
        "raw emission is not bigint legalization"
    );
    let artifact = target.compile(&p).expect("runtime compilation").remove(0);
    let dir = std::env::temp_dir().join(format!(
        "faun-bigint-{}-{}",
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
        let output = command.output().expect("target runner");
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
    }
    fs::remove_dir_all(dir).unwrap();
}
