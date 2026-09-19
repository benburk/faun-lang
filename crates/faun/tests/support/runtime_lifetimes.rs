// Shared by machine-IR ownership tests and real x86/wasm integration tests.
use super::ir::{
    Binary, Builder, Class, FunctionId, Offset, Program, Relation, Returns, Terminator, ValueId,
    Width,
};
use super::targets::Target;

pub(super) const ITERATIONS: u64 = 384;
const OUTPUT_BYTES: usize = 20;
pub(super) const HEAP_BYTES: usize = 512;

/// The full result is 2^128 + argc * ITERATIONS, not merely its low exit byte.
pub(super) fn expected(argc: u64) -> Vec<u8> {
    let mut bytes = vec![0; OUTPUT_BYTES];
    bytes[..8].copy_from_slice(&(argc * ITERATIONS).to_le_bytes());
    bytes[16] = 1;
    bytes
}

pub(super) fn program(early_return: bool) -> Program {
    let (mut p, main) = Program::new("main");
    let identity = p.declare("borrowed identity", &[Class::Natural], &[Class::Natural]);
    p.define(identity, |b, args| b.ret(&[args[0]]));
    let accumulate = accumulator(&mut p, identity, early_return);
    let serialize = serializer(&mut p);
    let argc = p.external("argc", "argc", &[], Returns::Values(&[Class::Word]));
    let write = p.external(
        "write",
        "write",
        &[Class::Address, Class::Word],
        Returns::Values(&[]),
    );
    let buffer = p.global(&[0; OUTPUT_BYTES]);
    p.define(main, |b, _| {
        let argc = b.call(argc, &[])[0];
        let iterations = b.constant(Class::Word, ITERATIONS);
        let answer = b.call(accumulate, &[argc, iterations])[0];
        let address = b.address_of(buffer);
        b.call(serialize, &[answer, address]);
        let length = b.constant(Class::Word, u64::try_from(OUTPUT_BYTES).unwrap());
        b.call(write, &[address, length]);
        let status = b.constant(Class::Word, 0);
        // Cleanup must run on Return, not be skipped by a terminal exit effect.
        b.ret(&[status])
    });
    p
}

fn accumulator(p: &mut Program, identity: FunctionId, early_return: bool) -> FunctionId {
    let function = p.declare("accumulate", &[Class::Word, Class::Word], &[Class::Natural]);
    p.define(function, |b, args| {
        // This mortal ancestor is captured and read after every nested exit.
        let increment = b.convert(Class::Natural, args[0]);
        let max = b.constant(Class::Natural, u64::MAX);
        let one = b.constant(Class::Natural, 1);
        let high = b.binary(Binary::Add, max, one);
        let initial = b.binary(Binary::Mul, high, high);
        let zero = b.constant(Class::Word, 0);
        let result = b.loop_(&[initial, zero], &[Class::Natural], |b, state| {
            let next = b.binary(Binary::Add, state[0], increment);
            let alias = b.call(identity, &[next])[0];
            let one = b.constant(Class::Word, 1);
            let index = b.binary(Binary::Add, state[1], one);
            let done = b.compare(Relation::Equal, index, args[1]);
            let inner = nested(b, alias, done, early_return);
            b.if_(
                done,
                &[],
                |b| b.break_(&[inner]),
                |b| b.continue_(&[inner, index]),
            );
            Terminator::UNREACHABLE
        });
        b.ret(&result)
    });
    function
}

fn nested(b: &mut Builder<'_>, value: ValueId, done: ValueId, early_return: bool) -> ValueId {
    let zero = b.constant(Class::Word, 0);
    b.loop_(&[value, zero], &[Class::Natural], |b, state| {
        let first = b.compare(Relation::Equal, state[1], zero);
        b.if_(
            first,
            &[],
            |b| {
                let one = b.constant(Class::Word, 1);
                b.continue_(&[state[0], one])
            },
            |b| b.yield_(&[]),
        );
        b.if_(
            done,
            &[],
            |b| {
                if early_return {
                    // Unwind both loops, their branch scopes, and the root's
                    // owners before the outer loop's result has been defined.
                    b.ret(&[state[0]])
                } else {
                    b.break_(&[state[0]])
                }
            },
            |b| b.break_(&[state[0]]),
        );
        Terminator::UNREACHABLE
    })[0]
}

fn serializer(p: &mut Program) -> FunctionId {
    let function = p.declare("serialize borrowed", &[Class::Natural, Class::Address], &[]);
    p.define(function, |b, args| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let length = b.constant(Class::Word, u64::try_from(OUTPUT_BYTES).unwrap());
        let radix = b.constant(Class::Natural, 256);
        b.loop_(&[args[0], zero], &[], |b, state| {
            let byte = b.convert(Class::Fixed { bits: 8 }, state[0]);
            let base = b.convert(Class::Word, args[1]);
            let address = b.binary(Binary::Add, base, state[1]);
            let address = b.convert(Class::Address, address);
            b.store(Width::Byte, address, Offset::Bytes(0), byte);
            // Quotients are iteration-local, rather than twenty simultaneously
            // live temporaries in main. Even the serializer must reuse memory.
            let rest = b.binary(Binary::Div, state[0], radix);
            let index = b.binary(Binary::Add, state[1], one);
            let done = b.compare(Relation::Equal, index, length);
            b.if_(
                done,
                &[],
                |b| b.break_(&[]),
                |b| b.continue_(&[rest, index]),
            );
            Terminator::UNREACHABLE
        });
        b.ret(&[])
    });
    function
}

pub(super) fn check(target: &dyn Target, runner: Option<&str>, early_return: bool) {
    let p = program(early_return);
    let scalar = super::ir::legalize(
        &p,
        super::ir::natural::Config {
            word_bits: target.word(),
            heap_bytes: HEAP_BYTES,
        },
    )
    .expect("legalization with a target-matching tiny heap");
    let artifact = target
        .compile(&scalar)
        .expect("scalar compilation")
        .remove(0);
    let dir = std::env::temp_dir().join(format!(
        "faun-lifetimes-{}-{}-{early_return}",
        target.name(),
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("program{}", artifact.extension));
    std::fs::write(&path, artifact.bytes).unwrap();
    #[cfg(unix)]
    if artifact.executable {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    for argc in [1, 3] {
        execute(&path, runner, argc);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

fn execute(path: &std::path::Path, runner: Option<&str>, argc: u64) {
    use std::process::Command;
    let mut command = runner.map_or_else(
        || Command::new(path),
        |runner| {
            let mut command = Command::new(runner);
            command.arg(path);
            command
        },
    );
    for _ in 1..argc {
        command.arg("dynamic-increment");
    }
    let output = command.output().expect("native lifetime fixture runner");
    assert_eq!(
        output.status.code(),
        Some(0),
        "tiny-heap execution failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, expected(argc), "all 20 bytes, argc={argc}");
}
