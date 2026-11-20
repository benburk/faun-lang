//! Every program the ratchet measures, and the examples that compute with
//! floats, built with no float operation recognized, write what they write
//! when Barb recognizes the standard's float routines.
//!
//! Recognizing a routine only lets a target answer it with an instruction:
//! a table of fingerprints gone stale must leave every program as it was,
//! only slower. So these are built twice for each backend, once as `faun
//! build` builds them and once with every float routine walked, its body
//! compiled as any other definition is. Where the two images are the same,
//! as for a program with no floats, there is nothing to run; where they
//! differ, both run at a small size and must write the same and leave with
//! status zero. A walked routine is ordinary natural-number code that the
//! recognized build never runs on x86-64, so this is also where the
//! backends meet the guard-heavy code the routines are, which once found a
//! comparison read at its narrower operand's width.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use faun_core::targets::{Favour, SymbolTable, Target};
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

fn crates() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// What a program is handed: an argument, or bytes on standard input.
#[derive(Clone, Copy)]
enum Input {
    Argument(&'static str),
    /// What the fasta example writes at 1000, as k-nucleotide reads.
    Fasta,
    /// So many bytes, the same each run.
    Bytes(usize),
    Nothing,
}

/// The suite's programs at sizes a walked float routine keeps to a fraction
/// of a second, the probes, and the examples that print floats.
#[expect(clippy::too_many_lines, reason = "one list of every program")]
fn programs() -> Vec<(PathBuf, Input)> {
    let game = crates().join("frontend/examples/benchmarks-game");
    let kernels = crates().join("../eval/workloads");
    let examples = crates().join("frontend/examples");
    let mut programs: Vec<(PathBuf, Input)> = [
        ("binary-trees", Input::Argument("10")),
        ("fannkuch-redux", Input::Argument("7")),
        ("fasta", Input::Argument("1000")),
        ("k-nucleotide", Input::Fasta),
        ("mandelbrot", Input::Argument("16")),
        ("md5", Input::Bytes(1000)),
        ("n-body", Input::Argument("50")),
        ("pidigits", Input::Argument("27")),
        ("spectral-norm", Input::Argument("6")),
    ]
    .into_iter()
    .map(|(name, input)| (game.join(name).join("main.fn"), input))
    .collect();
    programs.extend(
        [
            ("checksum", Input::Bytes(1024)),
            ("collatz", Input::Argument("100")),
            ("crc32", Input::Bytes(16)),
            ("inflate", Input::Argument("200")),
            ("queens", Input::Argument("6")),
            ("sieve", Input::Argument("1000")),
            ("sort", Input::Argument("24")),
        ]
        .into_iter()
        .map(|(name, input)| (kernels.join(name).join("main.fn"), input)),
    );
    let mut probes: Vec<_> = std::fs::read_dir(crates().join("../probes"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("sizes").exists())
        .collect();
    probes.sort();
    for probe in probes {
        for file in ["main.fn", "twin.fn"] {
            programs.push((probe.join(file), Input::Argument("8")));
        }
    }
    programs.push((examples.join("newton.fn"), Input::Nothing));
    programs.push((
        examples.join("nbody-untyped/main.fn"),
        Input::Argument("50"),
    ));
    programs
}

#[derive(Clone, Copy, Debug)]
enum Backend {
    Stock,
    Lab,
    Wasm,
}

/// The image `source` makes favouring speed, as `faun build` makes it, or
/// with every float operation walked.
fn image(source: &Path, backend: Backend, walked: bool) -> Vec<u8> {
    let target: &dyn Target = match backend {
        Backend::Stock | Backend::Lab => &X86_64Linux,
        Backend::Wasm => &Wasm32Wasi,
    };
    let mut program = faun_frontend::lower_to_barb(source, &faun_driver::platform(target))
        .unwrap_or_else(|error| panic!("{}: {}", source.display(), error.message));
    if walked {
        program.walk_floats();
    }
    barb::optimize(&mut program);
    let built = match backend {
        Backend::Lab => faun_x86_lab::compile(&program, Favour::Speed, SymbolTable::Omitted),
        Backend::Stock | Backend::Wasm => {
            faun_core::lower_to_machine_ir(&program, &target.routines()).and_then(|ir| {
                target.compile_machine_ir_with(&ir, Favour::Speed, SymbolTable::Omitted)
            })
        }
    };
    built.unwrap_or_else(|error| panic!("{} on {backend:?}: {error}", source.display()))
}

/// What an image writes and the status it leaves with, run on `input`.
fn run(image: &[u8], backend: Backend, input: Input, path: &Path) -> (i32, Vec<u8>) {
    // An image is written and started one at a time: a child another
    // thread starts while this one's image is open to write would hold it
    // open, and the image would be busy when it is run.
    static ONE_AT_A_TIME: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let starting = ONE_AT_A_TIME.lock().unwrap();
    std::fs::write(path, image).unwrap();
    let mut command = match backend {
        Backend::Stock | Backend::Lab => {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
            Command::new(path)
        }
        Backend::Wasm => {
            let mut wasmtime = Command::new("wasmtime");
            wasmtime.arg(path);
            wasmtime
        }
    };
    if let Input::Argument(argument) = input {
        command.arg(argument);
    }
    let stdin = given(input);
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    drop(starting);
    let mut pipe = child.stdin.take().unwrap();
    let feeding = std::thread::spawn(move || {
        use std::io::Write as _;
        // A program may stop reading before the end.
        let _ = pipe.write_all(&stdin);
    });
    let output = child.wait_with_output().unwrap();
    feeding.join().unwrap();
    (output.status.code().unwrap_or(-1), output.stdout)
}

/// What a program reads on standard input.
fn given(input: Input) -> Vec<u8> {
    match input {
        Input::Argument(_) | Input::Nothing => Vec::new(),
        Input::Fasta => {
            std::fs::read(crates().join("frontend/examples/benchmarks-game/fasta/1000.out"))
                .unwrap()
        }
        // A fixed walk of bytes, every value among them.
        Input::Bytes(count) => (0..count)
            .map(|at| u8::try_from((at * 167 + 13) % 256).unwrap())
            .collect(),
    }
}

fn check(backend: Backend) {
    let scratch = std::env::temp_dir().join(format!(
        "faun-walked-floats-{backend:?}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&scratch).unwrap();
    let programs = programs();
    let failures: Vec<String> = std::thread::scope(|scope| {
        #[expect(
            clippy::needless_collect,
            reason = "every program is started before any is waited for"
        )]
        let running: Vec<_> = programs
            .iter()
            .enumerate()
            .map(|(at, (source, input))| {
                let scratch = &scratch;
                scope.spawn(move || checked(source, *input, backend, &scratch.join(at.to_string())))
            })
            .collect();
        running
            .into_iter()
            .filter_map(|handle| handle.join().unwrap())
            .collect()
    });
    std::fs::remove_dir_all(&scratch).unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// What is wrong with `source` built for `backend` with its float routines
/// walked, its images written beside `scratch`; nothing where it writes what
/// it writes recognized.
fn checked(source: &Path, input: Input, backend: Backend, scratch: &Path) -> Option<String> {
    let recognized = image(source, backend, false);
    let walked = image(source, backend, true);
    if recognized == walked {
        // On x86-64 a program computing with floats must differ, or
        // nothing was recognized to walk.
        return (!matches!(backend, Backend::Wasm)
            && source.to_string_lossy().contains("mandelbrot"))
        .then(|| format!("{}: no float operation recognized", source.display()));
    }
    let expected = run(
        &recognized,
        backend,
        input,
        &scratch.with_extension("recognized"),
    );
    let said = run(&walked, backend, input, &scratch.with_extension("walked"));
    (expected.0 != 0 || said != expected).then(|| {
        format!(
            "{}: recognized left {} writing {} bytes, walked left {} writing {} bytes{}",
            source.display(),
            expected.0,
            expected.1.len(),
            said.0,
            said.1.len(),
            if said.1 == expected.1 {
                ""
            } else {
                ", and they differ"
            },
        )
    })
}

#[test]
fn walked_floats_write_what_recognized_floats_write_on_x86_64() {
    check(Backend::Stock);
}

#[test]
fn walked_floats_write_what_recognized_floats_write_on_the_x86_lab_backend() {
    check(Backend::Lab);
}

/// On wasm32 every float operation runs its body anyway; recognizing one
/// only lets the compiler fold it with the host's arithmetic.
#[test]
fn walked_floats_write_what_recognized_floats_write_on_wasm32() {
    check(Backend::Wasm);
}
