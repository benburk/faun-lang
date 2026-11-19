//! The png library's encoder, built for this machine as its two examples
//! and run on `PngSuite`: every image the decoder reads, encoded at several
//! levels and both ways of filtering, reads back to the same pixels
//! through the library's own decoder and through a reader written apart
//! from it, in Python on its standard zlib.

#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

fn library() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../frontend/examples/libraries/png")
}

/// Both examples built once into a directory of its own, removed when
/// dropped.
struct Examples(PathBuf);

impl Examples {
    fn build() -> Self {
        // Numbered, since `cargo test` runs this file's tests side by side
        // in one process, and each builds into, and then removes, its own.
        static MADE: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "faun-png-encode-{}-{}",
            std::process::id(),
            MADE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        for name in ["topam", "topng"] {
            let status = Command::new(env!("CARGO_BIN_EXE_faun"))
                .arg("build")
                .arg(format!("--output={}", dir.join(name).display()))
                .arg(library().join(format!("examples/{name}.fn")))
                .status()
                .unwrap();
            assert!(status.success(), "the {name} example builds");
        }
        Self(dir)
    }

    /// The status `name` exits with on `input`, and what it wrote.
    fn run(&self, name: &str, args: &[&str], input: &[u8]) -> (i32, Vec<u8>) {
        let output = pipe(Command::new(self.0.join(name)).args(args), input);
        let status = output.status.code().unwrap_or_else(|| {
            panic!("{name} ended by a signal: {:?}", output.status);
        });
        (status, output.stdout)
    }
}

impl Drop for Examples {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// What `command` writes with `input` on its standard input.
fn pipe(command: &mut Command, input: &[u8]) -> std::process::Output {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || {
        // A program that refuses early may close its input first.
        let _ = stdin.write_all(&input);
    });
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap();
    output
}

/// A PNG reader for what the encoder writes, 8-bit samples without
/// interlacing, on Python's own zlib: each file named on the command line
/// read, every chunk's CRC-32 checked, and its pixels written as red,
/// green, blue and alpha, one file's after another's.
const PYTHON_READ: &str = r"import struct, sys, zlib
for path in sys.argv[1:]:
    data = open(path, 'rb').read()
    assert data[:8] == b'\x89PNG\r\n\x1a\n', path
    at, idat, header = 8, b'', None
    while True:
        length, kind = struct.unpack('>I4s', data[at:at + 8])
        body = data[at + 8:at + 8 + length]
        crc, = struct.unpack('>I', data[at + 8 + length:at + 12 + length])
        assert zlib.crc32(kind + body) == crc, path
        at += 12 + length
        if kind == b'IHDR': header = struct.unpack('>IIBBBBB', body)
        elif kind == b'IDAT': idat += body
        elif kind == b'IEND': break
    width, height, depth, colour, _, _, interlace = header
    assert depth == 8 and interlace == 0, path
    per = {0: 1, 2: 3, 4: 2, 6: 4}[colour]
    stride = width * per
    raw = zlib.decompress(idat)
    assert len(raw) == height * (stride + 1), path
    prev, out = bytearray(stride), bytearray()
    for y in range(height):
        kind, row = raw[y * (stride + 1)], bytearray(raw[y * (stride + 1) + 1:(y + 1) * (stride + 1)])
        for i in range(stride):
            a = row[i - per] if i >= per else 0
            b = prev[i]
            c = prev[i - per] if i >= per else 0
            if kind == 1: row[i] = (row[i] + a) & 255
            elif kind == 2: row[i] = (row[i] + b) & 255
            elif kind == 3: row[i] = (row[i] + (a + b) // 2) & 255
            elif kind == 4:
                p = a + b - c
                pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
                row[i] = (row[i] + (a if pa <= pb and pa <= pc else b if pb <= pc else c)) & 255
            else: assert kind == 0, path
        for x in range(width):
            s = row[x * per:(x + 1) * per]
            out += {1: lambda: bytes([s[0]] * 3 + [255]), 2: lambda: bytes([s[0]] * 3 + [s[1]]),
                    3: lambda: bytes(s) + b'\xff', 4: lambda: bytes(s)}[per]()
        prev = row
    sys.stdout.buffer.write(out)";

fn name(path: &Path) -> &str {
    path.file_name().unwrap().to_str().unwrap()
}

/// Every image `PngSuite` holds that is not corrupt.
fn suite() -> Vec<PathBuf> {
    let mut paths: Vec<_> = std::fs::read_dir(library().join("fixtures/pngsuite"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|e| e == "png") && !name(path).starts_with('x'))
        .collect();
    paths.sort();
    paths
}

/// The pixels after a PAM file's header.
fn pixels(pam: &[u8]) -> &[u8] {
    let end = b"ENDHDR\n";
    let at = pam.windows(end.len()).position(|w| w == end).unwrap();
    &pam[at + end.len()..]
}

#[test]
fn every_image_encoded_reads_back_through_both_readers() {
    let examples = Examples::build();
    let written = examples.0.join("written");
    std::fs::create_dir_all(&written).unwrap();
    let mut files = Vec::new();
    let mut expected = Vec::new();
    for path in suite() {
        let (status, pam) = examples.run("topam", &[], &std::fs::read(&path).unwrap());
        assert_eq!(status, 0, "{} decodes", name(&path));
        for flags in [&[][..], &["-0"], &["-1", "--unfiltered"], &["-9"]] {
            let (status, png) = examples.run("topng", flags, &pam);
            assert_eq!(status, 0, "{} {flags:?} encodes", name(&path));
            let (status, back) = examples.run("topam", &[], &png);
            assert_eq!(status, 0, "{} {flags:?} reads back", name(&path));
            assert_eq!(back, pam, "{} {flags:?} reads back the same", name(&path));
            let file = written.join(format!("{}{}", files.len(), name(&path)));
            std::fs::write(&file, &png).unwrap();
            files.push(file);
            expected.extend_from_slice(pixels(&pam));
        }
    }
    let output = Command::new("python3")
        .args(["-I", "-c", PYTHON_READ])
        .args(&files)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout == expected, "Python reads the same pixels");
}

#[test]
fn a_file_not_understood_is_refused() {
    let examples = Examples::build();
    for input in [
        &b""[..],
        b"P6\n1 1\n255\n\0\0\0",
        b"P7\nWIDTH 2\nHEIGHT 1\nDEPTH 4\nMAXVAL 255\nENDHDR\n\0\0\0\0",
        b"P7\nWIDTH 1\nHEIGHT 1\nDEPTH 4\nMAXVAL 65535\nENDHDR\n\0\0\0\0\0\0\0\0",
    ] {
        assert_eq!(examples.run("topng", &[], input).0, 1, "{input:?}");
    }
    assert_eq!(examples.run("topng", &["-x"], b"").0, 2);
}
