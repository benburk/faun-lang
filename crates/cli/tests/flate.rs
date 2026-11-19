//! The flate library's gzip example, built for this machine and run on the
//! fixtures Python's zlib wrote: every stream gives back its input byte for
//! byte, and a stream cut short or corrupted is refused, never a crash.

#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

fn library() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../frontend/examples/libraries/flate")
}

/// The gzip example built once into a directory of its own, removed when
/// dropped.
struct Gzip(PathBuf);

impl Gzip {
    fn build() -> Self {
        // Numbered, since `cargo test` runs this file's tests side by side
        // in one process, and each builds into, and then removes, its own.
        static MADE: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "faun-flate-{}-{}",
            std::process::id(),
            MADE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let image = dir.join("gzip");
        let status = Command::new(env!("CARGO_BIN_EXE_faun"))
            .arg("build")
            .arg(format!("--output={}", image.display()))
            .arg(library().join("examples/gzip.fn"))
            .status()
            .unwrap();
        assert!(status.success(), "the gzip example builds");
        Self(dir)
    }

    /// The status `gzip -d` exits with on `input`, read as `format`, and
    /// what it wrote to standard output.
    fn decompress(&self, format: Option<&str>, input: &[u8]) -> (i32, Vec<u8>) {
        let mut child = Command::new(self.0.join("gzip"))
            .arg("-d")
            .args(format)
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
        let status = output.status.code().unwrap_or_else(|| {
            panic!("ended by a signal: {:?}", output.status);
        });
        (status, output.stdout)
    }
}

impl Drop for Gzip {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The fixtures, each with the format flag it is read with and the input
/// it was made from.
fn fixtures() -> Vec<(PathBuf, Option<&'static str>, Vec<u8>)> {
    let dir = library().join("fixtures");
    let mut found: Vec<_> = std::fs::read_dir(dir.join("deflate"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    found.sort();
    found
        .into_iter()
        .map(|path| {
            let name = path.file_name().unwrap().to_str().unwrap();
            let format = match path.extension().unwrap().to_str().unwrap() {
                "gz" => None,
                "zlib" => Some("--zlib"),
                _ => Some("--raw"),
            };
            let input = name.split('.').next().unwrap();
            let expected = std::fs::read(dir.join("input").join(input)).unwrap();
            (path, format, expected)
        })
        .collect()
}

fn name(path: &Path) -> &str {
    path.file_name().unwrap().to_str().unwrap()
}

#[test]
fn every_fixture_inflates_to_its_input() {
    let gzip = Gzip::build();
    let all = fixtures();
    assert!(all.len() >= 70, "{} fixtures", all.len());
    for (path, format, expected) in all {
        let (status, written) = gzip.decompress(format, &std::fs::read(&path).unwrap());
        assert_eq!(status, 0, "{}", name(&path));
        assert!(written == expected, "{} inflates to its input", name(&path));
    }
}

/// Every stream cut short, at points through it and at each of its last
/// bytes, is refused with status one.
#[test]
fn a_stream_cut_short_is_refused() {
    let gzip = Gzip::build();
    for (path, format, _) in fixtures() {
        let stream = std::fs::read(&path).unwrap();
        let len = stream.len();
        let step = (len / 12).max(1);
        let cuts = (0..len).step_by(step).chain(len.saturating_sub(4)..len);
        for cut in cuts {
            let (status, _) = gzip.decompress(format, &stream[..cut]);
            assert_eq!(status, 1, "{} cut to {cut} of {len}", name(&path));
        }
    }
}

/// A bit flipped anywhere a container's checksum covers is refused, or
/// read as the same input, as a match a byte further back can be in a run
/// of one byte; one flipped in raw DEFLATE, or bytes that were never a
/// stream, end with an answer or a refusal, never a crash.
#[test]
fn a_corrupted_stream_is_refused_or_read_never_a_crash() {
    let gzip = Gzip::build();
    let mut seed: u64 = 1952;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for (path, format, expected) in fixtures() {
        let stream = std::fs::read(&path).unwrap();
        if stream.len() < 24 {
            continue;
        }
        for _ in 0..6 {
            let mut flipped = stream.clone();
            // gzip's time, flags for the compressor and system are read by
            // nobody; zlib's header is checked, and its data by Adler-32.
            let from = if format.is_none() { 10 } else { 0 };
            let at = from + usize::try_from(next()).unwrap() % (stream.len() - from);
            flipped[at] ^= 1 << (next() % 8);
            let (status, written) = gzip.decompress(format, &flipped);
            let read_alike = status == 0 && written == expected;
            if format == Some("--raw") {
                assert!(status <= 1, "{} flipped at {at}: {status}", name(&path));
            } else {
                assert!(status == 1 || read_alike, "{} flipped at {at}", name(&path));
            }
        }
    }
    for size in [1, 2, 3, 7, 64, 1000, 20000] {
        let noise: Vec<u8> = (0..size).map(|_| next().to_le_bytes()[0]).collect();
        for format in [None, Some("--zlib"), Some("--raw")] {
            let (status, _) = gzip.decompress(format, &noise);
            assert!(status <= 1, "{size} random bytes as {format:?}: {status}");
        }
    }
}
