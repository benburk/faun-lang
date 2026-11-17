//! The png library's example, built for this machine and run on `PngSuite`:
//! every image decodes to the pixels pypng gives, by the CRC-32 the
//! fixtures' `expected.txt` holds, and every file `PngSuite` marks corrupt,
//! or a valid one cut short or with a bit flipped, is refused, never a
//! crash.

#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn library() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../frontend/examples/libraries/png")
}

/// The example built once into a directory of its own, removed when
/// dropped.
struct ToPam(PathBuf);

impl ToPam {
    fn build() -> Self {
        let dir = std::env::temp_dir().join(format!("faun-png-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let image = dir.join("topam");
        let status = Command::new(env!("CARGO_BIN_EXE_faun"))
            .arg("build")
            .arg(format!("--output={}", image.display()))
            .arg(library().join("examples/topam.fn"))
            .status()
            .unwrap();
        assert!(status.success(), "the png example builds");
        Self(dir)
    }

    /// The status the example exits with on `input`, and the pixels it
    /// wrote after the PAM header.
    fn decode(&self, input: &[u8]) -> (i32, Vec<u8>) {
        let mut child = Command::new(self.0.join("topam"))
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
        let end = b"ENDHDR\n";
        let pixels = output
            .stdout
            .windows(end.len())
            .position(|window| window == end)
            .map_or_else(Vec::new, |at| output.stdout[at + end.len()..].to_vec());
        (status, pixels)
    }
}

impl Drop for ToPam {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// What a file should decode to: its pixels' count and CRC-32, or nothing
/// where it should be refused.
type Expected = Option<(usize, u32)>;

fn suite() -> Vec<(PathBuf, Expected)> {
    let dir = library().join("fixtures");
    std::fs::read_to_string(dir.join("expected.txt"))
        .unwrap()
        .lines()
        .map(|line| {
            let fields: Vec<_> = line.split(' ').collect();
            let path = dir.join("pngsuite").join(fields[0]);
            let expected = match fields[1..] {
                ["error"] => None,
                [width, height, crc] => {
                    let width: usize = width.parse().unwrap();
                    let height: usize = height.parse().unwrap();
                    Some((width * height * 4, u32::from_str_radix(crc, 16).unwrap()))
                }
                _ => panic!("{line}"),
            };
            (path, expected)
        })
        .collect()
}

/// CRC-32 as zlib computes it, a bit at a time: slow, and plainly right.
fn crc32(bytes: &[u8]) -> u32 {
    let mut register = u32::MAX;
    for &byte in bytes {
        register ^= u32::from(byte);
        for _ in 0..8 {
            let low = register & 1;
            register = (register >> 1) ^ (0xedb8_8320 * low);
        }
    }
    !register
}

fn name(path: &Path) -> &str {
    path.file_name().unwrap().to_str().unwrap()
}

#[test]
fn crc32_is_zlibs() {
    assert_eq!(crc32(b"123456789"), 0xcbf4_3926);
}

#[test]
fn every_image_decodes_to_the_reference_and_every_corrupt_one_is_refused() {
    let decoder = ToPam::build();
    let all = suite();
    assert!(all.len() >= 170, "{} images", all.len());
    for (path, expected) in all {
        let (status, pixels) = decoder.decode(&std::fs::read(&path).unwrap());
        match expected {
            Some((len, crc)) => {
                assert_eq!(status, 0, "{}", name(&path));
                assert_eq!(pixels.len(), len, "{}", name(&path));
                assert_eq!(
                    crc32(&pixels),
                    crc,
                    "{} decodes to pypng's pixels",
                    name(&path)
                );
            }
            None => assert_eq!(status, 1, "{} is refused", name(&path)),
        }
    }
}

/// Every file cut short is refused, since a cut loses IEND. A bit flipped
/// anywhere is refused too: in the signature it is no PNG, and anywhere
/// after, every chunk's length, type, data and CRC-32 are checked by that
/// CRC-32, ancillary chunks' as well.
#[test]
fn a_file_cut_short_or_flipped_is_refused() {
    let decoder = ToPam::build();
    let mut seed: u64 = 2003;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for (path, expected) in suite().into_iter().step_by(5) {
        if expected.is_none() {
            continue;
        }
        let file = std::fs::read(&path).unwrap();
        let len = file.len();
        for cut in (0..len).step_by((len / 8).max(1)).chain(len - 3..len) {
            let (status, _) = decoder.decode(&file[..cut]);
            assert_eq!(status, 1, "{} cut to {cut} of {len}", name(&path));
        }
        for _ in 0..4 {
            let mut flipped = file.clone();
            let at = usize::try_from(next()).unwrap() % len;
            flipped[at] ^= 1 << (next() % 8);
            let (status, _) = decoder.decode(&flipped);
            assert_eq!(status, 1, "{} flipped at {at}", name(&path));
        }
    }
}
