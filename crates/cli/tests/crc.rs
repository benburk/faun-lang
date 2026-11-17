//! The crc library's example, built for this machine, on inputs too long
//! for its expectations: CRC-32 eight bytes a step and Adler-32 reduced
//! every few megabytes agree with checksums worked out here, a byte at a
//! time, at lengths that leave every tail.

#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn crc32(bytes: &[u8]) -> u32 {
    let mut register = !0u32;
    for &byte in bytes {
        register ^= u32::from(byte);
        for _ in 0..8 {
            register = if register & 1 == 1 {
                0xedb8_8320 ^ (register >> 1)
            } else {
                register >> 1
            };
        }
    }
    !register
}

fn adler32(bytes: &[u8]) -> u32 {
    let (mut low, mut high) = (1u32, 0u32);
    for &byte in bytes {
        low = (low + u32::from(byte)) % 65521;
        high = (high + low) % 65521;
    }
    high << 16 | low
}

/// Bytes from a fixed xorshift, so the input is the same every run.
fn noise(len: usize) -> Vec<u8> {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state.to_le_bytes()[3]
        })
        .collect()
}

/// The example built into `dir`.
fn build(dir: &Path) -> PathBuf {
    std::fs::create_dir_all(dir).unwrap();
    let image = dir.join("basic");
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../frontend/examples/libraries/crc/examples/basic.fn");
    let status = Command::new(env!("CARGO_BIN_EXE_faun"))
        .arg("build")
        .arg(format!("--output={}", image.display()))
        .arg(source)
        .status()
        .unwrap();
    assert!(status.success(), "the crc example builds");
    image
}

/// What the example prints for `input`.
fn printed(image: &Path, input: &[u8]) -> String {
    let mut child = Command::new(image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let written = input.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&written).unwrap());
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn long_inputs_agree_with_checksums_worked_out_here() {
    let dir = std::env::temp_dir().join(format!("faun-crc-{}", std::process::id()));
    let image = build(&dir);
    // 0xff is the largest each sum can grow by, and 17 MB passes four
    // reductions of Adler-32; the lengths leave each tail of eight.
    let inputs = [
        vec![0xff; 17_000_003],
        noise(9_000_005),
        noise(7),
        Vec::new(),
    ];
    for input in inputs {
        let expected = format!(
            "crc32 {:08x}\nadler32 {:08x}\n",
            crc32(&input),
            adler32(&input)
        );
        assert_eq!(printed(&image, &input), expected, "{} bytes", input.len());
    }
    let _ = std::fs::remove_dir_all(&dir);
}
