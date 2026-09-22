//! A dyld-loaded Mach-O with no imported symbols or linked libraries.
//!
//! Apple Silicon requires every executable page to be signed. The final
//! `__LINKEDIT` payload is therefore a minimal ad-hoc SHA-256 code directory,
//! not a library dependency or a developer identity.

use faun::ir::{Origin, Program};
use faun::targets::bytes::{Bytes, len32};
use sha2::{Digest, Sha256};

use crate::Code;
use crate::encode::adr;

const BASE: u64 = 0x1_0000_0000;
const PAGE: usize = 0x4000;
const HASH_PAGE: usize = 0x1000;

const HEADER_SIZE: usize = 32;
const COMMANDS_SIZE: usize = 536;
pub(crate) const CODE_OFFSET: usize = HEADER_SIZE + COMMANDS_SIZE;

const IDENTIFIER: &[u8] = b"faun-aarch64-macos\0";
const CODE_DIRECTORY_FIXED: usize = 48;
const SUPERBLOB_HEADER: usize = 20;

pub(crate) fn check_size(code: &Code, program: &Program) -> Result<(), String> {
    let occupied = CODE_OFFSET + code.words.len() * 4 + program.data().len();
    if occupied > PAGE {
        return Err(format!(
            "aarch64-macos baseline text and data use {occupied} bytes; at most {PAGE} are supported"
        ));
    }
    Ok(())
}

pub(crate) fn image(code: &Code, program: &Program) -> Vec<u8> {
    check_size(code, program).expect("target limits check the image size");

    let code_bytes = code.words.len() * 4;
    let signature_size = signature_size();
    let mut out = Bytes::default();
    load_commands(&mut out, code_bytes, program.data().len(), signature_size);

    let mut words = code.words.clone();
    for reloc in &code.relocs {
        let instruction = CODE_OFFSET + reloc.instruction * 4;
        let span = program.datum(reloc.data);
        assert_eq!(span.origin, Origin::Data, "target limits reject globals");
        let target = CODE_OFFSET + code_bytes + usize::try_from(span.start).unwrap();
        words[reloc.instruction] = adr(
            reloc.register,
            i64::try_from(target).unwrap() - i64::try_from(instruction).unwrap(),
        );
    }
    for word in words {
        out.le32(word);
    }
    out.bytes(program.data());
    let mut text = out.finish();
    text.resize(PAGE, 0);
    let signature = signature(&text);
    debug_assert_eq!(signature.len(), signature_size);
    text.extend(signature);
    text
}

fn load_commands(out: &mut Bytes, code_size: usize, data_size: usize, signature_size: usize) {
    header(out);
    segment(out, "__PAGEZERO", 0, BASE, 0, 0, 0, 0, 0);
    segment(
        out,
        "__TEXT",
        BASE,
        u64::try_from(PAGE).unwrap(),
        0,
        u64::try_from(PAGE).unwrap(),
        5,
        5,
        2,
    );
    section(out, "__text", CODE_OFFSET, code_size, 2, 0x8000_0400);
    section(out, "__const", CODE_OFFSET + code_size, data_size, 0, 0);
    segment(
        out,
        "__LINKEDIT",
        BASE + u64::try_from(PAGE).unwrap(),
        u64::try_from(PAGE).unwrap(),
        u64::try_from(PAGE).unwrap(),
        u64::try_from(signature_size).unwrap(),
        1,
        1,
        0,
    );
    dyld_info(out);
    dylinker(out);
    build_version(out);
    source_version(out);
    main_command(out);
    code_signature_command(out, signature_size);
}

fn header(out: &mut Bytes) {
    out.le32(0xFEED_FACF); // MH_MAGIC_64
    out.le32(0x0100_000C); // CPU_TYPE_ARM64
    out.le32(0); // CPU_SUBTYPE_ARM64_ALL
    out.le32(2); // MH_EXECUTE
    out.le32(9); // ncmds
    out.le32(u32::try_from(COMMANDS_SIZE).unwrap());
    out.le32(0x0020_0085); // NOUNDEFS | DYLDLINK | TWOLEVEL | PIE
    out.le32(0);
}

#[expect(
    clippy::too_many_arguments,
    reason = "the fields are the segment command"
)]
fn segment(
    out: &mut Bytes,
    name: &str,
    vmaddr: u64,
    vmsize: u64,
    fileoff: u64,
    filesize: u64,
    maxprot: u32,
    initprot: u32,
    sections: u32,
) {
    out.le32(0x19); // LC_SEGMENT_64
    out.le32(72 + 80 * sections);
    fixed_name(out, name);
    out.le64(vmaddr);
    out.le64(vmsize);
    out.le64(fileoff);
    out.le64(filesize);
    out.le32(maxprot);
    out.le32(initprot);
    out.le32(sections);
    out.le32(0);
}

fn section(out: &mut Bytes, name: &str, address: usize, size: usize, alignment: u32, flags: u32) {
    fixed_name(out, name);
    fixed_name(out, "__TEXT");
    out.le64(BASE + u64::try_from(address).unwrap());
    out.le64(u64::try_from(size).unwrap());
    out.le32(u32::try_from(address).unwrap());
    out.le32(alignment);
    out.le32(0); // reloff
    out.le32(0); // nreloc
    out.le32(flags);
    out.le32(0);
    out.le32(0);
    out.le32(0);
}

fn dyld_info(out: &mut Bytes) {
    out.le32(0x8000_0022); // LC_DYLD_INFO_ONLY
    out.le32(48);
    out.bytes(&[0; 40]); // no rebases, binds, lazy binds, or exports
}

fn dylinker(out: &mut Bytes) {
    out.le32(0xE); // LC_LOAD_DYLINKER
    out.le32(32);
    out.le32(12);
    out.bytes(b"/usr/lib/dyld\0");
    out.bytes(&[0; 6]);
}

fn build_version(out: &mut Bytes) {
    out.le32(0x32); // LC_BUILD_VERSION
    out.le32(24);
    out.le32(1); // PLATFORM_MACOS
    out.le32(0x000B_0000); // macOS 11.0, the first Apple Silicon release
    out.le32(0x000B_0000);
    out.le32(0); // no tool records
}

fn source_version(out: &mut Bytes) {
    out.le32(0x2A); // LC_SOURCE_VERSION
    out.le32(16);
    out.le64(0);
}

fn main_command(out: &mut Bytes) {
    out.le32(0x8000_0028); // LC_MAIN
    out.le32(24);
    out.le64(u64::try_from(CODE_OFFSET).unwrap());
    out.le64(0); // default stack
}

fn code_signature_command(out: &mut Bytes, size: usize) {
    out.le32(0x1D); // LC_CODE_SIGNATURE
    out.le32(16);
    out.le32(u32::try_from(PAGE).unwrap());
    out.le32(len32(size));
}

fn fixed_name(out: &mut Bytes, name: &str) {
    assert!(name.len() <= 16);
    out.bytes(name.as_bytes());
    out.bytes(&[0; 16][..16 - name.len()]);
}

const fn signature_size() -> usize {
    SUPERBLOB_HEADER + CODE_DIRECTORY_FIXED + IDENTIFIER.len() + PAGE / HASH_PAGE * 32
}

fn signature(text: &[u8]) -> Vec<u8> {
    let slots = PAGE / HASH_PAGE;
    let directory_size = CODE_DIRECTORY_FIXED + IDENTIFIER.len() + slots * 32;
    let hash_offset = CODE_DIRECTORY_FIXED + IDENTIFIER.len();
    let mut out = Vec::with_capacity(SUPERBLOB_HEADER + directory_size);
    let be32 = |out: &mut Vec<u8>, value: usize| {
        out.extend_from_slice(&u32::try_from(value).unwrap().to_be_bytes());
    };

    out.extend_from_slice(&0xFADE_0CC0u32.to_be_bytes()); // embedded signature
    be32(&mut out, SUPERBLOB_HEADER + directory_size);
    be32(&mut out, 1); // one blob
    be32(&mut out, 0); // CSSLOT_CODEDIRECTORY
    be32(&mut out, SUPERBLOB_HEADER);

    out.extend_from_slice(&0xFADE_0C02u32.to_be_bytes()); // code directory
    be32(&mut out, directory_size);
    out.extend_from_slice(&0x0002_0100u32.to_be_bytes());
    out.extend_from_slice(&2u32.to_be_bytes()); // CS_ADHOC
    be32(&mut out, hash_offset);
    be32(&mut out, CODE_DIRECTORY_FIXED);
    be32(&mut out, 0); // special slots
    be32(&mut out, slots);
    be32(&mut out, PAGE); // signed bytes end at __LINKEDIT
    out.extend_from_slice(&[32, 2, 0, 12]); // SHA-256, 4 KiB hash pages
    be32(&mut out, 0); // spare2
    be32(&mut out, 0); // scatter offset
    out.extend_from_slice(IDENTIFIER);
    for page in text.chunks_exact(HASH_PAGE) {
        out.extend_from_slice(&Sha256::digest(page));
    }
    out
}

#[cfg(test)]
mod tests {
    use faun::programs;
    use faun::targets::Target;

    use super::{PAGE, signature_size};
    use crate::Aarch64Macos;

    #[test]
    fn image_is_a_signed_arm64_macho_with_a_dyld_entry() {
        let image = Aarch64Macos
            .compile(&programs::hello_world())
            .unwrap()
            .remove(0)
            .bytes;
        assert_eq!(&image[..4], &0xFEED_FACFu32.to_le_bytes());
        assert_eq!(&image[4..8], &0x0100_000Cu32.to_le_bytes());
        assert_eq!(&image[16..20], &9u32.to_le_bytes());
        assert_eq!(&image[PAGE..PAGE + 4], &0xFADE_0CC0u32.to_be_bytes());
        assert_eq!(image.len(), PAGE + signature_size());
    }
}
