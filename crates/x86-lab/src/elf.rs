//! ELF header, program headers, then the segments they describe. In a
//! program with naturals the data and the globals each start on a word,
//! where an object in them has an even address, as a natural's must;
//! nothing else is padded.
//!
//! Omitted, none of it consulted to execute a file:
//!
//! - Notes, page alignment, dynamic linking.
//! - Section headers and a symbol table, unless [`SymbolTable::Written`] asks
//!   for them, as `faun build --symbols` does: then a `.symtab` names each
//!   function, so `perf` and `objdump -d` can say where they are, after
//!   everything that is loaded. Without them `nm` finds nothing, and the
//!   file is as small as it was.
//!
//! Position independence, at two bytes:
//!
//! - `lea rsi, [rip+d]` is 7 bytes against `mov esi, imm32`'s 5. `REX.W` is
//!   required; without it the address truncates to 32 bits.
//! - An absolute immediate needs a fixed load address, which puts the
//!   container format inside the instruction selector.
//! - Every address is a displacement within one mapping, so `ET_DYN` needs
//!   no `PT_DYNAMIC`, no relocation processing, and no interpreter.
//!
//! Size:
//!
//! - 120 of 158 bytes are header.
//! - Under about 140 needs code inside `e_shoff`, `e_flags`, or the
//!   `e_ident` padding. Rejected: unreadable, and the specification does not
//!   promise those fields stay unread.
//!
//! Segments come from a list. Two more are possible:
//!
//! - Read-only for the data, 56 bytes, no padding: two segments share a file
//!   page when `p_vaddr` matches `p_offset` modulo the page size.
//! - Writable, only for storage outliving every call. A heap comes from
//!   `mmap` and the stack from the kernel, so neither needs a segment.

use super::Code;
use crate::ir::{Origin, Program};
use faun_core::targets::SymbolTable;
use faun_core::targets::bytes::{Bytes, len32};

pub(crate) const EHDR_LEN: u16 = 64;
pub(crate) const PHDR_LEN: u16 = 56;
const SHDR_LEN: u16 = 64;
const SYM_LEN: u64 = 24;
const PAGE_SIZE: u64 = 0x1000;
const PAGE: usize = 0x1000;
/// What the data and the globals each start on, where naturals are held.
const ALIGN: usize = 8;

/// `p_flags`.
const READ: u32 = 4;
const WRITE: u32 = 2;
const EXECUTE: u32 = 1;

/// One mapping the kernel makes.
struct Segment {
    flags: u32,
    start: u32,
    len: u32,
    /// Where it is mapped, which for everything but the writable region is
    /// its own file offset.
    vaddr: u32,
}

pub(crate) fn image(code: &Code, program: &Program, symbols: SymbolTable) -> Vec<u8> {
    let layout = Layout::new(code, program);
    let end = layout.globals + program.globals().len();
    let sections = match symbols {
        SymbolTable::Omitted => None,
        SymbolTable::Written => Some(Sections::new(code, program, (layout.text, end))),
    };
    let mut out = Bytes::default();

    header(&mut out, &layout, sections.as_ref());
    for segment in &layout.segments {
        program_header(&mut out, segment);
    }
    out.bytes(&relocated(code, &layout, program));
    out.bytes(&vec![0; layout.data - layout.text - code.bytes.len()]);
    out.bytes(program.data());
    out.bytes(&vec![
        0;
        layout.globals - layout.data - program.data().len()
    ]);
    out.bytes(program.globals());
    if let Some(sections) = &sections {
        sections.write(&mut out, code.bytes.len());
    }

    out.finish()
}

/// What follows the loaded segments where functions are named: a symbol for
/// each, their names, the section names, and the headers of the four
/// sections, each table on a word.
struct Sections {
    /// Each function's name and where its code starts and ends in the text,
    /// in order.
    functions: Vec<(String, usize, usize)>,
    /// File offsets of the text, of the end of what is loaded, and of the
    /// symbol table, its names, the section names and the section headers.
    text: usize,
    end: usize,
    symtab: usize,
    strtab: usize,
    shstrtab: usize,
    headers: usize,
    names: Vec<u8>,
}

/// The section names, each after a nought, and where each starts in them:
/// the text, the symbols, their names, and these names.
const SECTION_NAMES: &[u8] = b"\0.text\0.symtab\0.strtab\0.shstrtab\0";
const TEXT_NAME: u32 = 1;
const SYMTAB_NAME: u32 = 7;
const STRTAB_NAME: u32 = 15;
const SHSTRTAB_NAME: u32 = 23;

impl Sections {
    fn new(code: &Code, program: &Program, (text, end): (usize, usize)) -> Self {
        // Code before the first function sets the program up; it is named
        // for where it starts the program.
        let mut starts: Vec<(String, usize)> = Vec::with_capacity(code.functions.len() + 1);
        if code.functions.first().is_none_or(|&(_, at)| at > 0) {
            starts.push(("_start".to_owned(), 0));
        }
        starts.extend(
            code.functions.iter().map(|&(function, at)| {
                (program.name(program.function(function).name).to_owned(), at)
            }),
        );
        let functions: Vec<_> = starts
            .iter()
            .enumerate()
            .map(|(at, (name, start))| {
                let next = starts
                    .get(at + 1)
                    .map_or(code.bytes.len(), |&(_, next)| next);
                (name.clone(), *start, next)
            })
            .collect();
        let mut names = vec![0];
        for (name, _, _) in &functions {
            names.extend_from_slice(name.as_bytes());
            names.push(0);
        }
        let symtab = end.next_multiple_of(ALIGN);
        let count = u64::try_from(functions.len() + 1).expect("a count of functions");
        let symtab_len = usize::try_from(count * SYM_LEN).expect("a symbol table in memory");
        let strtab = symtab + symtab_len;
        let shstrtab = strtab + names.len();
        let headers = (shstrtab + SECTION_NAMES.len()).next_multiple_of(ALIGN);
        Self {
            functions,
            text,
            end,
            symtab,
            strtab,
            shstrtab,
            headers,
            names,
        }
    }

    /// Where the section headers start, how many there are, and which holds
    /// the section names.
    fn header_fields(&self) -> (u64, u16, u16) {
        (as64(self.headers), 5, 4)
    }

    /// Everything after what is loaded: the tables, then the headers.
    fn write(&self, out: &mut Bytes, text_len: usize) {
        out.bytes(&vec![0; self.symtab - self.end]);
        // The first symbol is nothing; each function's is local, as nothing
        // links against the file.
        out.bytes(&[0; 24]);
        let mut name = 1;
        for (function, from, to) in &self.functions {
            out.le32(name);
            out.byte(2); // st_info: STB_LOCAL, STT_FUNC
            out.byte(0); // st_other
            out.le16(1); // st_shndx: .text
            out.le64(as64(self.text + from)); // st_value
            out.le64(as64(to - from)); // st_size
            name += len32(function.len()) + 1;
        }
        out.bytes(&self.names);
        out.bytes(SECTION_NAMES);
        out.bytes(&vec![0; self.headers - self.shstrtab - SECTION_NAMES.len()]);

        let count = as64(self.functions.len() + 1);
        out.bytes(&[0; 64]);
        section(out, (TEXT_NAME, 1, 6), (self.text, text_len), (0, 0, 1, 0));
        section(
            out,
            (SYMTAB_NAME, 2, 0),
            (self.symtab, self.strtab - self.symtab),
            (3, count, 8, SYM_LEN),
        );
        section(
            out,
            (STRTAB_NAME, 3, 0),
            (self.strtab, self.names.len()),
            (0, 0, 1, 0),
        );
        section(
            out,
            (SHSTRTAB_NAME, 3, 0),
            (self.shstrtab, SECTION_NAMES.len()),
            (0, 0, 1, 0),
        );
    }
}

/// One section header: its name, type and flags; where it lies; and its
/// link, info, alignment and entry size. Only `.text` is loaded, at the
/// address its offset is.
fn section(
    out: &mut Bytes,
    (name, kind, flags): (u32, u32, u64),
    (offset, len): (usize, usize),
    (link, info, align, entry): (u32, u64, u64, u64),
) {
    out.le32(name);
    out.le32(kind);
    out.le64(flags);
    out.le64(if flags == 0 { 0 } else { as64(offset) }); // sh_addr
    out.le64(as64(offset));
    out.le64(as64(len));
    out.le32(link);
    out.le32(u32::try_from(info).expect("a count of symbols"));
    out.le64(align);
    out.le64(entry);
}

fn as64(value: usize) -> u64 {
    u64::try_from(value).expect("an offset in the file")
}

struct Layout {
    /// File offset of the code, and of the data that follows it.
    text: usize,
    data: usize,
    /// File offset of the globals.
    globals: usize,
    /// Where the globals are *mapped*, which is not where they sit in the
    /// file: they need a page of their own to be writable in.
    globals_at: usize,
    segments: Vec<Segment>,
}

impl Layout {
    fn new(code: &Code, program: &Program) -> Self {
        // What is only read shares one mapping with the code and the headers.
        // What is written needs its own, and only exists when something is.
        let writable = !program.globals().is_empty();
        let count = 1 + usize::from(writable);
        let text = usize::from(EHDR_LEN) + usize::from(PHDR_LEN) * count;
        // Only a region holding a natural's object is placed anywhere in
        // particular.
        let aligned = |at: usize, len: usize| {
            if len == 0 || !program.has_runtime_naturals() {
                at
            } else {
                at.next_multiple_of(ALIGN)
            }
        };
        let data = aligned(text + code.bytes.len(), program.data().len());
        let globals = aligned(data + program.data().len(), program.globals().len());

        // A page further on. The two mappings then land on different pages
        // of memory while sharing one page of the file, which the kernel
        // allows so long as an address matches its offset modulo a page.
        let globals_at = globals + PAGE;

        let mut segments = vec![Segment {
            flags: READ | EXECUTE,
            start: 0,
            len: len32(globals),
            vaddr: 0,
        }];
        if writable {
            segments.push(Segment {
                flags: READ | WRITE,
                start: len32(globals),
                len: len32(program.globals().len()),
                vaddr: len32(globals_at),
            });
        }
        debug_assert_eq!(segments.len(), count);

        Self {
            text,
            data,
            globals,
            globals_at,
            segments,
        }
    }
}

/// Each address as a displacement from the end of its own instruction, which
/// is why nothing here needs a load address.
fn relocated(code: &Code, layout: &Layout, program: &Program) -> Vec<u8> {
    let mut text = code.bytes.clone();
    for reloc in &code.relocs {
        let from = layout.text + reloc.offset + 4;
        let span = program.datum(reloc.data);
        let start = usize::try_from(span.start).expect("an offset in the image");
        // Addresses, not file offsets: the two happen to agree everywhere
        // but in the writable mapping, which sits a page further along.
        let to = match span.origin {
            Origin::Data => layout.data + start,
            Origin::Globals => layout.globals_at + start,
        };
        let displacement = to.abs_diff(from);
        let displacement = i32::try_from(displacement).expect("data within 2 GiB of the code");
        let displacement = if to < from {
            -displacement
        } else {
            displacement
        };
        text[reloc.offset..reloc.offset + 4].copy_from_slice(&displacement.to_le_bytes());
    }
    text
}

fn header(out: &mut Bytes, layout: &Layout, sections: Option<&Sections>) {
    let (shoff, shnum, shstrndx) = sections.map_or((0, 0, 0), Sections::header_fields);
    out.bytes(b"\x7FELF"); // e_ident: magic
    out.byte(2); //             ELFCLASS64
    out.byte(1); //             ELFDATA2LSB
    out.byte(1); //             EV_CURRENT
    out.byte(0); //             ELFOSABI_SYSV
    out.byte(0); //             ABI version
    out.bytes(&[0; 7]); //      padding
    out.le16(3); // e_type: ET_DYN
    out.le16(0x3E); // e_machine: EM_X86_64
    out.le32(1); // e_version
    out.le64(u64::from(len32(layout.text))); // e_entry, before the load bias
    out.le64(u64::from(EHDR_LEN)); // e_phoff
    out.le64(shoff); // e_shoff
    out.le32(0); // e_flags
    out.le16(EHDR_LEN); // e_ehsize
    out.le16(PHDR_LEN); // e_phentsize
    out.le16(len16(layout.segments.len())); // e_phnum
    out.le16(if shnum == 0 { 0 } else { SHDR_LEN }); // e_shentsize
    out.le16(shnum); // e_shnum
    out.le16(shstrndx); // e_shstrndx
}

/// A segment's address has to match its file offset modulo the page size,
/// which laying them out in order gives.
fn program_header(out: &mut Bytes, segment: &Segment) {
    out.le32(1); // p_type: PT_LOAD
    out.le32(segment.flags);
    out.le64(u64::from(segment.start)); // p_offset
    out.le64(u64::from(segment.vaddr)); // p_vaddr
    out.le64(u64::from(segment.vaddr)); // p_paddr
    out.le64(u64::from(segment.len)); // p_filesz
    out.le64(u64::from(segment.len)); // p_memsz
    out.le64(PAGE_SIZE); // p_align
}

fn len16(count: usize) -> u16 {
    u16::try_from(count).expect("a handful of segments")
}

#[cfg(test)]
mod tests {
    use crate::targets::Target;

    use super::*;

    fn hello() -> Vec<u8> {
        crate::X86_64Linux.emit(&crate::programs::hello_world())
    }

    #[test]
    fn the_header_describes_a_loadable_executable() {
        let image = hello();

        assert_eq!(&image[..4], b"\x7FELF");
        assert_eq!(&image[16..18], &3u16.to_le_bytes()); // ET_DYN
        assert_eq!(&image[18..20], &0x3Eu16.to_le_bytes()); // EM_X86_64
        assert_eq!(&image[54..56], &56u16.to_le_bytes()); // e_phentsize
        assert_eq!(&image[56..58], &1u16.to_le_bytes()); // e_phnum

        // The segment covers the file exactly, so no byte is wasted.
        let filesz = u64::from_le_bytes(image[96..104].try_into().unwrap());
        assert_eq!(usize::try_from(filesz).unwrap(), image.len());
    }

    /// Symbols, asked for, follow everything that is loaded: the segment
    /// and what it holds are as they were, and the header points at five
    /// sections naming the program's functions. (A program that calls
    /// functions also chains their frames, which this one does not.)
    #[test]
    fn symbols_follow_what_is_loaded() {
        let plain = hello();
        let named = crate::X86_64Linux.emit_with(
            &crate::programs::hello_world(),
            faun_core::targets::Favour::Speed,
            SymbolTable::Written,
        );

        assert!(named.len() > plain.len());
        assert_eq!(&named[96..104], &plain[96..104], "the segment is unchanged");
        let text = usize::from(EHDR_LEN + PHDR_LEN);
        assert_eq!(&named[text..plain.len()], &plain[text..]);
        let shoff = u64::from_le_bytes(named[40..48].try_into().unwrap());
        assert!(usize::try_from(shoff).unwrap() >= plain.len());
        assert_eq!(&named[58..64], &[64, 0, 5, 0, 4, 0]); // shentsize, shnum, shstrndx
        let tables = &named[plain.len()..];
        assert!(tables.windows(6).any(|name| name == b".text\0"));
    }

    /// Nothing in the file names an address, which is what lets the kernel
    /// put it wherever it likes.
    #[test]
    fn the_message_is_reached_from_the_instruction_pointer() {
        let image = hello();
        let text = usize::from(EHDR_LEN + PHDR_LEN);
        assert_eq!(
            u64::from_le_bytes(image[24..32].try_into().unwrap()),
            u64::from(EHDR_LEN + PHDR_LEN),
            "the entry point is an offset, not an address"
        );

        // Find `lea rsi, [rip+disp]`; the displacement follows its three-byte
        // opcode and is counted from the end of the instruction.
        let lea = image[text..]
            .windows(3)
            .position(|bytes| bytes == [0x48, 0x8D, 0x35])
            .expect("the message address load");
        let at = text + lea + 3;
        let displacement = i32::from_le_bytes(image[at..at + 4].try_into().unwrap());
        let target = (at + 4).wrapping_add_signed(isize::try_from(displacement).unwrap());
        assert_eq!(&image[target..], b"Hello, World!\n");
    }
}
