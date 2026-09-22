use faun::ir::DataId;

const SVC_0X80: u32 = 0xD400_1001;

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Reg {
    X0 = 0,
    X1 = 1,
    X2 = 2,
    X16 = 16,
    X19 = 19,
}

impl From<Reg> for u8 {
    #[expect(clippy::as_conversions, reason = "reading a repr(u8) discriminant")]
    fn from(reg: Reg) -> Self {
        reg as Self
    }
}

pub(crate) struct Reloc {
    pub(crate) instruction: usize,
    pub(crate) register: Reg,
    pub(crate) data: DataId,
}

#[derive(Default)]
pub(crate) struct Encoder {
    words: Vec<u32>,
    relocs: Vec<Reloc>,
}

impl Encoder {
    pub(crate) fn mov_reg(&mut self, dst: Reg, src: Reg) {
        let dst = u32::from(u8::from(dst));
        let src = u32::from(u8::from(src));
        self.words.push(0xAA00_03E0 | src << 16 | dst);
    }

    /// Materialize all 64 bits without a literal pool or relocation.
    pub(crate) fn mov_imm(&mut self, dst: Reg, value: u64) {
        let dst = u32::from(u8::from(dst));
        let mut chunks = (0..4).filter_map(|shift| {
            let immediate = u16::try_from((value >> (shift * 16)) & 0xFFFF).unwrap();
            (immediate != 0).then_some((shift, immediate))
        });
        let Some((shift, immediate)) = chunks.next() else {
            self.words.push(0xD280_0000 | dst);
            return;
        };
        self.words.push(
            0xD280_0000 | u32::from(immediate) << 5 | u32::try_from(shift).unwrap() << 21 | dst,
        );
        for (shift, immediate) in chunks {
            self.words.push(
                0xF280_0000 | u32::from(immediate) << 5 | u32::try_from(shift).unwrap() << 21 | dst,
            );
        }
    }

    pub(crate) fn address(&mut self, dst: Reg, data: DataId) {
        let instruction = self.words.len();
        self.words.push(0);
        self.relocs.push(Reloc {
            instruction,
            register: dst,
            data,
        });
    }

    pub(crate) fn syscall(&mut self, number: u64) {
        self.mov_imm(Reg::X16, number);
        self.words.push(SVC_0X80);
    }

    pub(crate) fn finish(self) -> (Vec<u32>, Vec<Reloc>) {
        (self.words, self.relocs)
    }
}

pub(crate) fn adr(register: Reg, displacement: i64) -> u32 {
    assert!(
        (-(1 << 20)..1 << 20).contains(&displacement),
        "data must be within ADR's one MiB reach"
    );
    let immediate = displacement.rem_euclid(1 << 21);
    let immediate = u32::try_from(immediate).unwrap();
    0x1000_0000
        | (immediate & 0b11) << 29
        | ((immediate >> 2) & 0x7_FFFF) << 5
        | u32::from(u8::from(register))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constants_use_movz_then_only_the_needed_movks() {
        let mut encoder = Encoder::default();
        encoder.mov_imm(Reg::X0, 0);
        encoder.mov_imm(Reg::X1, 0x1234_0000_0000_5678);
        let (words, _) = encoder.finish();
        assert_eq!(words, [0xD280_0000, 0xD28A_CF01, 0xF2E2_4681]);
    }

    #[test]
    fn adr_splits_its_signed_immediate() {
        assert_eq!(adr(Reg::X1, 12), 0x1000_0061);
        assert_eq!(adr(Reg::X1, -4), 0x10FF_FFE1);
    }
}
