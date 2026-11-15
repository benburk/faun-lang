//! Straight-line startup, writes, and exit through the Darwin syscall ABI.
use faun_core::ir::{DataId, Exit, Op, Origin, Program, ValueId};

use crate::Code;
use crate::encode::{Encoder, Reg};

#[derive(Clone, Copy)]
enum Source {
    Constant(u64),
    Address(DataId),
    Argv,
    Argc(u16),
}

impl Source {
    fn narrowed(self, bits: u16) -> Result<Self, String> {
        match self {
            Self::Constant(value) => Ok(Self::Constant(value & mask(bits))),
            Self::Argc(old) => Ok(Self::Argc(old.min(bits))),
            Self::Address(_) | Self::Argv if bits == 64 => Ok(self),
            Self::Address(_) | Self::Argv => {
                Err("aarch64-macos cannot narrow a data address".into())
            }
        }
    }
}

const fn mask(bits: u16) -> u64 {
    if bits == 0 {
        0
    } else {
        u64::MAX >> (64 - bits)
    }
}

pub(crate) fn lower(p: &Program) -> Result<Code, String> {
    if !p.globals().is_empty() {
        return Err("aarch64-macos baseline emission does not yet map writable globals".into());
    }
    let entry = p.entry();
    let body = p.function(entry).body().expect("validated entry");
    let mut state = Lowering {
        program: p,
        sources: vec![None; p.values_count()],
        encoder: Encoder::default(),
    };
    for (i, name) in p.parameter_names(entry).enumerate() {
        let (saved, incoming, source) = match (i, name) {
            (0, "argc") => (Reg::X19, Reg::X0, Source::Argc(64)),
            (1, "argv") => (Reg::X20, Reg::X1, Source::Argv),
            _ => {
                return Err(format!(
                    "aarch64-macos cannot supply entry parameter {i} `{name}`"
                ));
            }
        };
        state.encoder.mov_reg(saved, incoming);
        state.sources[p.values(p.region(body).params)[i].index()] = Some(source);
    }
    for (op, results) in p.walk(body) {
        state.instruction(op, results)?;
    }
    if let Some(term) = p.region(body).terminator {
        if term.exit != Exit::Return {
            return Err("aarch64-macos baseline emission only supports entry returns".into());
        }
        if let Some(&status) = p.values(term.values).first() {
            state.read(Reg::X0, status)?;
        } else {
            state.encoder.mov_imm(Reg::X0, 0);
        }
        state.encoder.syscall(1);
    }
    let (words, relocs) = state.encoder.finish();
    Ok(Code { words, relocs })
}

struct Lowering<'a> {
    program: &'a Program,
    sources: Vec<Option<Source>>,
    encoder: Encoder,
}

impl Lowering<'_> {
    fn source(&self, value: ValueId) -> Result<Source, String> {
        self.sources[value.index()].ok_or_else(|| {
            "aarch64-macos baseline requires a constant, data address or argument count".into()
        })
    }

    fn instruction(&mut self, op: &Op, results: &[ValueId]) -> Result<(), String> {
        let source = match *op {
            Op::Constant { value } => Source::Constant(value),
            Op::AddressOf(data) if self.program.datum(data).origin == Origin::Data => {
                Source::Address(data)
            }
            Op::Convert { value } => self
                .source(value)?
                .narrowed(self.program.class(results[0]).bits(64))?,
            Op::Call { function, args } => {
                let f = self.program.function(function);
                let name = self.program.name(f.name);
                let Some(symbol) = f.external() else {
                    return Err(format!(
                        "aarch64-macos baseline emission does not yet support internal call `{name}`"
                    ));
                };
                let name = self.program.name(symbol);
                return self.call(name, self.program.values(args));
            }
            _ => {
                return Err(format!(
                    "aarch64-macos baseline emission does not yet support `{op:?}`"
                ));
            }
        };
        self.sources[results[0].index()] = Some(source);
        Ok(())
    }

    fn call(&mut self, name: &str, args: &[ValueId]) -> Result<(), String> {
        match (name, args) {
            ("write!", &[address, len]) => {
                self.encoder.mov_imm(Reg::X0, 1);
                self.write(address, len)?;
            }
            ("write_fd!", &[fd, address, len]) => {
                self.read(Reg::X0, fd)?;
                self.write(address, len)?;
            }
            ("exit!", &[status]) => {
                self.read(Reg::X0, status)?;
                self.encoder.syscall(1);
            }
            _ => return Err(format!("aarch64-macos baseline cannot emit `{name}`")),
        }
        Ok(())
    }

    fn write(&mut self, address: ValueId, len: ValueId) -> Result<(), String> {
        self.read(Reg::X1, address)?;
        self.read(Reg::X2, len)?;
        self.encoder.syscall(4);
        Ok(())
    }

    fn read(&mut self, reg: Reg, value: ValueId) -> Result<(), String> {
        match self.source(value)? {
            Source::Constant(n) => self.encoder.mov_imm(reg, n),
            Source::Argv => self.encoder.mov_reg(reg, Reg::X20),
            Source::Address(data) => self.encoder.address(reg, data),
            Source::Argc(0) => self.encoder.mov_imm(reg, 0),
            Source::Argc(64) => self.encoder.mov_reg(reg, Reg::X19),
            Source::Argc(bits) => self.encoder.low_bits(reg, Reg::X19, bits),
        }
        Ok(())
    }
}
