use faun_core::ir::{DataId, Exit, Op, Origin, Program, Terminator, ValueId};

use crate::Code;
use crate::encode::{Encoder, Reg};

const SYS_EXIT: u64 = 1;
const SYS_WRITE: u64 = 4;
const STDOUT: u64 = 1;

#[derive(Clone, Copy)]
enum Source {
    Constant(u64),
    Address(DataId),
    Argc,
}

fn entry_host(program: &Program) -> Option<ValueId> {
    let entry = program.entry();
    (program.parameter_names(entry).next() == Some("host")).then(|| {
        let body = program
            .function(entry)
            .body()
            .expect("the entry has a body");
        program.values(program.region(body).params)[0]
    })
}

pub(crate) fn lower(program: &Program) -> Code {
    let mut lowering = Lowering {
        program,
        sources: vec![None; program.values_count()],
        encoder: Encoder::default(),
    };

    if program.reaches("argc!") || entry_host(program).is_some() {
        // dyld's LC_MAIN convention supplies argc in x0. Keep it away from
        // syscall arguments for the rest of the process.
        lowering.encoder.mov_reg(Reg::X19, Reg::X0);
    }

    let body = program
        .function(program.entry())
        .body()
        .expect("validation requires an entry body");
    if let Some(host) = entry_host(program) {
        lowering.sources[host.index()] = Some(Source::Argc);
    }
    for (op, results) in program.walk(body) {
        lowering.instruction(op, results);
    }
    if let Some(terminator) = program.region(body).terminator {
        lowering.terminator(terminator);
    }

    let (words, relocs) = lowering.encoder.finish();
    Code { words, relocs }
}

struct Lowering<'a> {
    program: &'a Program,
    sources: Vec<Option<Source>>,
    encoder: Encoder,
}

impl Lowering<'_> {
    fn instruction(&mut self, op: &Op, results: &[ValueId]) {
        match *op {
            Op::Constant { value } => {
                self.sources[results[0].index()] = Some(Source::Constant(value));
            }
            Op::AddressOf(data) => {
                self.sources[results[0].index()] = Some(Source::Address(data));
            }
            Op::Call { function, args } => {
                let function = self.program.function(function);
                let name = self
                    .program
                    .name(function.external().expect("limits reject internal calls"));
                let args = self.program.values(args);
                match name {
                    "argc!" => {
                        self.sources[results[0].index()] = Some(Source::Argc);
                    }
                    "write" => {
                        self.encoder.mov_imm(Reg::X0, STDOUT);
                        self.read(Reg::X1, args[0]);
                        self.read(Reg::X2, args[1]);
                        self.encoder.syscall(SYS_WRITE);
                    }
                    "exit!" => {
                        self.read(Reg::X0, args[0]);
                        self.encoder.syscall(SYS_EXIT);
                    }
                    _ => unreachable!("target acceptance checks provider names"),
                }
            }
            _ => unreachable!("target limits reject unsupported operations"),
        }
    }

    fn terminator(&mut self, terminator: Terminator) {
        debug_assert_eq!(terminator.exit, Exit::Return);
        let values = self.program.values(terminator.values);
        if let Some(&status) = values.first() {
            self.read(Reg::X0, status);
        } else {
            self.encoder.mov_imm(Reg::X0, 0);
        }
        self.encoder.syscall(SYS_EXIT);
    }

    fn read(&mut self, register: Reg, value: ValueId) {
        match self.sources[value.index()].expect("limits require a supported value source") {
            Source::Constant(value) => self.encoder.mov_imm(register, value),
            Source::Address(data) => self.encoder.address(register, data),
            Source::Argc => self.encoder.mov_reg(register, Reg::X19),
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one exhaustive acceptance boundary for this deliberately small baseline"
)]
pub(crate) fn check(program: &Program) -> Result<(), String> {
    if !program.globals().is_empty() {
        return Err("aarch64-macos baseline emission does not yet map writable globals".to_owned());
    }

    let entry = program.entry();
    for (at, name) in program.parameter_names(entry).enumerate() {
        if at != 0 || name != "host" {
            return Err(format!(
                "aarch64-macos cannot supply entry parameter {at} `{name}`"
            ));
        }
    }
    for (index, function) in program.functions().iter().enumerate() {
        let Some(body) = function.body() else {
            continue;
        };
        if index != entry.index() {
            let name = program.name(function.name);
            return Err(format!(
                "aarch64-macos baseline emission does not yet support internal function `{name}`"
            ));
        }

        let mut sources = vec![false; program.values_count()];
        if let Some(host) = entry_host(program) {
            sources[host.index()] = true;
        }
        for (op, results) in program.walk(body) {
            match *op {
                Op::Constant { .. } => sources[results[0].index()] = true,
                Op::AddressOf(data) => {
                    if program.datum(data).origin != Origin::Data {
                        return Err(
                            "aarch64-macos baseline emission only addresses read-only data"
                                .to_owned(),
                        );
                    }
                    sources[results[0].index()] = true;
                }
                Op::Call {
                    function: called,
                    args,
                } => {
                    let called = program.function(called);
                    let Some(symbol) = called.external() else {
                        return Err(
                            "aarch64-macos baseline emission does not yet support internal calls"
                                .to_owned(),
                        );
                    };
                    if program
                        .values(args)
                        .iter()
                        .any(|value| !sources[value.index()])
                    {
                        return Err(
                            "aarch64-macos baseline calls require constants, data addresses, or argc"
                                .to_owned(),
                        );
                    }
                    match program.name(symbol) {
                        "argc!" => sources[results[0].index()] = true,
                        "write" | "exit!" => {}
                        name => {
                            return Err(format!(
                                "aarch64-macos baseline emission does not implement `{name}`"
                            ));
                        }
                    }
                }
                _ => {
                    return Err(format!(
                        "aarch64-macos baseline emission does not yet support `{op:?}`"
                    ));
                }
            }
        }

        if let Some(terminator) = program.region(body).terminator {
            if terminator.exit != Exit::Return {
                return Err(
                    "aarch64-macos baseline emission only supports entry returns".to_owned(),
                );
            }
            if program
                .values(terminator.values)
                .iter()
                .any(|value| !sources[value.index()])
            {
                return Err(
                    "aarch64-macos baseline return requires a constant, data address, or argc"
                        .to_owned(),
                );
            }
        }
    }
    Ok(())
}
