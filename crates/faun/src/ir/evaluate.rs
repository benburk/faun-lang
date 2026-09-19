//! A deterministic, target-independent machine-IR reference interpreter.
//!
//! `Natural` uses arbitrary precision. `Fixed` arithmetic must fit its declared
//! result (a violated proof is an error); `Word` arithmetic uses target-width
//! unsigned machine arithmetic. Only constants and explicit conversions truncate
//! fixed values. Memory is byte-addressed, unaligned access is allowed, address
//! zero is invalid, and Data is read-only. These addresses are interpreter-local.
//!
//! Fuel charges one unit per instruction and region terminator, including calls
//! and loop iterations. Explicit stacks avoid native-stack overflow. The natural
//! size limit is a resource guard, not a language modulus. Host callbacks must
//! themselves terminate; their internal work cannot be metered by this evaluator.

use super::{
    Binary, Class, Exit, FunctionId, Offset, Op, Origin, Program, Range, RegionId, Relation,
    ValueId, Width,
};
use num_bigint::BigUint;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endian {
    Little,
    Big,
}

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub word_bits: u16,
    pub endian: Endian,
    pub fuel: u64,
    pub max_natural_bits: u64,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            word_bits: 64,
            endian: Endian::Little,
            fuel: 100_000,
            max_natural_bits: 1_048_576,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidConfig,
    InvalidProgram(&'static str),
    FuelExhausted,
    SizeLimit,
    DoesNotFit(Class),
    InvalidMemory,
    ReadOnlyMemory,
    Unreachable,
    Host(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Debug, PartialEq, Eq)]
pub struct Evaluation {
    pub values: Vec<BigUint>,
    pub globals: Vec<u8>,
    pub fuel_remaining: u64,
    pub halted: bool,
}

#[derive(Debug)]
pub enum HostResult {
    Return(Vec<BigUint>),
    Halt(Vec<BigUint>),
}

pub trait Host {
    /// # Errors
    /// A host may reject an unsupported operation or invalid arguments/memory.
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, Error>;
}

#[derive(Debug)]
pub struct RejectHost;
impl Host for RejectHost {
    fn call(&mut self, name: &str, _: &[BigUint], _: &mut Memory<'_>) -> Result<HostResult, Error> {
        Err(Error::Host(format!(
            "unsupported platform routine `{name}`"
        )))
    }
}

/// Data starts at 1; Globals starts one byte beyond the end of Data. Neither
/// pool may be accessed through the gap, nor may an access cross a pool boundary.
#[derive(Debug)]
pub struct Memory<'a> {
    data: &'a [u8],
    globals: Vec<u8>,
    globals_base: u64,
}
impl Memory<'_> {
    fn locate(&self, address: u64, len: usize) -> Result<(Origin, std::ops::Range<usize>), Error> {
        let (origin, base, size) = if address >= self.globals_base {
            (Origin::Globals, self.globals_base, self.globals.len())
        } else {
            (Origin::Data, 1, self.data.len())
        };
        let start = address
            .checked_sub(base)
            .and_then(|n| usize::try_from(n).ok())
            .ok_or(Error::InvalidMemory)?;
        let end = start
            .checked_add(len)
            .filter(|&end| end <= size)
            .ok_or(Error::InvalidMemory)?;
        Ok((origin, start..end))
    }

    /// # Errors
    /// Rejects addresses outside the two pools or accesses crossing their ends.
    pub fn read(&self, address: u64, len: usize) -> Result<&[u8], Error> {
        let (origin, range) = self.locate(address, len)?;
        Ok(match origin {
            Origin::Data => &self.data[range],
            Origin::Globals => &self.globals[range],
        })
    }

    /// # Errors
    /// Rejects out-of-bounds accesses and writes to read-only Data.
    pub fn write(&mut self, address: u64, bytes: &[u8]) -> Result<(), Error> {
        let (origin, range) = self.locate(address, bytes.len())?;
        if origin == Origin::Data {
            return Err(Error::ReadOnlyMemory);
        }
        self.globals[range].copy_from_slice(bytes);
        Ok(())
    }
}

// A continuation stack is shared by all calls; each call owns a separate value
// frame so recursion cannot overwrite the caller's SSA definitions.
enum Task {
    Region {
        id: RegionId,
        at: usize,
    },
    If {
        results: Range,
    },
    Loop {
        body: RegionId,
        results: Range,
    },
    Call {
        results: Option<Range>,
        returns: Range,
    },
}

struct Machine<'a, H> {
    program: &'a Program,
    config: Config,
    host: &'a mut H,
    memory: Memory<'a>,
    frames: Vec<Vec<Option<BigUint>>>,
    tasks: Vec<Task>,
}

/// Evaluate any function, with fresh Globals for each invocation.
///
/// # Errors
/// Rejects malformed executed IR, invalid widths, memory accesses, violated
/// fixed-width fits, unsupported host operations, and resource exhaustion.
/// This is not a replacement for static validation of unexecuted paths.
pub fn evaluate(
    program: &Program,
    function: FunctionId,
    args: &[BigUint],
    config: Config,
    host: &mut impl Host,
) -> Result<Evaluation, Error> {
    if !matches!(config.word_bits, 16 | 32 | 64) || config.max_natural_bits == 0 {
        return Err(Error::InvalidConfig);
    }
    let globals_base = u64::try_from(program.data.len())
        .ok()
        .and_then(|n| n.checked_add(2))
        .ok_or(Error::InvalidMemory)?;
    let end = globals_base
        .checked_add(u64::try_from(program.globals.len()).map_err(|_| Error::InvalidMemory)?)
        .ok_or(Error::InvalidMemory)?;
    if config.word_bits < 64 && end > (1u64 << config.word_bits) {
        return Err(Error::InvalidMemory);
    }
    let mut machine = Machine {
        program,
        config,
        host,
        memory: Memory {
            data: &program.data,
            globals: program.globals.clone(),
            globals_base,
        },
        frames: Vec::new(),
        tasks: Vec::new(),
    };
    machine.call(function, args, None)?;
    machine.run()
}

const fn invalid(what: &'static str) -> Error {
    Error::InvalidProgram(what)
}

impl<H: Host> Machine<'_, H> {
    fn ids(&self, range: Range) -> Result<&[ValueId], Error> {
        self.program
            .operands
            .get(range.range())
            .ok_or_else(|| invalid("operand range"))
    }

    fn class(&self, id: ValueId) -> Result<Class, Error> {
        self.program
            .classes
            .get(id.index())
            .copied()
            .ok_or_else(|| invalid("value id"))
    }

    const fn width(&self, class: Class) -> Result<Option<u16>, Error> {
        match class {
            Class::Natural => Ok(None),
            Class::Word | Class::Address => Ok(Some(self.config.word_bits)),
            Class::Fixed { bits } if bits > 0 && bits <= self.config.word_bits => Ok(Some(bits)),
            Class::Fixed { .. } => Err(Error::DoesNotFit(class)),
        }
    }

    fn fit(&self, class: Class, value: &BigUint) -> Result<(), Error> {
        match self.width(class)? {
            Some(bits) if value.bits() > u64::from(bits) => Err(Error::DoesNotFit(class)),
            None if value.bits() > self.config.max_natural_bits => Err(Error::SizeLimit),
            _ => Ok(()),
        }
    }

    fn convert(&self, class: Class, value: BigUint) -> Result<BigUint, Error> {
        let value = if let Some(bits) = self.width(class)? {
            value % (BigUint::from(1u8) << usize::from(bits))
        } else {
            value
        };
        self.fit(class, &value)?;
        Ok(value)
    }

    fn value(&self, id: ValueId) -> Result<BigUint, Error> {
        self.frames
            .last()
            .and_then(|f| f.get(id.index()))
            .and_then(Option::as_ref)
            .cloned()
            .ok_or_else(|| invalid("undefined value"))
    }

    fn values(&self, range: Range) -> Result<Vec<BigUint>, Error> {
        self.ids(range)?.iter().map(|&id| self.value(id)).collect()
    }

    fn bind(&mut self, range: Range, values: &[BigUint]) -> Result<(), Error> {
        let ids = self.ids(range)?.to_vec();
        if ids.len() != values.len() {
            return Err(invalid("result arity"));
        }
        for (&id, value) in ids.iter().zip(values) {
            self.fit(self.class(id)?, value)?;
        }
        let frame = self
            .frames
            .last_mut()
            .ok_or_else(|| invalid("missing frame"))?;
        for (id, value) in ids.into_iter().zip(values) {
            *frame
                .get_mut(id.index())
                .ok_or_else(|| invalid("value id"))? = Some(value.clone());
        }
        Ok(())
    }

    fn signature(&self, range: Range, values: &[BigUint]) -> Result<(), Error> {
        let classes = self
            .program
            .signature
            .get(range.range())
            .ok_or_else(|| invalid("signature range"))?;
        if classes.len() != values.len() {
            return Err(invalid("signature arity"));
        }
        for (&class, value) in classes.iter().zip(values) {
            self.fit(class, value)?;
        }
        Ok(())
    }

    fn region(&mut self, id: RegionId, args: &[BigUint]) -> Result<(), Error> {
        let region = self
            .program
            .regions
            .get(id.index())
            .ok_or_else(|| invalid("region id"))?;
        self.bind(region.params, args)?;
        self.tasks.push(Task::Region { id, at: 0 });
        Ok(())
    }

    fn call(
        &mut self,
        id: FunctionId,
        args: &[BigUint],
        results: Option<Range>,
    ) -> Result<(), Error> {
        let function = self
            .program
            .functions
            .get(id.index())
            .ok_or_else(|| invalid("function id"))?;
        self.frames.push(vec![None; self.program.classes.len()]);
        self.bind(function.params, args)?;
        self.tasks.push(Task::Call {
            results,
            returns: function.returns,
        });
        self.region(function.body, args)
    }

    fn finish(self, values: Vec<BigUint>, halted: bool) -> Evaluation {
        Evaluation {
            values,
            globals: self.memory.globals,
            fuel_remaining: self.config.fuel,
            halted,
        }
    }

    fn run(mut self) -> Result<Evaluation, Error> {
        loop {
            let Some(Task::Region { id, at }) = self.tasks.pop() else {
                return Err(invalid("missing region continuation"));
            };
            self.config.fuel = self
                .config
                .fuel
                .checked_sub(1)
                .ok_or(Error::FuelExhausted)?;
            let region = *self
                .program
                .regions
                .get(id.index())
                .ok_or_else(|| invalid("region id"))?;
            if at == region.ops.len() {
                let values = self.values(region.terminator.values)?;
                if let Some(values) = self.leave(region.terminator.exit, values)? {
                    return Ok(self.finish(values, false));
                }
                continue;
            }
            let index = region
                .ops
                .range()
                .start
                .checked_add(at)
                .ok_or_else(|| invalid("instruction range"))?;
            let (op, results) = self.instruction(index)?;
            self.tasks.push(Task::Region { id, at: at + 1 });
            if let Some(values) = self.step(op, results)? {
                return Ok(self.finish(values, true));
            }
        }
    }

    fn instruction(&self, index: usize) -> Result<(Op, Range), Error> {
        let op = self
            .program
            .ops
            .get(index)
            .ok_or_else(|| invalid("instruction range"))?;
        let results = self
            .program
            .results
            .get(index)
            .ok_or_else(|| invalid("results range"))?;
        Ok((*op, *results))
    }

    fn leave(&mut self, exit: Exit, values: Vec<BigUint>) -> Result<Option<Vec<BigUint>>, Error> {
        if exit == Exit::Unreachable {
            return Err(Error::Unreachable);
        }
        while let Some(task) = self.tasks.pop() {
            match (task, exit) {
                (Task::If { results }, Exit::Yield) | (Task::Loop { results, .. }, Exit::Break) => {
                    self.bind(results, &values)?;
                    return Ok(None);
                }
                (Task::Loop { body, results }, Exit::Continue) => {
                    self.tasks.push(Task::Loop { body, results });
                    self.region(body, &values)?;
                    return Ok(None);
                }
                (Task::Region { .. }, _)
                | (Task::If { .. }, Exit::Return | Exit::Break | Exit::Continue)
                | (Task::Loop { .. }, Exit::Return) => {}
                (Task::Call { results, returns }, Exit::Return) => {
                    self.signature(returns, &values)?;
                    self.frames.pop();
                    if let Some(results) = results {
                        self.bind(results, &values)?;
                        return Ok(None);
                    }
                    return Ok(Some(values));
                }
                _ => return Err(invalid("exit crosses the wrong construct")),
            }
        }
        Err(invalid("exit has no enclosing construct"))
    }

    fn address(&self, id: ValueId, offset: Offset) -> Result<u64, Error> {
        let value = self.value(id)?;
        self.fit(Class::Address, &value)?;
        let base = u64::try_from(value).map_err(|_| Error::InvalidMemory)?;
        let offset = match offset {
            Offset::Bytes(n) => i64::from(n),
            Offset::Words(n) => i64::from(n) * i64::from(self.config.word_bits / 8),
        };
        let address = base
            .checked_add_signed(offset)
            .ok_or(Error::InvalidMemory)?;
        if self.config.word_bits < 64 && address >= (1u64 << self.config.word_bits) {
            return Err(Error::InvalidMemory);
        }
        Ok(address)
    }

    fn result_class(&self, results: Range) -> Result<Class, Error> {
        let [id] = self.ids(results)? else {
            return Err(invalid("scalar result arity"));
        };
        self.class(*id)
    }

    fn binary(
        &self,
        op: Binary,
        class: Class,
        left: BigUint,
        right: BigUint,
    ) -> Result<BigUint, Error> {
        self.fit(class, &left)?;
        self.fit(class, &right)?;
        let value = match op {
            Binary::Add => left + right,
            Binary::Sub if left >= right => left - right,
            Binary::Sub if class == Class::Natural => BigUint::default(),
            Binary::Sub if class == Class::Word => {
                (BigUint::from(1u8) << usize::from(self.config.word_bits)) + left - right
            }
            Binary::Sub => return Err(Error::DoesNotFit(class)),
        };
        if class == Class::Word {
            self.convert(class, value)
        } else {
            self.fit(class, &value)?;
            Ok(value)
        }
    }

    // A non-local host halt is returned directly rather than disguised as a
    // function return, which would incorrectly execute caller continuations.
    fn step(&mut self, op: Op, results: Range) -> Result<Option<Vec<BigUint>>, Error> {
        match op {
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                let region = if self.value(condition)? == BigUint::default() {
                    else_region
                } else {
                    then_region
                };
                self.tasks.push(Task::If { results });
                self.region(region, &[])?;
            }
            Op::Loop { initial, body } => {
                let args = self.values(initial)?;
                self.tasks.push(Task::Loop { body, results });
                self.region(body, &args)?;
            }
            Op::Call { function, args } => {
                let args = self.values(args)?;
                self.call(function, &args, Some(results))?;
            }
            Op::PlatformCall { platform, args } => match self.platform(platform, args)? {
                HostResult::Halt(values) => return Ok(Some(values)),
                HostResult::Return(values) => self.bind(results, &values)?,
            },
            _ => {
                let values = self.scalar(op, results)?;
                self.bind(results, &values)?;
            }
        }
        Ok(None)
    }

    fn scalar(&mut self, op: Op, results: Range) -> Result<Vec<BigUint>, Error> {
        let value = match op {
            Op::Constant { class, value } => self.convert(class, BigUint::from(value))?,
            Op::NaturalConstant(id) => self.natural(id)?,
            Op::AddressOf(id) => BigUint::from(self.datum_address(id)?),
            Op::Binary { op, left, right } => self.binary(
                op,
                self.result_class(results)?,
                self.value(left)?,
                self.value(right)?,
            )?,
            Op::Compare {
                relation,
                left,
                right,
            } => {
                let (left, right) = (self.value(left)?, self.value(right)?);
                BigUint::from(u8::from(match relation {
                    Relation::Equal => left == right,
                    Relation::Less => left < right,
                }))
            }
            Op::Convert { class, value } => self.convert(class, self.value(value)?)?,
            Op::Load {
                width,
                address,
                offset,
            } => self.load(width, address, offset)?,
            Op::Store {
                width,
                address,
                offset,
                value,
            } => {
                self.store(width, address, offset, value)?;
                return Ok(Vec::new());
            }
            _ => return Err(invalid("expected scalar instruction")),
        };
        Ok(vec![value])
    }

    fn natural(&self, id: super::DataId) -> Result<BigUint, Error> {
        let span = self
            .program
            .spans
            .get(id.index())
            .ok_or_else(|| invalid("data id"))?;
        if span.origin != Origin::Data {
            return Err(invalid("natural constant outside Data"));
        }
        let address = self.datum_address(id)?;
        let len = usize::try_from(span.len).map_err(|_| Error::InvalidMemory)?;
        let value = BigUint::from_bytes_le(self.memory.read(address, len)?);
        self.fit(Class::Natural, &value)?;
        Ok(value)
    }

    fn datum_address(&self, id: super::DataId) -> Result<u64, Error> {
        let span = self
            .program
            .spans
            .get(id.index())
            .ok_or_else(|| invalid("data id"))?;
        let base = match span.origin {
            Origin::Data => 1,
            Origin::Globals => self.memory.globals_base,
        };
        let address = base
            .checked_add(u64::from(span.start))
            .ok_or(Error::InvalidMemory)?;
        let len = usize::try_from(span.len).map_err(|_| Error::InvalidMemory)?;
        let (origin, _) = self.memory.locate(address, len)?;
        if origin != span.origin {
            return Err(Error::InvalidMemory);
        }
        Ok(address)
    }

    fn load(&self, width: Width, address: ValueId, offset: Offset) -> Result<BigUint, Error> {
        let bytes = self
            .memory
            .read(self.address(address, offset)?, self.bytes(width))?;
        Ok(match self.config.endian {
            Endian::Little => BigUint::from_bytes_le(bytes),
            Endian::Big => BigUint::from_bytes_be(bytes),
        })
    }

    fn bytes(&self, width: Width) -> usize {
        match width {
            Width::Byte => 1,
            Width::Word => usize::from(self.config.word_bits / 8),
        }
    }

    fn store(
        &mut self,
        width: Width,
        address: ValueId,
        offset: Offset,
        value: ValueId,
    ) -> Result<(), Error> {
        let address = self.address(address, offset)?;
        let value = self.value(value)?;
        self.fit(Class::Word, &value)?;
        let mut bytes = value.to_bytes_le();
        bytes.resize(self.bytes(width), 0);
        if self.config.endian == Endian::Big {
            bytes.reverse();
        }
        self.memory.write(address, &bytes)
    }

    fn platform(&mut self, platform: super::PlatformId, args: Range) -> Result<HostResult, Error> {
        let platform = self
            .program
            .platform
            .get(platform.index())
            .ok_or_else(|| invalid("platform id"))?;
        let args = self.values(args)?;
        self.signature(platform.params, &args)?;
        let symbol = self
            .program
            .symbols
            .get(platform.name.index())
            .ok_or_else(|| invalid("symbol id"))?;
        let name = self
            .program
            .names
            .get(symbol.range())
            .and_then(|n| std::str::from_utf8(n).ok())
            .ok_or_else(|| invalid("platform name"))?;
        let result = self.host.call(name, &args, &mut self.memory)?;
        if let HostResult::Return(values) = &result {
            if self
                .program
                .routines
                .get(name)
                .is_some_and(|r| !r.comes_back)
            {
                return Err(invalid("non-returning host returned"));
            }
            self.signature(platform.returns, values)?;
        }
        Ok(result)
    }
}
