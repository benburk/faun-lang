//! A deterministic, target-independent machine-IR reference interpreter.
//!
//! `Natural` uses arbitrary precision. `Fixed` arithmetic must fit its declared
//! result (a violated proof is an error); `Word` arithmetic uses target-width
//! unsigned machine arithmetic; division and remainder are total (`x/0=0`,
//! `x%0=x`). Only explicit conversions truncate values. Builders normalize Fixed
//! constants before storing them; encoded constants must fit, just as with
//! `Target::accepts`. In particular, an oversized Word constant is an error,
//! not an implicit conversion. `fixed(0)` holds only zero.
//! Memory is byte-addressed, unaligned access is allowed, address
//! zero is invalid, and Data is read-only. These addresses are interpreter-local.
//!
//! Every evaluation also counts what it did: how often each function was
//! called and how many bytes were stored. Those counts are the cost oracle
//! representation work is judged by -- an allocation count alone reads a loop
//! that recopies its result every step as linear.
//!
//! Fuel charges one unit per instruction and region terminator, including calls
//! and loop iterations. Explicit stacks avoid native-stack overflow. The natural
//! size limit is a resource guard, not a language modulus. Host callbacks must
//! themselves terminate; their internal work cannot be metered by this evaluator.

use super::{
    Binary, Class, Definition, Direction, Exit, FunctionId, Offset, Op, Origin, Program, Range,
    RegionId, Relation, Returns, ValueId, Width,
};
use num_bigint::BigUint;
use number::Number;

mod number;

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub word_bits: u16,
    pub fuel: u64,
    pub max_natural_bits: u64,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            word_bits: 64,
            fuel: 100_000,
            max_natural_bits: 1_048_576,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidConfig,
    LayoutMismatch {
        expected: super::Layout,
        actual: super::Layout,
    },
    InvalidProgram(&'static str),
    FuelExhausted,
    SizeLimit,
    DoesNotFit(Class),
    InvalidMemory,
    ReadOnlyMemory,
    Host(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Values returned by the evaluated function, checked against its signature.
    Returned(Vec<BigUint>),
    /// A host halt's payload, not a function result.
    Halted(Vec<BigUint>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Evaluation {
    pub outcome: Outcome,
    pub globals: Vec<u8>,
    pub fuel_remaining: u64,
    pub counts: Counts,
}

/// What an evaluation did, counted as it went.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// Calls made to each function, by function; the evaluated function's
    /// own entry included.
    pub calls: Vec<u64>,
    /// Store instructions executed, and the bytes they wrote.
    pub stores: u64,
    pub stored_bytes: u64,
}

impl Counts {
    /// Calls made to every function named `name`, which is how a generated
    /// runtime helper such as `nat.allocate` is asked after.
    #[must_use]
    pub fn calls_to(&self, program: &Program, name: &str) -> u64 {
        program
            .functions
            .iter_enumerated()
            .filter(|(_, function)| program.name(function.name) == name)
            .map(|(id, _)| self.calls.get(id.index()).copied().unwrap_or(0))
            .sum()
    }
}

impl Evaluation {
    #[must_use]
    pub fn returned(&self) -> Option<&[BigUint]> {
        match &self.outcome {
            Outcome::Returned(values) => Some(values),
            Outcome::Halted(_) => None,
        }
    }

    #[must_use]
    pub fn halted(&self) -> Option<&[BigUint]> {
        match &self.outcome {
            Outcome::Halted(values) => Some(values),
            Outcome::Returned(_) => None,
        }
    }
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
            (Origin::Data, DATA_BASE, self.data.len())
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

    /// Room for `bytes` more after the globals, eight-aligned and zeroed:
    /// the address it starts at.
    ///
    /// # Errors
    /// If the globals would outgrow what an address holds.
    fn grow(&mut self, bytes: usize) -> Result<u64, Error> {
        let start = self.globals.len().next_multiple_of(8);
        let end = start.checked_add(bytes).ok_or(Error::InvalidMemory)?;
        self.globals.resize(end, 0);
        self.globals_base
            .checked_add(u64::try_from(start).map_err(|_| Error::InvalidMemory)?)
            .ok_or(Error::InvalidMemory)
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
// frame so recursion cannot overwrite the caller's SSA definitions. A frame
// holds only its own function's values, numbered when it is first called:
// sized to the whole program, every call would cost every value.
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
        returns: Returns<Range>,
    },
}

/// What an external call answers, in the interpreter's own numbers when
/// the program goes on to read them.
enum Answer {
    Halt(Vec<BigUint>),
    Return(Vec<Number>),
}

#[derive(Clone, Debug)]
struct CellValue {
    tag: u32,
    fields: Vec<Number>,
}

/// A buffer's elements, first to last, each as its leaves. A sequence
/// holding `len` of them holds the last `len`.
type BufferValue = Vec<Vec<Number>>;

/// Where a live call's values begin in [`Machine::slots`], and whose they are.
#[derive(Clone, Copy)]
struct Frame {
    function: FunctionId,
    base: usize,
}

struct Machine<'a, H> {
    program: &'a Program,
    config: Config,
    host: &'a mut H,
    memory: Memory<'a>,
    /// Every live call's values, end to end, the innermost last.
    slots: Vec<Option<Number>>,
    frames: Vec<Frame>,
    /// Each value's function and place in that function's frame, once the
    /// function has been called.
    places: Vec<Option<(FunctionId, u32)>>,
    /// Each function's frame size, once it has been called.
    sizes: Vec<Option<u32>>,
    /// The function each region belongs to, once numbered.
    regions: Vec<Option<FunctionId>>,
    cells: Vec<CellValue>,
    buffers: Vec<BufferValue>,
    tasks: Vec<Task>,
    counts: Counts,
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
    let actual = super::Layout {
        word_bits: config.word_bits,
    };
    if let Some(expected) = program.layout()
        && expected != actual
    {
        return Err(Error::LayoutMismatch { expected, actual });
    }
    let mut machine = Machine {
        program,
        config,
        host,
        memory: memory(program, config)?,
        slots: Vec::new(),
        frames: Vec::new(),
        places: vec![None; program.classes.len()],
        sizes: vec![None; program.functions.len()],
        regions: vec![None; program.regions.len()],
        cells: Vec::new(),
        buffers: Vec::new(),
        tasks: Vec::new(),
        counts: Counts {
            calls: vec![0; program.functions.len()],
            ..Counts::default()
        },
    };
    let args: Vec<Number> = args.iter().map(Number::from).collect();
    if let Some(outcome) = machine.call(function, &args, None)? {
        return Ok(machine.finish(outcome));
    }
    machine.run()
}

/// Where the data begins: past nought, which no datum is, and on a word, as
/// a target places it, so that an object in it has an even address.
pub const DATA_BASE: u64 = 8;

/// Where the globals begin: past the data and a byte more, so that nothing
/// reaches from one into the other, and on a word.
///
/// # Errors
/// If the data do not fit an address.
pub fn globals_base(program: &Program) -> Result<u64, Error> {
    u64::try_from(program.data.len())
        .ok()
        .and_then(|n| n.checked_add(DATA_BASE + 1))
        .map(|n| n.next_multiple_of(8))
        .ok_or(Error::InvalidMemory)
}

/// A fresh copy of the program's memory, placed where it fits the word.
fn memory(program: &Program, config: Config) -> Result<Memory<'_>, Error> {
    let globals_base = globals_base(program)?;
    let end = globals_base
        .checked_add(u64::try_from(program.globals.len()).map_err(|_| Error::InvalidMemory)?)
        .ok_or(Error::InvalidMemory)?;
    if config.word_bits < 64 && end > (1u64 << config.word_bits) {
        return Err(Error::InvalidMemory);
    }
    Ok(Memory {
        data: &program.data,
        globals: program.globals.clone(),
        globals_base,
    })
}

const fn invalid(what: &'static str) -> Error {
    Error::InvalidProgram(what)
}

/// Give each of `ids` the next place in `function`'s frame, which has
/// `size` so far; a value already placed there keeps its place.
fn place(
    places: &mut [Option<(FunctionId, u32)>],
    function: FunctionId,
    size: &mut u32,
    ids: &[ValueId],
) -> Result<(), Error> {
    for &id in ids {
        match places.get_mut(id.index()) {
            Some(Some((owner, _))) if *owner == function => {}
            Some(Some(_)) => return Err(invalid("value defined in two functions")),
            Some(slot @ None) => {
                *slot = Some((function, *size));
                *size += 1;
            }
            None => return Err(invalid("value id")),
        }
    }
    Ok(())
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
            .get(id)
            .copied()
            .ok_or_else(|| invalid("value id"))
    }

    fn width(&self, class: Class) -> Result<Option<u16>, Error> {
        match class {
            Class::Natural => Ok(None),
            Class::Cell | Class::Buffer | Class::Word | Class::Address => {
                Ok(Some(self.config.word_bits))
            }
            Class::Held(_) => match class.width() {
                Some(bits) if bits <= self.config.word_bits => Ok(Some(bits)),
                _ => Err(Error::DoesNotFit(class)),
            },
        }
    }

    fn fit(&self, class: Class, value: &Number) -> Result<(), Error> {
        match self.width(class)? {
            Some(bits) if value.bits() > u64::from(bits) => Err(Error::DoesNotFit(class)),
            None if value.bits() > self.config.max_natural_bits => Err(Error::SizeLimit),
            _ => Ok(()),
        }
    }

    fn convert(&self, class: Class, value: Number) -> Result<Number, Error> {
        let value = if let Some(bits) = self.width(class)? {
            value.low(bits)
        } else {
            value
        };
        self.fit(class, &value)?;
        Ok(value)
    }

    /// Where `id` lives in the innermost frame.
    fn slot(&self, id: ValueId) -> Option<usize> {
        let frame = self.frames.last()?;
        match *self.places.get(id.index())? {
            Some((function, at)) if function == frame.function => {
                Some(frame.base + usize::try_from(at).ok()?)
            }
            _ => None,
        }
    }

    fn value(&self, id: ValueId) -> Result<Number, Error> {
        self.slot(id)
            .and_then(|at| self.slots.get(at))
            .and_then(Option::as_ref)
            .cloned()
            .ok_or_else(|| invalid("undefined value"))
    }

    /// Number the values `function`'s body defines, once: its frame size.
    fn size(&mut self, function: FunctionId, body: RegionId) -> Result<usize, Error> {
        if let Some(size) = self.sizes[function.index()] {
            return usize::try_from(size).map_err(|_| invalid("frame size"));
        }
        let program = self.program;
        let ids = |range: Range| {
            program
                .operands
                .get(range.range())
                .ok_or_else(|| invalid("operand range"))
        };
        let mut size = 0u32;
        let mut pending = vec![body];
        while let Some(id) = pending.pop() {
            match self.regions.get_mut(id.index()) {
                Some(owner @ None) => *owner = Some(function),
                Some(Some(_)) => return Err(invalid("region entered twice")),
                None => return Err(invalid("region id")),
            }
            let region = program.regions[id];
            place(&mut self.places, function, &mut size, ids(region.params)?)?;
            for index in region.ops.range() {
                let (op, results) = self.instruction(index)?;
                place(&mut self.places, function, &mut size, ids(results)?)?;
                match op {
                    Op::If {
                        then_region,
                        else_region,
                        ..
                    } => pending.extend([then_region, else_region]),
                    Op::Loop { body, .. } => pending.push(body),
                    _ => {}
                }
            }
        }
        self.sizes[function.index()] = Some(size);
        usize::try_from(size).map_err(|_| invalid("frame size"))
    }

    fn values(&self, range: Range) -> Result<Vec<Number>, Error> {
        self.ids(range)?.iter().map(|&id| self.value(id)).collect()
    }

    fn bind(&mut self, range: Range, values: &[Number]) -> Result<(), Error> {
        let program = self.program;
        let ids = program
            .operands
            .get(range.range())
            .ok_or_else(|| invalid("operand range"))?;
        if ids.len() != values.len() {
            return Err(invalid("result arity"));
        }
        for (&id, value) in ids.iter().zip(values) {
            self.fit(self.class(id)?, value)?;
        }
        for (&id, value) in ids.iter().zip(values) {
            let at = self.slot(id).ok_or_else(|| invalid("value id"))?;
            self.slots[at] = Some(value.clone());
        }
        Ok(())
    }

    fn signature(&self, range: Range, values: &[Number]) -> Result<(), Error> {
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

    fn region(&mut self, id: RegionId, args: &[Number]) -> Result<(), Error> {
        let region = self
            .program
            .regions
            .get(id)
            .ok_or_else(|| invalid("region id"))?;
        self.bind(region.params, args)?;
        self.tasks.push(Task::Region { id, at: 0 });
        Ok(())
    }

    fn call(
        &mut self,
        id: FunctionId,
        args: &[Number],
        results: Option<Range>,
    ) -> Result<Option<Outcome>, Error> {
        let function = self
            .program
            .functions
            .get(id)
            .ok_or_else(|| invalid("function id"))?;
        self.signature(function.params, args)?;
        self.counts.calls[id.index()] += 1;
        match function.definition {
            Definition::Declared(_) => Err(invalid("function has not been defined")),
            Definition::Body(body) => {
                let base = self.slots.len();
                let size = self.size(id, body)?;
                self.slots.resize(base + size, None);
                self.frames.push(Frame { function: id, base });
                self.tasks.push(Task::Call {
                    results,
                    returns: function.returns,
                });
                self.region(body, args)?;
                Ok(None)
            }
            Definition::External => {
                if results.is_none() {
                    self.config.fuel = self
                        .config
                        .fuel
                        .checked_sub(1)
                        .ok_or(Error::FuelExhausted)?;
                }
                let answer = self.external(function.name, function.returns, args)?;
                self.answered(answer, results)
            }
        }
    }

    /// Bind what an external call answered to `results`, or, where nothing
    /// called it, finish with it.
    fn answered(
        &mut self,
        answer: Answer,
        results: Option<Range>,
    ) -> Result<Option<Outcome>, Error> {
        match (answer, results) {
            (Answer::Halt(values), _) => Ok(Some(Outcome::Halted(values))),
            (Answer::Return(values), Some(results)) => {
                self.bind(results, &values)?;
                Ok(None)
            }
            (Answer::Return(values), None) => Ok(Some(Outcome::Returned(
                values.iter().map(Number::to_big).collect(),
            ))),
        }
    }

    fn finish(self, outcome: Outcome) -> Evaluation {
        Evaluation {
            outcome,
            globals: self.memory.globals,
            fuel_remaining: self.config.fuel,
            counts: self.counts,
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
                .get(id)
                .ok_or_else(|| invalid("region id"))?;
            if at == region.ops.len() {
                let terminator = region
                    .terminator
                    .ok_or_else(|| invalid("missing region terminator"))?;
                let values = self.values(terminator.values)?;
                if let Some(values) = self.leave(terminator.exit, values)? {
                    let values = values.iter().map(Number::to_big).collect();
                    return Ok(self.finish(Outcome::Returned(values)));
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
            if let Some(outcome) = self.step(op, results)? {
                return Ok(self.finish(outcome));
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

    fn leave(&mut self, exit: Exit, values: Vec<Number>) -> Result<Option<Vec<Number>>, Error> {
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
                    let Returns::Values(returns) = returns else {
                        return Err(invalid("non-returning function returned"));
                    };
                    self.signature(returns, &values)?;
                    if let Some(frame) = self.frames.pop() {
                        self.slots.truncate(frame.base);
                    }
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
        let base = value.small().ok_or(Error::InvalidMemory)?;
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
        left: Number,
        right: &Number,
    ) -> Result<Number, Error> {
        // A monus answers at a class its operands need not fit; they were
        // checked where they were made.
        if op != Binary::Monus {
            self.fit(class, &left)?;
            self.fit(class, right)?;
        }
        let value = match op {
            Binary::Add => left.add(right),
            Binary::Mul => self.multiply(class, &left, right)?,
            Binary::Div => {
                if right.is_zero() {
                    Number::ZERO
                } else {
                    left.div(right)
                }
            }
            Binary::Mod => {
                if right.is_zero() {
                    left
                } else {
                    left.rem(right)
                }
            }
            Binary::And => left.bits_with(right, |a, b| a & b, |a, b| a & b),
            Binary::Or => left.bits_with(right, |a, b| a | b, |a, b| a | b),
            Binary::Xor => left.bits_with(right, |a, b| a ^ b, |a, b| a ^ b),
            Binary::ShiftUp | Binary::ShiftDown => moved(op, class, &left, right)?,
            Binary::Sub | Binary::Monus if left >= *right => left.sub(right),
            Binary::Sub if class == Class::Natural => Number::ZERO,
            Binary::Monus => Number::ZERO,
            // Both fit the word, so the difference wraps within one; and
            // the same at a class that wraps, which a word holds.
            Binary::Sub if class == Class::Word || class.wraps() => {
                wrapping_sub(class, &left, right)?
            }
            Binary::Sub => return Err(Error::DoesNotFit(class)),
        };
        // A shift by a worked-out distance is a fit requirement even where
        // the class wraps: see `Class::wraps`.
        if class == Class::Word || (class.wraps() && op != Binary::ShiftUp) {
            self.convert(class, value)
        } else {
            self.fit(class, &value)?;
            Ok(value)
        }
    }

    /// A value with its bits moved, which is a product or quotient by a
    /// power of two and answers to the same fit rule as one.
    fn shifted(
        &self,
        direction: Direction,
        class: Class,
        value: &Number,
        by: u16,
    ) -> Result<Number, Error> {
        self.fit(class, value)?;
        let held = match direction {
            Direction::Up => value.shl(by),
            Direction::Down => value.shr(by),
        };
        if class == Class::Word || class.wraps() {
            self.convert(class, held)
        } else {
            self.fit(class, &held)?;
            Ok(held)
        }
    }

    fn multiply(&self, class: Class, left: &Number, right: &Number) -> Result<Number, Error> {
        // A nonzero product needs m+n-1 or m+n bits. Reject obviously oversized
        // products before allocating them, without rejecting any fitting value.
        // The ambiguous boundary allocates at most cap+1 result bits; binary's
        // exact fit check then decides it. Zero products need no allocation.
        if left.is_zero() || right.is_zero() {
            return Ok(Number::ZERO);
        }
        if class == Class::Natural
            && left
                .bits()
                .checked_add(right.bits())
                .and_then(|bits| bits.checked_sub(1))
                .is_none_or(|bits| bits > self.config.max_natural_bits)
        {
            return Err(Error::SizeLimit);
        }
        Ok(left.mul(right))
    }

    fn constant(&self, class: Class, value: u64) -> Result<Number, Error> {
        let value = Number::from(value);
        self.fit(class, &value)?;
        Ok(value)
    }

    // A non-local host halt is returned directly rather than disguised as a
    // function return, which would incorrectly execute caller continuations.
    fn step(&mut self, op: Op, results: Range) -> Result<Option<Outcome>, Error> {
        match op {
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                let region = if self.value(condition)? == Number::ZERO {
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
                return self.call(function, &args, Some(results));
            }
            _ => {
                self.scalar(op, results)?;
            }
        }
        Ok(None)
    }

    /// Which of two a comparison says, as the nought or one it answers.
    fn compared(&self, relation: Relation, left: ValueId, right: ValueId) -> Result<Number, Error> {
        let (left, right) = (self.value(left)?, self.value(right)?);
        Ok(Number::from(u8::from(match relation {
            Relation::Equal => left == right,
            Relation::Less => left < right,
        })))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one arm per instruction; the length is the patterns"
    )]
    /// Run an instruction that neither branches nor calls, binding what it
    /// answers to `results`.
    fn scalar(&mut self, op: Op, results: Range) -> Result<(), Error> {
        let value = match op {
            Op::Constant { value } => self.constant(self.result_class(results)?, value)?,
            Op::NaturalConstant(id) => self.natural(id)?,
            Op::AddressOf(id) => Number::from(self.datum_address(id)?),
            Op::Cell { tag, fields, .. } => {
                let fields = self.values(fields)?;
                self.cells.push(CellValue { tag, fields });
                Number::from(self.cells.len())
            }
            Op::CellTag { cell } => Number::from(self.cell(cell)?.tag),
            Op::BufferEmpty { .. } | Op::BufferRoom { .. } => {
                self.buffers.push(Vec::new());
                Number::from(self.buffers.len())
            }
            // Nothing outside reads a buffer this tier has not laid out.
            Op::BufferKnown {
                elements,
                shape,
                bytes,
            } => {
                let leaves: Vec<_> =
                    super::model::known_leaves(self.program.datum_bytes(elements), bytes)
                        .map(Number::from)
                        .collect();
                let elements = leaves
                    .chunks(self.program.shaped(shape).len())
                    .map(<[Number]>::to_vec)
                    .collect();
                self.buffers.push(elements);
                Number::from(self.buffers.len())
            }
            Op::BufferAt { .. } => return Err(invalid("a buffer's address before layout")),
            Op::Keep { .. } => return self.bind(results, &[]),
            // A sequence built here is a buffer of its own, starting at its
            // first element.
            Op::BufferPush { operands, .. } => {
                let operands = self.ids(operands)?.to_vec();
                let (sequence, fields) = operands.split_at(3);
                let first = fields
                    .iter()
                    .map(|&id| self.value(id))
                    .collect::<Result<Vec<_>, _>>()?;
                let rest = self.elements((sequence[0], sequence[1], sequence[2]))?;
                let mut elements = Vec::with_capacity(rest.len() + 1);
                elements.push(first);
                elements.extend_from_slice(rest);
                self.buffers.push(elements);
                let sequence = [Number::from(self.buffers.len()), Number::ZERO];
                return self.bind(results, &sequence);
            }
            Op::BufferAppend { operands, .. } => {
                let operands = self.ids(operands)?.to_vec();
                let (sequence, fields) = operands.split_at(3);
                let last = fields
                    .iter()
                    .map(|&id| self.value(id))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut elements = self
                    .elements((sequence[0], sequence[1], sequence[2]))?
                    .to_vec();
                elements.push(last);
                self.buffers.push(elements);
                let sequence = [Number::from(self.buffers.len()), Number::ZERO];
                return self.bind(results, &sequence);
            }
            Op::BufferReplace { operands, .. } => {
                let operands = self.ids(operands)?.to_vec();
                let (sequence, fields) = operands.split_at(4);
                let written = fields
                    .iter()
                    .map(|&id| self.value(id))
                    .collect::<Result<Vec<_>, _>>()?;
                let index = self.value(sequence[3])?;
                let mut elements = self
                    .elements((sequence[0], sequence[1], sequence[2]))?
                    .to_vec();
                let slot = index
                    .index()
                    .and_then(|index| elements.get_mut(index))
                    .ok_or_else(|| invalid("a replacement past its sequence"))?;
                *slot = written;
                self.buffers.push(elements);
                let sequence = [Number::from(self.buffers.len()), Number::ZERO];
                return self.bind(results, &sequence);
            }
            Op::BufferPrepend { operands, .. } | Op::BufferExtend { operands, .. } => {
                let operands = self.ids(operands)?.to_vec();
                let [first, then] =
                    [0, 3].map(|at| (operands[at], operands[at + 1], operands[at + 2]));
                let (first, then) = if matches!(op, Op::BufferPrepend { .. }) {
                    (then, first)
                } else {
                    (first, then)
                };
                let mut elements = self.elements(first)?.to_vec();
                if matches!(op, Op::BufferPrepend { .. }) {
                    elements.reverse();
                }
                elements.extend_from_slice(self.elements(then)?);
                self.buffers.push(elements);
                let sequence = [Number::from(self.buffers.len()), Number::ZERO];
                return self.bind(results, &sequence);
            }
            Op::BufferField {
                buffer,
                start,
                index,
                ..
            } => self
                .element(buffer, start)?
                .get(usize::try_from(index).map_err(|_| invalid("buffer field"))?)
                .cloned()
                .ok_or_else(|| invalid("buffer field"))?,
            Op::CellField { cell, index, .. } => self
                .cell(cell)?
                .fields
                .get(usize::try_from(index).map_err(|_| invalid("cell field index"))?)
                .cloned()
                .ok_or_else(|| invalid("cell field index"))?,
            Op::Binary { op, left, right } => self.binary(
                op,
                self.result_class(results)?,
                self.value(left)?,
                &self.value(right)?,
            )?,
            Op::Shift {
                direction,
                value,
                by,
            } => self.shifted(
                direction,
                self.result_class(results)?,
                &self.value(value)?,
                by,
            )?,
            Op::Compare {
                relation,
                left,
                right,
            } => self.compared(relation, left, right)?,
            Op::Convert { value } => {
                self.convert(self.result_class(results)?, self.value(value)?)?
            }
            Op::Float { float, operands } => {
                let patterns = self
                    .values(operands)?
                    .iter()
                    .map(|pattern| pattern.small().ok_or_else(|| invalid("a float's operand")))
                    .collect::<Result<Vec<_>, _>>()?;
                Number::from(float.calculate(&patterns))
            }
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
                return self.bind(results, &[]);
            }
            _ => return Err(invalid("expected scalar instruction")),
        };
        self.bind(results, std::slice::from_ref(&value))
    }

    /// The `len` elements of a buffer from `start`: what a sequence holds.
    fn elements(
        &self,
        (buffer, start, len): (ValueId, ValueId, ValueId),
    ) -> Result<&[Vec<Number>], Error> {
        let elements = self.buffer(buffer)?;
        let start = self
            .value(start)?
            .index()
            .ok_or_else(|| invalid("buffer start"))?;
        let len = self
            .value(len)?
            .index()
            .ok_or_else(|| invalid("buffer length"))?;
        start
            .checked_add(len)
            .and_then(|end| elements.get(start..end))
            .ok_or_else(|| invalid("buffer length"))
    }

    /// Element `start` of a buffer.
    fn element(&self, buffer: ValueId, start: ValueId) -> Result<&[Number], Error> {
        let elements = self.buffer(buffer)?;
        let start = self
            .value(start)?
            .index()
            .ok_or_else(|| invalid("buffer start"))?;
        elements
            .get(start)
            .map(Vec::as_slice)
            .ok_or_else(|| invalid("buffer start"))
    }

    fn buffer(&self, buffer: ValueId) -> Result<&[Vec<Number>], Error> {
        let handle = self
            .value(buffer)?
            .index()
            .ok_or_else(|| invalid("buffer handle"))?;
        handle
            .checked_sub(1)
            .and_then(|at| self.buffers.get(at))
            .map(Vec::as_slice)
            .ok_or_else(|| invalid("buffer handle"))
    }

    fn cell(&self, id: ValueId) -> Result<&CellValue, Error> {
        let handle = self
            .value(id)?
            .index()
            .ok_or_else(|| invalid("cell handle"))?;
        let index = handle
            .checked_sub(1)
            .ok_or_else(|| invalid("cell handle"))?;
        self.cells.get(index).ok_or_else(|| invalid("cell handle"))
    }

    fn natural(&self, id: super::DataId) -> Result<Number, Error> {
        let span = self
            .program
            .spans
            .get(id)
            .ok_or_else(|| invalid("data id"))?;
        if span.origin != Origin::Data {
            return Err(invalid("natural constant outside Data"));
        }
        let address = self.datum_address(id)?;
        let len = usize::try_from(span.len).map_err(|_| Error::InvalidMemory)?;
        let value = Number::from_bytes_le(self.memory.read(address, len)?);
        self.fit(Class::Natural, &value)?;
        Ok(value)
    }

    fn datum_address(&self, id: super::DataId) -> Result<u64, Error> {
        let span = self
            .program
            .spans
            .get(id)
            .ok_or_else(|| invalid("data id"))?;
        let base = match span.origin {
            Origin::Data => DATA_BASE,
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

    fn load(&self, width: Width, address: ValueId, offset: Offset) -> Result<Number, Error> {
        let bytes = self
            .memory
            .read(self.address(address, offset)?, self.bytes(width))?;
        Ok(Number::from_bytes_le(bytes))
    }

    fn bytes(&self, width: Width) -> usize {
        usize::from(width.bytes(self.config.word_bits))
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
        self.counts.stores += 1;
        self.counts.stored_bytes += u64::try_from(bytes.len()).expect("a width in bytes");
        self.memory.write(address, &bytes)
    }

    fn external(
        &mut self,
        symbol: super::model::Symbol,
        returns: Returns<Range>,
        args: &[Number],
    ) -> Result<Answer, Error> {
        let symbol = self
            .program
            .symbols
            .get(symbol)
            .ok_or_else(|| invalid("symbol id"))?;
        let name = self
            .program
            .names
            .get(symbol.range())
            .and_then(|n| std::str::from_utf8(n).ok())
            .ok_or_else(|| invalid("platform name"))?;
        // Fresh memory is the interpreter's own to hand out: after the
        // globals, where nothing else is, and aligned for any word.
        let result = if name == "grow" {
            let [bytes] = args else {
                return Err(invalid("grow takes one size"));
            };
            let bytes = bytes.index().ok_or(Error::InvalidMemory)?;
            vec![Number::from(self.memory.grow(bytes)?)]
        } else {
            let args: Vec<BigUint> = args.iter().map(Number::to_big).collect();
            match self.host.call(name, &args, &mut self.memory)? {
                HostResult::Halt(values) => return Ok(Answer::Halt(values)),
                HostResult::Return(values) => values.iter().map(Number::from).collect(),
            }
        };
        let Returns::Values(classes) = returns else {
            return Err(invalid("non-returning host returned"));
        };
        self.signature(classes, &result)?;
        Ok(Answer::Return(result))
    }
}

/// `left - right` modulo the word both fit.
fn wrapping_sub(class: Class, left: &Number, right: &Number) -> Result<Number, Error> {
    match (left.small(), right.small()) {
        (Some(left), Some(right)) => Ok(Number::from(left.wrapping_sub(right))),
        _ => Err(Error::DoesNotFit(class)),
    }
}

/// `left` with its bits moved `right` places, up or down as `op` says: a
/// distance a word does not hold moves every bit out.
fn moved(op: Binary, class: Class, left: &Number, right: &Number) -> Result<Number, Error> {
    let by = right.small().and_then(|by| u16::try_from(by).ok());
    Ok(match (op, by) {
        (Binary::ShiftUp, Some(by)) => left.shl(by),
        (_, Some(by)) => left.shr(by),
        (Binary::ShiftUp, None) if left.is_zero() => Number::ZERO,
        (Binary::ShiftUp, None) => return Err(Error::DoesNotFit(class)),
        (_, None) => Number::ZERO,
    })
}
