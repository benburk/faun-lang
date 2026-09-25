//! `if` and `loop` are what wasm already has, so nothing is reconstructed.
//! A word is an `i32`; region parameters and results live in locals.
//!
//! - A transfer pushes every source before setting any destination, leaving
//!   the parallel move to wasm's operand stack.
//! - Returning from `_start` already exits zero, so inside the entry an
//!   `exit 0` is a `return`, and at the end of the body it is the `end`
//!   that is there anyway. A program that only ever leaves with nought
//!   imports nothing, which is most of a small module.

use super::{Body, CALL, Code, DROP, END, I32, I32_CONST, Segment};
use crate::WORD_BITS;
use faun_core::ir::{
    Binary, Class, DataId, Direction, Exit, FunctionId, Offset, Op, Origin, Program, Range,
    RegionId, Relation, Terminator, ValueId, Width,
};
use faun_core::targets::bytes::{Bytes, len32};

const STDIN: i32 = 0;
const STDOUT: i32 = 1;
const STDERR: i32 = 2;

/// Linear memory: the cell `fd_write`/`fd_read` reports its byte count into,
/// then argument scratch, four-byte aligned WASI vectors, then program data.
const NWRITTEN: i32 = 0;
/// Where `args_sizes_get` reports the count. The cell beside it is the one
/// `fd_write` reports into, and neither is live while the other is called,
/// so the second thing `args_sizes_get` answers goes there and is dropped.
const ARGC: i32 = 4;
const IOVECS: u32 = 8;
const IOVEC_LEN: u32 = 8;

const UNREACHABLE: u8 = 0x00;
const BLOCK: u8 = 0x02;
const LOOP: u8 = 0x03;
const IF: u8 = 0x04;
const ELSE: u8 = 0x05;
const BR: u8 = 0x0C;
const RETURN: u8 = 0x0F;
const LOCAL_GET: u8 = 0x20;
const LOCAL_SET: u8 = 0x21;
const I32_LOAD: u8 = 0x28;
const I32_LOAD8_U: u8 = 0x2D;
const I32_STORE: u8 = 0x36;
const I32_STORE8: u8 = 0x3A;
const I32_AND: u8 = 0x71;
const I32_SHL: u8 = 0x74;
const I32_SHR_U: u8 = 0x76;
const MEMORY_GROW: u8 = 0x40;

/// A word on this target, in bytes, and a page as a power of two.
const WORD: i32 = 4;
const PAGE_BITS: i32 = 16;
const I32_ADD: u8 = 0x6A;
const I32_SUB: u8 = 0x6B;
const I32_MUL: u8 = 0x6C;
const I32_DIV_U: u8 = 0x6E;
const I32_REM_U: u8 = 0x70;
const I32_EQ: u8 = 0x46;
const I32_LT_U: u8 = 0x49;
const I32_GE_U: u8 = 0x4F;
const SELECT: u8 = 0x1B;
const EMPTY: u8 = 0x40;

/// How wide a class is held, which for anything unfixed is a word.
fn bits(class: Class) -> u16 {
    class.bits(WORD_BITS)
}

fn entry_argc(program: &Program) -> Option<ValueId> {
    let entry = program.entry();
    (program.parameter_names(entry).next() == Some("argc")).then(|| {
        let body = program
            .function(entry)
            .body()
            .expect("the entry has a body");
        program.values(program.region(body).params)[0]
    })
}

#[derive(Clone, Copy)]
enum Source {
    Const(u64),
    Addr(DataId),
    Local(u32),
}

#[expect(
    clippy::too_many_lines,
    reason = "memory scratch and import indices must be planned before bodies"
)]
pub(crate) fn lower(program: &Program) -> Code {
    let plan = Plan::new(program);

    let after_writes = IOVECS + IOVEC_LEN * len32(plan.writes);
    let read = plan.reads.then_some(ReadScratch {
        iovec: after_writes,
        byte: after_writes + IOVEC_LEN,
    });
    // Keep following words aligned; the read buffer itself is one byte.
    let data_start = after_writes + read.map_or(0, |_| IOVEC_LEN + 4);

    let writes = plan.writes > 0;
    let mut state = Lowering {
        program,
        entry: program.entry(),
        role: FunctionRole::Entry,
        iovecs: vec![None; plan.writes],
        read,
        plan,
        data_start,
        body: Bytes::default(),
        written: 0,
        depth: 0,
        ifs: Vec::new(),
        loops: Vec::new(),
        imports: Vec::new(),
    };

    // Which imports exist decides their indices, so it has to be settled
    // before anything calls one.
    if writes {
        state.imports.push("fd_write");
    }
    if state.read.is_some() {
        state.imports.push("fd_read");
    }
    if state.needs_proc_exit() {
        state.imports.push("proc_exit");
    }
    if entry_argc(program).is_some() {
        state.imports.push("args_sizes_get");
    }

    let bodies = state.bodies();

    Code {
        data: state.segments(data_start),
        // WASI refuses to run a module that imports anything and exports no
        // memory, even when nothing it imports reads one.
        memory: !state.imports.is_empty(),
        entry: state.entry.index(),
        imports: state.imports,
        bodies,
    }
}

#[derive(Clone, Copy)]
struct Frame {
    /// Dense emitted index; external function IDs do not occupy wasm bodies.
    index: u32,
    locals: u32,
}

struct Plan {
    source: Vec<Source>,
    locals: u32,
    writes: usize,
    reads: bool,
    functions: Vec<Option<Frame>>,
}

impl Plan {
    /// Locals restart per body: parameters first, then the rest. External
    /// declarations have no frame and do not consume an emitted body index.
    fn new(program: &Program) -> Self {
        let mut plan = Self {
            source: vec![Source::Local(0); program.values_count()],
            locals: 0,
            writes: 0,
            reads: false,
            functions: Vec::new(),
        };
        let mut index = 0;
        for function in program.functions() {
            let frame = function.body().map(|body| {
                plan.locals = 0;
                plan.walk(program, body);
                let frame = Frame {
                    index,
                    locals: plan.locals,
                };
                index += 1;
                frame
            });
            plan.functions.push(frame);
        }
        plan
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one exhaustive walk assigns value storage and counts platform calls"
    )]
    fn walk(&mut self, program: &Program, region: RegionId) {
        for &param in program.values(program.region(region).params) {
            self.give_local(param);
        }
        for (op, results) in program.walk(region) {
            match *op {
                Op::Constant { value, .. } => {
                    self.source[results[0].index()] = Source::Const(value);
                }
                Op::AddressOf(data) => self.source[results[0].index()] = Source::Addr(data),
                _ => {
                    for &result in results {
                        self.give_local(result);
                    }
                }
            }
            match *op {
                Op::Call { function, .. }
                    if program.function(function).external().is_some_and(|symbol| {
                        matches!(program.name(symbol), "write!" | "write_error!")
                    }) =>
                {
                    self.writes += 1;
                }
                Op::Call { function, .. }
                    if program
                        .function(function)
                        .external()
                        .is_some_and(|symbol| program.name(symbol) == "read_byte!") =>
                {
                    self.reads = true;
                }
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.walk(program, then_region);
                    self.walk(program, else_region);
                }
                Op::Loop { body, .. } => self.walk(program, body),
                _ => {}
            }
        }
    }

    fn give_local(&mut self, value: ValueId) {
        self.source[value.index()] = Source::Local(self.locals);
        self.locals += 1;
    }
}

/// The two labels a terminator can branch to: the `loop` to go round
/// again, the `block` around it to leave.
struct LoopFrame {
    params: Vec<ValueId>,
    again: usize,
    results: Vec<ValueId>,
    exit: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FunctionRole {
    Entry,
    Function,
}

impl FunctionRole {
    fn at(index: usize, entry: FunctionId) -> Self {
        if index == entry.index() {
            Self::Entry
        } else {
            Self::Function
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    Interior,
    /// The final instruction of the entry's outermost region.
    EntryEnd,
}

#[derive(Clone, Copy)]
struct ReadScratch {
    iovec: u32,
    byte: u32,
}

struct Lowering<'a> {
    program: &'a Program,
    data_start: u32,
    entry: FunctionId,
    role: FunctionRole,
    plan: Plan,
    body: Bytes,
    /// Each call's vector, where its contents were known.
    iovecs: Vec<Option<(u32, u32)>>,
    read: Option<ReadScratch>,
    written: usize,
    /// How many labels enclose the instruction being emitted.
    depth: usize,
    ifs: Vec<Vec<ValueId>>,
    loops: Vec<LoopFrame>,
    imports: Vec<&'static str>,
}

impl Lowering<'_> {
    /// Falling off the end of `_start` already means success, so a program
    /// that only ever leaves with nought needs no import, and that is most
    /// of an import section.
    ///
    /// Anything else has to be said: a status the entry did not work out to
    /// nought, and every exit from somewhere a `return` would not end the
    /// program.
    fn needs_proc_exit(&self) -> bool {
        self.program
            .functions()
            .iter()
            .enumerate()
            .any(|(id, function)| {
                function
                    .body()
                    .is_some_and(|body| self.exits(body, FunctionRole::at(id, self.entry)))
            })
    }

    /// Whether a region holds an exit this target has to make a call for.
    /// Leaving `_start` with nought is a `return`, which is the same thing
    /// and costs a byte; leaving anywhere else, or with anything else, is
    /// the routine.
    fn exits(&self, region: RegionId, role: FunctionRole) -> bool {
        let status = role == FunctionRole::Entry
            && self
                .program
                .region(region)
                .terminator
                .is_some_and(|t| t.exit == Exit::Return)
            && self
                .program
                .outgoing(region)
                .first()
                .is_some_and(|&value| self.constant(value) != Some(0));
        status
            || self.program.ops(region).iter().any(|op| match *op {
                Op::Call { function, args } => {
                    self.program
                        .function(function)
                        .external()
                        .is_some_and(|symbol| self.program.name(symbol) == "exit!")
                        && !(role == FunctionRole::Entry && self.leaves_with_nought(args))
                }
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => self.exits(then_region, role) || self.exits(else_region, role),
                Op::Loop { body, .. } => self.exits(body, role),
                _ => false,
            })
    }

    fn leaves_with_nought(&self, args: Range) -> bool {
        self.program
            .values(args)
            .first()
            .is_some_and(|&value| self.constant(value) == Some(0))
    }

    /// `_start` returns nothing of its own, whatever the entry's signature
    /// says: WASI takes the status through `proc_exit`.
    fn bodies(&mut self) -> Vec<Body> {
        let mut bodies = Vec::new();
        for (id, function) in self.program.functions().iter().enumerate() {
            let Some(body) = function.body() else {
                continue;
            };
            self.role = FunctionRole::at(id, self.entry);
            self.body = Bytes::default();
            if self.role == FunctionRole::Entry
                && let Some(argc) = entry_argc(self.program)
            {
                self.count(argc);
            }
            self.region(body);
            // Wasm does not infer that both branches return, or that a
            // void host import never returns. Supply its stack-polymorphic
            // marker when a result-bearing function has no final transfer.
            if self.role != FunctionRole::Entry
                && !function.returns.classes().is_empty()
                && self.program.region(body).terminator.is_none()
            {
                self.body.byte(UNREACHABLE);
            }

            let declared = len32(function.params.len());
            let params = if self.role == FunctionRole::Entry {
                0
            } else {
                declared
            };
            bodies.push(Body {
                params,
                locals: self.plan.functions[id].expect("a body has a frame").locals - params,
                returns: if self.role == FunctionRole::Entry {
                    0
                } else {
                    len32(function.returns.classes().len())
                },
                code: std::mem::take(&mut self.body).finish(),
            });
        }
        bodies
    }

    fn segments(&self, data_start: u32) -> Vec<Segment> {
        let mut vectors = Vec::new();
        for iovec in &self.iovecs {
            // A call whose arguments were not constant fills its own vector.
            let (base, length) = iovec.unwrap_or((0, 0));
            vectors.extend_from_slice(&base.to_le_bytes());
            vectors.extend_from_slice(&length.to_le_bytes());
        }

        let mut data = Vec::new();
        if vectors.iter().any(|&byte| byte != 0) {
            data.push(Segment {
                offset: IOVECS,
                bytes: vectors,
            });
        }
        if let Some(read) = self.read {
            let mut iovec = Vec::with_capacity(8);
            iovec.extend_from_slice(&read.byte.to_le_bytes());
            iovec.extend_from_slice(&1u32.to_le_bytes());
            data.push(Segment {
                offset: read.iovec,
                bytes: iovec,
            });
        }
        let mut blob = self.program.data().to_vec();
        blob.extend_from_slice(self.program.globals());
        if !blob.is_empty() {
            data.push(Segment {
                offset: data_start,
                bytes: blob,
            });
        }
        data
    }

    fn region(&mut self, region: RegionId) {
        // The program outlives this, so the walk borrows it rather than
        // `self`, and the loop stays one pass over a contiguous run.
        let program = self.program;
        let terminator = program.region(region).terminator;
        // Where the last of these instructions is the last of `_start`:
        // what happens after it is running off the end, which is already
        // an exit with nought.
        let ending = self.role == FunctionRole::Entry && self.depth == 0 && terminator.is_none();
        let last = program.ops(region).len();
        for (at, (op, results)) in program.walk(region).enumerate() {
            let position = if ending && at + 1 == last {
                Position::EntryEnd
            } else {
                Position::Interior
            };
            self.instruction(op, results, position);
        }
        if let Some(terminator) = terminator {
            self.terminator(terminator);
        } else if self.depth > 0 {
            self.body.byte(UNREACHABLE);
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one call per op; the length is the patterns"
    )]
    fn instruction(&mut self, op: &Op, results: &[ValueId], position: Position) {
        let program = self.program;
        match op {
            Op::NaturalConstant(_) => unreachable!("target acceptance rejects arbitrary precision"),
            Op::Cell { .. }
            | Op::CellTag { .. }
            | Op::CellField { .. }
            | Op::BufferEmpty
            | Op::BufferPush { .. }
            | Op::BufferField { .. } => {
                unreachable!("target preparation legalizes abstract cells")
            }
            Op::Constant { .. } | Op::AddressOf(_) => {}
            Op::Binary { op, left, right } => {
                let opcode = match op {
                    Binary::Add => I32_ADD,
                    Binary::Sub => I32_SUB,
                    Binary::Monus => {
                        self.monus(*left, *right, results[0]);
                        return;
                    }
                    Binary::Mul => {
                        self.push(*left);
                        self.push(*right);
                        self.body.byte(I32_MUL);
                        self.set(results[0]);
                        return;
                    }
                    Binary::Div | Binary::Mod => {
                        self.divide(*op, *left, *right, results[0]);
                        return;
                    }
                };
                self.binary(opcode, *left, *right, results[0]);
            }
            Op::Shift {
                direction,
                value,
                by,
            } => {
                self.push(*value);
                self.constant_i32(i32::from(*by));
                self.body.byte(match direction {
                    Direction::Up => I32_SHL,
                    Direction::Down => I32_SHR_U,
                });
                self.set(results[0]);
            }
            Op::Compare {
                relation,
                left,
                right,
            } => {
                let opcode = match relation {
                    Relation::Equal => I32_EQ,
                    Relation::Less => I32_LT_U,
                };
                self.binary(opcode, *left, *right, results[0]);
            }
            Op::Load {
                width,
                address,
                offset,
            } => self.load_at(*width, *address, *offset, results[0]),
            Op::Store {
                width,
                address,
                offset,
                value,
            } => self.store_at(*width, *address, *offset, *value),
            Op::Convert { value } => {
                self.push(*value);
                let kept = bits(self.program.class(results[0]));
                if kept < bits(self.program.class(*value)) {
                    self.narrow(kept);
                }
                self.set(results[0]);
            }
            Op::Call { function, args } => {
                if let Some(symbol) = program.function(*function).external() {
                    self.platform_named(
                        program.name(symbol),
                        program.values(*args),
                        results,
                        position,
                    );
                    return;
                }
                for &arg in program.values(*args) {
                    self.push(arg);
                }
                let imports = len32(self.imports.len());
                self.call(
                    imports
                        + self.plan.functions[function.index()]
                            .expect("an internal callee")
                            .index,
                );
                for &result in results.iter().rev() {
                    self.set(result);
                }
            }
            Op::If {
                condition,
                then_region,
                else_region,
            } => self.conditional(*condition, *then_region, *else_region, results),
            Op::Loop { initial, body } => {
                self.repeat(program.values(*initial), *body, results);
            }
        }
    }

    fn load_at(&mut self, width: Width, address: ValueId, offset: Offset, result: ValueId) {
        self.push(address);
        self.access(width, offset, I32_LOAD8_U, I32_LOAD);
        self.set(result);
    }

    fn store_at(&mut self, width: Width, address: ValueId, offset: Offset, value: ValueId) {
        self.push(address);
        self.push(value);
        self.access(width, offset, I32_STORE8, I32_STORE);
    }

    /// A word here is 32 bits, so anything narrower is masked back down.
    fn narrow(&mut self, kept: u16) {
        assert!(kept <= WORD_BITS, "no {kept}-bit form on this target");
        if kept < WORD_BITS {
            let mask = (1u32 << kept) - 1;
            self.constant_i32(mask.cast_signed());
            self.body.byte(I32_AND);
        }
    }

    /// Fixed widths are fit requirements, so arithmetic never masks an
    /// answer. Only an explicit narrowing conversion may discard bits.
    fn binary(&mut self, opcode: u8, left: ValueId, right: ValueId, result: ValueId) {
        self.push(left);
        self.push(right);
        self.body.byte(opcode);
        self.set(result);
    }

    /// The wrapped difference where nothing borrowed, and zero where
    /// something did, chosen without a branch.
    fn monus(&mut self, left: ValueId, right: ValueId, result: ValueId) {
        self.push(left);
        self.push(right);
        self.body.byte(I32_SUB);
        self.constant_i32(0);
        self.push(left);
        self.push(right);
        self.body.byte(I32_GE_U);
        self.body.byte(SELECT);
        self.set(result);
    }

    /// WASM traps on a zero divisor; the machine IR's operations are total.
    fn divide(&mut self, op: Binary, left: ValueId, right: ValueId, result: ValueId) {
        self.push(right);
        self.body.byte(IF);
        self.body.byte(0x7F); // one i32 result
        self.open();
        self.push(left);
        self.push(right);
        self.body.byte(if op == Binary::Div {
            I32_DIV_U
        } else {
            I32_REM_U
        });
        self.body.byte(ELSE);
        if op == Binary::Div {
            self.constant_i32(0);
        } else {
            self.push(left);
        }
        self.close();
        self.set(result);
    }

    fn conditional(
        &mut self,
        condition: ValueId,
        then_region: RegionId,
        else_region: RegionId,
        results: &[ValueId],
    ) {
        self.push(condition);
        self.body.byte(IF);
        self.body.byte(EMPTY);
        self.open();

        self.ifs.push(results.to_vec());
        self.region(then_region);
        self.body.byte(ELSE);
        self.region(else_region);
        self.ifs.pop();

        self.close();
    }

    fn repeat(&mut self, initial: &[ValueId], body: RegionId, results: &[ValueId]) {
        let program = self.program;
        let params = program.values(program.region(body).params);
        self.transfer(initial, params);
        self.body.byte(BLOCK);
        self.body.byte(EMPTY);
        self.open();
        let exit = self.depth - 1;
        self.body.byte(LOOP);
        self.body.byte(EMPTY);
        self.open();
        let again = self.depth - 1;

        self.loops.push(LoopFrame {
            params: params.to_vec(),
            again,
            results: results.to_vec(),
            exit,
        });
        self.region(body);
        self.loops.pop();

        self.close();
        self.close();
    }

    fn terminator(&mut self, terminator: Terminator) {
        let program = self.program;
        let values = program.values(terminator.values);
        match terminator.exit {
            // The `end` that closes the if is the branch.
            Exit::Yield => {
                let results = self.ifs.last().expect("a yield inside an if").clone();
                self.transfer(values, &results);
            }
            Exit::Continue => {
                let frame = self.loops.last().expect("a continue inside a loop");
                let (params, again) = (frame.params.clone(), frame.again);
                self.transfer(values, &params);
                self.branch(again);
            }
            Exit::Break => {
                let frame = self.loops.last().expect("a break inside a loop");
                let (results, exit) = (frame.results.clone(), frame.exit);
                self.transfer(values, &results);
                self.branch(exit);
            }
            Exit::Return => {
                if self.role == FunctionRole::Entry {
                    // The status the entry returns is the program's, and a
                    // WASI command has no result of its own.
                    if let Some(index) = self.import("proc_exit") {
                        for &value in values {
                            self.push(value);
                        }
                        self.call(index);
                    } else if self.depth > 0 {
                        self.body.byte(RETURN);
                    }
                } else {
                    for &value in values {
                        self.push(value);
                    }
                    self.body.byte(RETURN);
                }
            }
        }
    }

    /// Leaving `_start` with nought is returning from it, and a return at
    /// the end of a body is the `end` that body ends with anyway. Every
    /// other way out is the routine, which is why it is imported.
    fn leave(&mut self, status: ValueId, position: Position) {
        if self.role == FunctionRole::Entry && self.constant(status) == Some(0) {
            if position != Position::EntryEnd {
                self.body.byte(RETURN);
            }
        } else if let Some(index) = self.import("proc_exit") {
            self.push(status);
            self.call(index);
        }
    }

    /// The opcode for the width, then its alignment as a power of two and
    /// the constant part of its address.
    /// How many arguments the program was handed.
    ///
    /// Two cells are written and one is wanted: the count comes back
    /// through memory, and what the call answers is an errno there is
    /// nobody to tell.
    fn count(&mut self, result: ValueId) {
        self.constant_i32(ARGC);
        self.constant_i32(NWRITTEN);
        let sizes = self
            .import("args_sizes_get")
            .expect("a count imports args_sizes_get");
        self.call(sizes);
        self.body.byte(DROP);
        self.constant_i32(ARGC);
        self.access(Width::Word, Offset::Bytes(0), I32_LOAD8_U, I32_LOAD);
        self.set(result);
    }

    fn access(&mut self, width: Width, offset: Offset, byte: u8, word: u8) {
        let bytes = match offset {
            Offset::Bytes(bytes) => bytes,
            Offset::Words(words) => words * WORD,
        };
        let (opcode, align) = match width {
            Width::Byte => (byte, 0),
            Width::Word => (word, 2),
        };
        self.body.byte(opcode);
        self.body.uleb(align);
        self.body
            .uleb(u32::try_from(bytes).expect("a non-negative offset in range"));
    }

    fn platform_named(
        &mut self,
        name: &str,
        args: &[ValueId],
        results: &[ValueId],
        position: Position,
    ) {
        match name {
            "write!" | "write_error!" => {
                let index = self.written;
                self.written += 1;
                let iovec = IOVECS + IOVEC_LEN * len32(index);

                // Both known, so the vector ships as initialised data; if
                // not, the call fills it in for itself.
                if let (Some(base), Some(length)) = (self.constant(args[0]), self.constant(args[1]))
                {
                    self.iovecs[index] = Some((base, length));
                } else {
                    self.store(iovec, args[0]);
                    self.store(iovec + 4, args[1]);
                }

                self.constant_i32(if name == "write!" { STDOUT } else { STDERR });
                self.constant_i32(iovec.cast_signed());
                self.constant_i32(1);
                self.constant_i32(NWRITTEN);
                let fd_write = self.import("fd_write").expect("a write imports fd_write");
                self.call(fd_write);
                self.body.byte(DROP); // The errno, which there is nobody to tell.
            }
            "exit!" => self.leave(args[0], position),
            "read_byte!" => self.read_byte(results[0]),
            // Handed straight back: nothing is asked of the outside, and
            // all this says is that nothing worked the value out.
            "grow" => {
                self.push(args[0]);
                self.constant_i32((1 << PAGE_BITS) - 1);
                self.body.byte(I32_ADD);
                self.constant_i32(PAGE_BITS);
                self.body.byte(I32_SHR_U);
                self.body.byte(MEMORY_GROW);
                self.body.uleb(0);
                self.constant_i32(PAGE_BITS);
                self.body.byte(I32_SHL);
                self.set(results[0]);
            }
            other => panic!("`{other}` is not one this answers for, which `accepts` says first"),
        }
    }

    /// Return zero at EOF or on a host error, and otherwise the byte plus
    /// one. The offset preserves all 256 byte values in one scalar result.
    fn read_byte(&mut self, result: ValueId) {
        let read = self.read.expect("a byte read reserves its scratch");
        self.constant_i32(STDIN);
        self.constant_i32(read.iovec.cast_signed());
        self.constant_i32(1);
        self.constant_i32(NWRITTEN);
        let fd_read = self.import("fd_read").expect("a byte read imports fd_read");
        self.call(fd_read);

        self.constant_i32(0);
        self.body.byte(I32_EQ); // errno == 0
        self.body.byte(IF);
        self.body.byte(I32); // one i32 result
        self.open();

        self.constant_i32(NWRITTEN);
        self.access(Width::Word, Offset::Bytes(0), I32_LOAD8_U, I32_LOAD);
        self.constant_i32(1);
        self.body.byte(I32_EQ);
        self.body.byte(IF);
        self.body.byte(I32); // one i32 result
        self.open();
        self.constant_i32(read.byte.cast_signed());
        self.access(Width::Byte, Offset::Bytes(0), I32_LOAD8_U, I32_LOAD);
        self.constant_i32(1);
        self.body.byte(I32_ADD);
        self.body.byte(ELSE);
        self.constant_i32(0);
        self.close();

        self.body.byte(ELSE);
        self.constant_i32(0);
        self.close();
        self.set(result);
    }

    /// Hand `sources` over as `destinations`. Every source is pushed before
    /// any destination is set, so wasm's operand stack does the swapping.
    fn transfer(&mut self, sources: &[ValueId], destinations: &[ValueId]) {
        for &source in sources {
            self.push(source);
        }
        for &destination in destinations.iter().rev() {
            self.set(destination);
        }
    }

    fn push(&mut self, value: ValueId) {
        match self.plan.source[value.index()] {
            Source::Const(value) => {
                let narrow = u32::try_from(value).expect("a word this target can hold");
                self.constant_i32(narrow.cast_signed());
            }
            Source::Addr(data) => {
                let address = self.address(data);
                self.constant_i32(address.cast_signed());
            }
            Source::Local(index) => {
                self.body.byte(LOCAL_GET);
                self.body.uleb(index);
            }
        }
    }

    fn set(&mut self, value: ValueId) {
        let Source::Local(index) = self.plan.source[value.index()] else {
            panic!("a computed value needs a local");
        };
        self.body.byte(LOCAL_SET);
        self.body.uleb(index);
    }

    fn store(&mut self, address: u32, value: ValueId) {
        self.constant_i32(address.cast_signed());
        self.push(value);
        self.body.byte(I32_STORE);
        self.body.uleb(2); // Four-byte alignment, as a power of two.
        self.body.uleb(0);
    }

    fn constant(&self, value: ValueId) -> Option<u32> {
        match self.plan.source[value.index()] {
            Source::Const(value) => {
                Some(u32::try_from(value).expect("a word this target can hold"))
            }
            Source::Addr(data) => Some(self.address(data)),
            Source::Local(_) => None,
        }
    }

    /// Where a datum sits in linear memory. Both regions are writable here,
    /// so they differ only in where they begin.
    fn address(&self, data: DataId) -> u32 {
        let span = self.program.datum(data);
        let base = match span.origin {
            Origin::Data => self.data_start,
            Origin::Globals => self.data_start + len32(self.program.data().len()),
        };
        base + span.start
    }

    fn constant_i32(&mut self, value: i32) {
        self.body.byte(I32_CONST);
        self.body.sleb(value);
    }

    fn import(&self, name: &str) -> Option<u32> {
        let index = self.imports.iter().position(|&each| each == name)?;
        Some(len32(index))
    }

    fn call(&mut self, function: u32) {
        self.body.byte(CALL);
        self.body.uleb(function);
    }

    /// `br` counts labels outwards from the innermost, which is why the
    /// depth a label was opened at is what gets remembered.
    fn branch(&mut self, label: usize) {
        self.body.byte(BR);
        self.body.uleb(len32(self.depth - 1 - label));
    }

    const fn open(&mut self) {
        self.depth += 1;
    }

    fn close(&mut self) {
        self.depth -= 1;
        self.body.byte(END);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use faun_core::ir::Class;

    fn entry(build: impl FnOnce(&mut faun_core::ir::Builder)) -> Program {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| build(b));
        faun_core::ir::validate(&program).unwrap();
        program
    }

    #[test]
    fn hello_world_needs_no_exit_call() {
        let code = lower(&faun_core::programs::hello_world());
        assert_eq!(code.imports, ["fd_write"], "no proc_exit");
        assert_eq!(code.bodies[0].locals, 0, "constants need no locals");

        #[rustfmt::skip]
        let expected: &[u8] = &[
            0x41, 0x01, // i32.const 1   (stdout)
            0x41, 0x08, // i32.const 8   (the one ciovec)
            0x41, 0x01, // i32.const 1   (vector count)
            0x41, 0x00, // i32.const 0   (where the byte count goes)
            0x10, 0x00, // call 0        (fd_write)
            0x1A,       // drop
        ];
        assert_eq!(code.bodies[0].code, expected);
    }

    #[test]
    fn the_vector_points_at_the_message() {
        let code = lower(&faun_core::programs::hello_world());
        assert_eq!(code.data[0].offset, IOVECS);
        // Base 16 is the first byte past the vector itself, length 14.
        assert_eq!(code.data[0].bytes, [16, 0, 0, 0, 14, 0, 0, 0]);
        assert_eq!(code.data[1].bytes, b"Hello, World!\n");
    }

    #[test]
    fn a_nonzero_status_has_to_be_called_in() {
        let program = entry(|b| {
            let status = b.constant(Class::Word, 3);
            b.ret(&[status]);
        });
        let code = lower(&program);
        assert_eq!(code.imports, ["proc_exit"]);
        // The only import, so `proc_exit` is function zero.
        assert_eq!(code.bodies[0].code, [0x41, 0x03, 0x10, 0x00]);
    }

    /// The whole of a program that leaves with nought: no call, nothing to
    /// import, and nothing in the body but the `end` a body ends with.
    #[test]
    fn leaving_with_nought_is_the_end_of_the_entry() {
        let (mut program, main) = Program::new("main");
        let exit = faun_core::platform::Routines::builtin().declare(&mut program, "exit!");
        program.define(main, |b, _| {
            let status = b.constant(Class::Word, 0);
            b.call(exit, &[status]);
        });

        let code = lower(&program);
        assert!(code.imports.is_empty(), "{:?}", code.imports);
        assert_eq!(code.bodies[0].code, []);
    }

    /// The same exit where returning is not the end of the program: from a
    /// name the entry calls, it has to be the routine.
    #[test]
    fn leaving_with_nought_from_elsewhere_is_a_call() {
        let (mut program, main) = Program::new("main");
        let exit = faun_core::platform::Routines::builtin().declare(&mut program, "exit!");
        let leave = program.declare_never("leave", &[]);
        program.define(leave, |b, _| {
            let status = b.constant(Class::Word, 0);
            b.call(exit, &[status]);
        });
        program.define(main, |b, _| {
            b.call(leave, &[]);
        });
        faun_core::ir::validate(&program).unwrap();

        let code = lower(&program);
        assert_eq!(code.imports, ["proc_exit"]);
    }

    /// Structured control flow goes out as it came in: a `loop` inside a
    /// `block`, with `br 0` going round and `br 1` leaving.
    #[test]
    fn a_loop_is_a_loop() {
        let program = entry(|b| {
            let start = b.constant(Class::Word, 1);
            b.loop_(&[start], &[], |b, params| {
                let zero = b.constant(Class::Word, 0);
                let done = b.compare(Relation::Equal, params[0], zero);
                b.if_(
                    done,
                    &[],
                    |b| b.break_(&[]),
                    |b| {
                        let one = b.constant(Class::Word, 1);
                        let next = b.binary(Binary::Sub, params[0], one);
                        b.continue_(&[next]);
                    },
                );
            });
            let zero = b.constant(Class::Word, 0);
            b.ret(&[zero]);
        });

        let body = lower(&program).bodies[0].code.clone();
        assert!(body.starts_with(&[
            0x41, 0x01, // i32.const 1
            0x21, 0x00, // local.set 0   (the loop parameter)
            0x02, 0x40, // block
            0x03, 0x40, // loop
        ]));
        // Both branches sit inside the `if`, so label 0 is the if itself:
        // `br 1` goes round the loop and `br 2` leaves the block.
        assert!(body.windows(2).any(|w| w == [0x0C, 0x01]), "continue");
        assert!(body.windows(2).any(|w| w == [0x0C, 0x02]), "break");
    }
}
