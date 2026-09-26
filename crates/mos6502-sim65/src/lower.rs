//! Lowering the IR to 6502 code.
//!
//! Every value that is not a constant or an address lives in a two-byte
//! frame slot, reached as `(FP),Y`, so a frame holds at most 128 of them.
//! Two-operand forms read their operands into the scratch pairs and work
//! there, which is unhurried and obviously correct.

use super::asm::{Assembler, Cc, Half, Held};
use super::{
    ARG_COUNT, ARGC, ARGS, CSP, CSTACK_TOP, Code, FP, FRAMES_TOP, HEAP, HOME_COUNT, HOMES,
    HOOK_ARGS, HOOK_CLOSE, HOOK_EXIT, HOOK_OPEN, HOOK_READ, HOOK_WRITE, LOAD, PTR, R0, T0, T1,
};
use crate::WORD_BITS;
use faun_core::ir::{
    Binary, Class, DataId, Direction, Exit, FunctionId, Offset, Op, Origin, Program, RegionId,
    Relation, Terminator, ValueId, Width,
};

/// A word here is the width of an address.
const WORD: i32 = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum FrameAction {
    Enter,
    Leave,
}

/// Where a function keeps what it holds.
#[derive(Clone, Default)]
struct Plan {
    frame: u8,
    homes: Vec<u8>,
}

/// The first of `places`, or a new one while fewer than `most` are taken,
/// that holds nothing wanted while `span` is, now holding that too.
fn free(places: &mut Vec<Vec<(usize, usize)>>, span: (usize, usize), most: usize) -> Option<usize> {
    let apart = |&(first, last): &(usize, usize)| last < span.0 || span.1 < first;
    // Something never touched is wanted nowhere, and shares with nothing.
    let at = places
        .iter()
        .position(|held| span.0 <= span.1 && held.iter().all(apart))
        .or_else(|| {
            (places.len() < most).then(|| {
                places.push(Vec::new());
                places.len() - 1
            })
        })?;
    places[at].push(span);
    Some(at)
}

/// Where each value is first and last touched in emission order, and where
/// the calls are. A value whose span holds a call is live across it.
#[derive(Default)]
struct Spans {
    first: Vec<usize>,
    last: Vec<usize>,
    calls: Vec<usize>,
}

impl Spans {
    fn touch(&mut self, value: ValueId, at: usize) {
        self.first[value.index()] = self.first[value.index()].min(at);
        self.last[value.index()] = self.last[value.index()].max(at);
    }

    /// Whether a call happens while the value still matters. A call's own
    /// argument dies at it and its result is born there, so neither counts.
    fn crosses_call(&self, value: ValueId) -> bool {
        let (first, last) = (self.first[value.index()], self.last[value.index()]);
        first <= last && self.calls.iter().any(|at| first < *at && *at < last)
    }

    /// Everything touched inside a loop stays live for all of it, since the
    /// body runs again.
    fn widen(&mut self, from: usize, to: usize) {
        for value in 0..self.first.len() {
            let (first, last) = (self.first[value], self.last[value]);
            if first <= last && first <= to && last >= from {
                self.first[value] = first.min(from);
                self.last[value] = last.max(to);
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Source {
    Const(u64),
    Addr(DataId),
    /// A zero-page pair. Only a value no call outlives gets one, so a
    /// callee taking the same pair can never be noticed.
    Home(u8),
    Slot(u8),
}

/// Where an instruction can read a value without copying it anywhere first.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Operand {
    Imm(u16),
    /// A zero-page place, and whether a second byte of it is worth reading.
    /// What a class of eight bits or fewer can be has a high half of
    /// nought, so nothing keeps one and nothing reads one back.
    Zp {
        at: u8,
        wide: bool,
    },
}

impl Operand {
    /// A scratch pair, which holds two bytes whatever is put in it.
    const fn pair(at: u8) -> Self {
        Self::Zp { at, wide: true }
    }

    /// The byte at `index`, low first.
    const fn byte(self, index: u8) -> Held {
        match self {
            Self::Imm(value) => {
                let [low, high] = value.to_le_bytes();
                Held::Imm(if index == 0 { low } else { high })
            }
            Self::Zp { at, wide } => {
                if index == 0 {
                    Held::Zero(at)
                } else if wide {
                    Held::Zero(at + 1)
                } else {
                    Held::Imm(0)
                }
            }
        }
    }
}

/// Whether a byte is the number nought, known before the program runs.
///
/// Nothing unsigned is under nought, so a branch saying something is under
/// this one never runs and is not written.
const fn nought(byte: Held) -> bool {
    matches!(byte, Held::Imm(0))
}

/// Whether `value` is read anywhere in `region`, nested regions included.
fn region_reads(program: &Program, region: RegionId, value: ValueId) -> bool {
    program.outgoing(region).contains(&value)
        || program
            .ops(region)
            .iter()
            .any(|op| op_reads(program, op, value))
}

/// Whether a region works `value` out itself, rather than reading one from
/// somewhere it can see.
fn written_in(program: &Program, region: RegionId, value: ValueId) -> bool {
    program
        .walk(region)
        .any(|(_, results)| results.contains(&value))
}

fn op_reads(program: &Program, op: &Op, value: ValueId) -> bool {
    let mut found = false;
    for_each_operand(op, program, |read| found |= read == value);
    found
        || match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } => {
                region_reads(program, then_region, value)
                    || region_reads(program, else_region, value)
            }
            Op::Loop { body, .. } => region_reads(program, body, value),
            _ => false,
        }
}

/// How many `continue`s a loop body has. A nested loop's own belongs to it,
/// so the walk stops at one.
fn continues(program: &Program, region: RegionId) -> usize {
    let own = usize::from(
        program
            .region(region)
            .terminator
            .is_some_and(|t| t.exit == Exit::Continue),
    );
    own + program
        .ops(region)
        .iter()
        .map(|op| match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } => continues(program, then_region) + continues(program, else_region),
            _ => 0,
        })
        .sum::<usize>()
}

/// The chain of regions from a loop body down to its `continue`, each with
/// the index of the instruction descended into. The innermost index is past
/// the last instruction, since the `continue` is that region's terminator.
fn path_to_continue(
    program: &Program,
    region: RegionId,
    path: &mut Vec<(RegionId, usize)>,
) -> bool {
    let ops = program.ops(region);
    if program
        .region(region)
        .terminator
        .is_some_and(|t| t.exit == Exit::Continue)
    {
        path.push((region, ops.len()));
        return true;
    }
    for (index, op) in ops.iter().enumerate() {
        let Op::If {
            then_region,
            else_region,
            ..
        } = *op
        else {
            continue;
        };
        for child in [then_region, else_region] {
            path.push((region, index));
            if path_to_continue(program, child, path) {
                return true;
            }
            path.pop();
        }
    }
    false
}

/// Every value an operation reads, nested regions excluded.
/// How many bits of each value anything reads.
///
/// A value may be able to be more than anything ever looks at: a sum
/// narrowed as soon as it is worked out is read at the width it is narrowed
/// to, and whatever it carried above that was worked out for nobody. Asking
/// what is read rather than what can be there is what keeps a machine from
/// carrying the second.
fn reads(program: &Program) -> Vec<u16> {
    let mut needs = vec![0u16; program.values_count()];
    let mut regions = Vec::new();
    for function in program.functions() {
        let Some(body) = function.body() else {
            continue;
        };
        regions.push(body);
        for (op, results) in program.walk_within(body) {
            if let Op::If {
                then_region,
                else_region,
                ..
            } = *op
            {
                regions.extend([then_region, else_region]);
            }
            if let Op::Loop { body, .. } = *op {
                regions.push(body);
            }
            // The simulator's exit hook reads only its one-byte status.
            if let Some(value) = exit_status(program, op) {
                needs[value.index()] = needs[value.index()].max(8);
                continue;
            }
            // A conversion looks at the bits it keeps and no more.
            if let Op::Convert { value } = *op {
                let kept = bits(program.class(results[0])).min(bits(program.class(value)));
                let at = value.index();
                needs[at] = needs[at].max(kept);
                continue;
            }
            for_each_operand(op, program, |value| {
                let at = value.index();
                needs[at] = needs[at].max(bits(program.class(value)));
            });
        }
    }
    mark_region_outputs(program, &regions, &mut needs);
    needs
}

/// What a region carries out of it is read whole wherever it lands.
fn mark_region_outputs(program: &Program, regions: &[RegionId], needs: &mut [u16]) {
    for &region in regions {
        for &value in program.outgoing(region) {
            needs[value.index()] = bits(program.class(value));
        }
    }
}

fn exit_status(program: &Program, op: &Op) -> Option<ValueId> {
    let Op::Call { function, args } = *op else {
        return None;
    };
    program
        .function(function)
        .external()
        .is_some_and(|symbol| program.name(symbol) == "exit!")
        .then(|| program.values(args).first().copied())
        .flatten()
}

#[expect(clippy::too_many_lines, reason = "one exhaustive arm per operation")]
fn for_each_operand(op: &Op, program: &Program, mut each: impl FnMut(ValueId)) {
    match op {
        Op::Constant { .. }
        | Op::NaturalConstant(_)
        | Op::AddressOf(_)
        | Op::BufferEmpty { .. }
        | Op::BufferKnown { .. } => {}
        Op::Cell { fields, .. }
        | Op::BufferPush {
            operands: fields, ..
        }
        | Op::BufferPrepend {
            operands: fields, ..
        }
        | Op::BufferExtend {
            operands: fields, ..
        } => {
            program.values(*fields).iter().copied().for_each(&mut each);
        }
        Op::CellTag { cell: value }
        | Op::CellField { cell: value, .. }
        | Op::BufferRoom { count: value, .. }
        | Op::Keep { value }
        | Op::Load { address: value, .. }
        | Op::Convert { value, .. }
        | Op::Shift { value, .. } => each(*value),
        Op::Binary { left, right, .. }
        | Op::Compare { left, right, .. }
        | Op::BufferField {
            buffer: left,
            start: right,
            ..
        }
        | Op::BufferAt {
            buffer: left,
            start: right,
            ..
        }
        | Op::Store {
            address: left,
            value: right,
            ..
        } => {
            each(*left);
            each(*right);
        }
        Op::Call { args, .. } | Op::Float { operands: args, .. } => {
            program.values(*args).iter().copied().for_each(each);
        }
        Op::If { condition, .. } => each(*condition),
        Op::Loop { initial, .. } => program.values(*initial).iter().copied().for_each(each),
    }
}

/// What a round may learn and never unlearn: that the heap has to start
/// further up. It is not taken back, and an address is two bytes however
/// high it is, so a heap further out never makes the code that names it
/// longer. Every program here settles in two, one to lay the image out and
/// one to confirm it. Reaching this many means a round undid what an
/// earlier one settled.
///
/// How far a branch reaches settles inside the assembling, where the steps
/// can be measured without writing any of them out.
const ROUNDS: usize = 32;

/// # Panics
///
/// If the layout does not settle, which is this target disagreeing with
/// itself rather than anything a program did.
pub(crate) fn lower(program: &Program) -> Code {
    let mut heap = LOAD;
    // Nothing here knows yet whether the program calls anything, and one
    // that calls nothing needs no stack to call with. The first round asks
    // the assembling, and dropping the two steps that set it can only take
    // a call away, never add one, so the question is asked once.
    let mut stack = true;
    for _ in 0..ROUNDS {
        let code = assemble(program, heap, stack);
        if stack && !code.pushes {
            stack = false;
            continue;
        }
        let end = code.reset + u16::try_from(code.bytes.len()).expect("an image within 64 KiB");
        if end <= heap {
            return code;
        }
        heap = end;
    }
    panic!("the layout did not settle in {ROUNDS} rounds")
}

/// Run the actual home/slot allocation, without emitting instructions. A
/// frame's byte size must fit u8: at most 127 spilled pairs, not 128.
/// This does not prove recursion stack depth or image/stack separation.
pub(crate) fn check_frames(program: &Program) -> Result<(), String> {
    let mut state = Lowering::new(program, Assembler::new(0), 0);
    state.needs = reads(program);
    for function in program.functions() {
        let Some(body) = function.body() else {
            continue;
        };
        state.plan(body).map_err(|error| {
            format!(
                "mos6502-sim65 function `{}`: {error}",
                program.name(function.name)
            )
        })?;
    }
    Ok(())
}

fn assemble(program: &Program, heap: u16, stack: bool) -> Code {
    // The data sits at the front of the image and the code after it, so the
    // code's own addresses depend on how much data there is.
    let data = LOAD;
    let blob = program.data().len() + program.globals().len();
    let origin = data + u16::try_from(blob).expect("data within 64 KiB");

    let mut state = Lowering::new(program, Assembler::new(origin), data);
    state.starts = (0..program.functions().len())
        .map(|_| state.asm.label())
        .collect();
    // The simulator is told where the stack its hooks take arguments on is,
    // and reads it without any instruction here saying so.
    state.asm.read_outside(CSP);
    state.asm.read_outside(CSP + 1);
    state.needs = reads(program);
    state.plans = program
        .functions()
        .iter()
        .map(|function| {
            function
                .body()
                .map(|body| state.plan(body).expect("accepted frame size"))
        })
        .collect();
    state.reset(heap, stack);
    // The entry goes first, so the reset routine runs into it rather than
    // jumping to it. Everything else follows in the order it was declared.
    let entry = program.entry();
    let rest = (0..program.functions().len())
        .map(FunctionId::at)
        .filter(|id| id.index() != entry.index());
    let fallen = stack && !program.comes_back(entry);
    for id in std::iter::once(entry).chain(rest) {
        state.function(id, fallen && id.index() == entry.index());
    }
    state.emit_pool();

    Code {
        pushes: state.asm.pushes(),
        bytes: state.asm.finish(),
        reset: origin,
    }
}

struct Lowering<'a> {
    program: &'a Program,
    asm: Assembler,
    data: u16,
    source: Vec<Source>,
    frame: u8,
    /// The zero-page pairs this function keeps values in.
    homes: Vec<u8>,
    /// Every function's plan, worked out before any code is emitted.
    plans: Vec<Option<Plan>>,
    /// How many bits of each value anything reads.
    needs: Vec<u16>,
    /// Argument blocks the target lays down itself, one per distinct pair of
    /// constant arguments, emitted after the code.
    pool: Vec<(super::asm::Label, [u16; 2])>,
    /// Intermediates answered directly by their sole consumer, by value index.
    fused: std::collections::HashSet<usize>,
    /// A byte sum consumed only by a one-place downward shift. The sum's
    /// ninth bit can remain in carry until the shift reads it.
    halved_sums: Vec<Option<(ValueId, ValueId)>>,
    /// A comparison waiting for the `if` that reads its flags.
    pending: Option<(ValueId, Relation, ValueId, ValueId)>,
    starts: Vec<super::asm::Label>,
    loops: Vec<(
        Vec<ValueId>,
        super::asm::Label,
        Vec<ValueId>,
        super::asm::Label,
    )>,
    /// An absent label means the arm falls into its continuation.
    ifs: Vec<(Vec<ValueId>, Option<super::asm::Label>)>,
    /// Path-local upper bounds established by enclosing comparisons.
    bounds: Vec<(ValueId, u64)>,
}

impl<'a> Lowering<'a> {
    fn new(program: &'a Program, asm: Assembler, data: u16) -> Self {
        Self {
            program,
            asm,
            data,
            source: vec![Source::Slot(0); program.values_count()],
            frame: 0,
            homes: Vec::new(),
            plans: Vec::new(),
            needs: Vec::new(),
            pool: Vec::new(),
            fused: std::collections::HashSet::new(),
            halved_sums: vec![None; program.values_count()],
            pending: None,
            starts: Vec::new(),
            loops: Vec::new(),
            ifs: Vec::new(),
            bounds: Vec::new(),
        }
    }
}

impl Lowering<'_> {
    /// The hardware stack where one is needed, the two software stacks, the
    /// heap past the end of the image, then the entry; its result is the
    /// program's status.
    fn reset(&mut self, heap: u16, stack: bool) {
        // Where the simulator leaves the stack pointer is not something a
        // program may read, and there is no way to set it but through `X`.
        // One that never calls anything never pushes, and then what it says
        // about a stack nothing uses is nothing.
        if stack {
            self.asm.ldx_imm(0xFF);
            self.asm.txs();
        }
        if self.plans.iter().flatten().any(|plan| plan.frame > 0) {
            self.set_pair(FP, FRAMES_TOP);
        }
        if self.program.reaches("grow") {
            self.set_pair(HEAP, heap);
        }
        self.take_arguments(heap);

        // An entry that leaves through the exit hook itself never comes back
        // here, so there is nothing to write for after it: no result to read
        // out of `R0`, and no second way out. It is written next, so running
        // off the end of this is entering it.
        if !self.program.comes_back(self.program.entry()) {
            return;
        }
        let entry = self.starts[self.program.entry().index()];
        self.asm.jsr(entry);
        self.asm.lda_zp(R0);
        self.asm.jmp_abs(HOOK_EXIT);
    }

    /// The count and the arguments, where the entry reads them.
    fn take_arguments(&mut self, heap: u16) {
        // The hook is handed where to write the arguments themselves, in `A`
        // and `X`, and reads where the argument stack is from the pair the
        // image header named. Nothing has asked for memory yet, so it is
        // told the heap. What is wanted back is the count, which it leaves
        // in `A` and `X`.
        if self.entry_argc().is_some() {
            let [low, high] = heap.to_le_bytes();
            // `X` is free until the hook's argument goes in it, and holds
            // what the stack pointer was set from, so the pair is written
            // through it: a neighbour of a number `X` holds is a step away.
            let [stack_low, stack_high] = (CSTACK_TOP - 2).to_le_bytes();
            self.asm.ldx_imm(stack_low);
            self.asm.stx_zp(CSP);
            self.asm.ldx_imm(stack_high);
            self.asm.stx_zp(CSP + 1);
            self.asm.lda_imm(low);
            self.asm.ldx_imm(high);
            self.jsr_hook(HOOK_ARGS);
            self.asm.sta_zp(ARGC);
            // The high half only where something reads more of the count
            // than its low byte.
            if self.counts_wide() {
                self.asm.stx_zp(ARGC + 1);
            }
            // The simulator wrote the arguments on its C stack, and where
            // their addresses lie at the place it was handed: that is the
            // entry's second argument.
            if self.entry_argv().is_some() {
                self.set_pair(T0, heap);
                self.asm.ldy_imm(0);
                self.asm.lda_ind_y(T0);
                self.asm.sta_zp(ARGS + 2);
                self.asm.iny();
                self.asm.lda_ind_y(T0);
                self.asm.sta_zp(ARGS + 3);
            }
        }
    }

    /// Whether anything reads more of the count than its low byte.
    ///
    /// The simulator answers in two registers and the reset routine keeps
    /// what it answered, which is a byte nobody wants wherever every
    /// program that asks the count narrows it.
    fn counts_wide(&self) -> bool {
        self.entry_argc().is_some_and(|value| self.wide(value))
    }

    /// The entry's second parameter, where it asks where the arguments lie.
    fn entry_argv(&self) -> Option<ValueId> {
        let entry = self.program.entry();
        (self.program.parameter_names(entry).nth(1) == Some("argv")).then(|| {
            let body = self
                .program
                .function(entry)
                .body()
                .expect("the entry has a body");
            self.program.values(self.program.region(body).params)[1]
        })
    }

    fn entry_argc(&self) -> Option<ValueId> {
        let entry = self.program.entry();
        (self.program.parameter_names(entry).next() == Some("argc")).then(|| {
            let body = self
                .program
                .function(entry)
                .body()
                .expect("the entry has a body");
            self.program.values(self.program.region(body).params)[0]
        })
    }

    fn set_pair(&mut self, pair: u8, value: u16) {
        self.set_place(pair, value, true);
    }

    /// A known number where a place holds it, in one byte or two.
    fn set_place(&mut self, at: u8, value: u16, wide: bool) {
        let [low, high] = value.to_le_bytes();
        self.asm.carry(Held::Imm(low), at);
        if wide {
            self.asm.carry(Held::Imm(high), at + 1);
        }
    }

    /// `fallen` says the reset routine ran into this one rather than
    /// calling it, which is the one way a body is reached from a place that
    /// knows what it left in the accumulator.
    fn function(&mut self, id: FunctionId, fallen: bool) {
        let function = self.program.function(id);
        let Some(body) = function.body() else { return };
        let start = self.starts[id.index()];
        // A call may come from anywhere, knowing anything, including after
        // this is written; only running into it from the reset routine,
        // which is then the one way in, keeps what that left.
        if fallen {
            self.asm.bind(start);
        } else {
            self.asm.bind_reentered(start);
        }

        let plan = self.plans[id.index()]
            .as_ref()
            .expect("a body has a frame plan")
            .clone();
        self.frame = plan.frame;
        self.homes = plan.homes;
        let frame = self.frame;
        if frame > 0 {
            self.adjust_frame(frame, FrameAction::Enter);
        }

        // Arguments arrive in fixed pairs, so a callee takes its own copies
        // before anything it calls can overwrite them.
        let params = self.program.values(self.program.region(body).params);
        for (index, &param) in params.to_vec().iter().enumerate() {
            let pair =
                if id == self.program.entry() && self.program.parameter_name(id, index) == "argc" {
                    ARGC
                } else {
                    ARGS + 2 * u8::try_from(index).expect("a few arguments")
                };
            self.commit(param, pair);
        }
        self.region(body);
    }

    /// `FP` down by the frame, or back up again.
    fn adjust_frame(&mut self, frame: u8, action: FrameAction) {
        self.asm.lda_zp(FP);
        if action == FrameAction::Enter {
            self.asm.sec();
            self.asm.sbc_imm(frame);
        } else {
            self.asm.clc();
            self.asm.adc_imm(frame);
        }
        self.asm.sta_zp(FP);
        self.asm.lda_zp(FP + 1);
        if action == FrameAction::Enter {
            self.asm.sbc_imm(0);
        } else {
            self.asm.adc_imm(0);
        }
        self.asm.sta_zp(FP + 1);
    }

    /// Give every value the function holds a place. The most used get a
    /// zero-page pair, where an instruction can reach them in three cycles
    /// rather than the twenty a frame slot costs; the rest get slots. Use
    /// is counted per loop depth, so an inner loop outbids straight line
    /// code for the pairs.
    fn plan(&mut self, body: RegionId) -> Result<Plan, String> {
        let mut weight = vec![0u64; self.program.values_count()];
        let mut uses = vec![0u32; self.program.values_count()];
        let mut held = Vec::new();
        self.survey(body, 0, &mut weight, &mut uses, &mut held);
        // The count was read at reset and left at a pair nothing writes
        // again, so the entry's `argc` is already where it lives.
        if let Some(argc) = self.entry_argc() {
            held.retain(|&value| value != argc);
            self.source[argc.index()] = Source::Home(ARGC);
        }

        // Value numbers are unique across the program, so what one function
        // marks cannot be mistaken for another's.
        self.mark(body, &uses);
        let shared = self.share(body);

        // A fused comparison answers in the flags and a shared value lives
        // in the parameter's place, so neither needs one of its own. The
        // weight a shared value carried belongs to the parameter it joins.
        for &(value, param) in &shared {
            weight[param.index()] += weight[value.index()];
        }
        held.retain(|value| {
            !self.fused.contains(&value.index())
                && !shared.iter().any(|(shared, _)| shared == value)
        });
        held.sort_by_key(|value| (core::cmp::Reverse(weight[value.index()]), value.index()));

        // A shared value lives where its partner does, so the place has to
        // outlast both: one a call outlives makes the pair one too.
        let mut spans = self.spans(body);
        for &(value, param) in &shared {
            let (first, last) = (spans.first[value.index()], spans.last[value.index()]);
            if first <= last {
                spans.touch(param, first);
                spans.touch(param, last);
            }
        }
        let plan = self.place(&held, &spans)?;
        for (value, param) in shared {
            self.source[value.index()] = self.source[param.index()];
        }
        Ok(plan)
    }

    /// The most used values get a zero-page pair and the rest frame slots,
    /// with room after them to save the pairs, for a function that has
    /// someone to give them back to.
    fn place(&mut self, held: &[ValueId], spans: &Spans) -> Result<Plan, String> {
        let mut plan = Plan::default();
        // Each pair and slot, with the spans of what it holds: a value no
        // longer wanted leaves its place to one wanted only after.
        let mut homes: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut slots: Vec<Vec<(usize, usize)>> = Vec::new();
        for &value in held {
            let span = (spans.first[value.index()], spans.last[value.index()]);
            // A callee takes the pairs from the same place, so a value a
            // call outlives cannot hold one; the frame is out of a callee's
            // reach, and that is where such a value goes.
            // The most used take a pair each, as they come; after them,
            // one whose pair is no longer wanted may take it again.
            let home = if spans.crosses_call(value) {
                None
            } else if homes.len() < usize::from(HOME_COUNT) {
                homes.push(vec![span]);
                Some(homes.len() - 1)
            } else {
                free(&mut homes, span, 0)
            };
            if let Some(at) = home {
                let pair = HOMES + 2 * u8::try_from(at).expect("fewer pairs than a byte counts");
                if at == plan.homes.len() {
                    plan.homes.push(pair);
                }
                self.source[value.index()] = Source::Home(pair);
                continue;
            }
            let at = free(&mut slots, span, 127)
                .ok_or_else(|| "frame exceeds 254 bytes (127 spilled values)".to_owned())?;
            let slot = u8::try_from(2 * at).expect("127 slots are 254 bytes");
            plan.frame = plan.frame.max(slot + 2);
            self.source[value.index()] = Source::Slot(slot);
        }
        Ok(plan)
    }

    /// What each value is, and how much the function leans on it.
    fn survey(
        &mut self,
        region: RegionId,
        depth: u32,
        weight: &mut [u64],
        uses: &mut [u32],
        held: &mut Vec<ValueId>,
    ) {
        let program = self.program;
        let each = 1u64 << (2 * depth.min(8));
        for &param in program.values(program.region(region).params) {
            held.push(param);
            weight[param.index()] += each;
        }

        for (op, results) in program.walk(region) {
            let settled = match *op {
                Op::Constant { value, .. } => {
                    self.source[results[0].index()] = Source::Const(value);
                    true
                }
                Op::AddressOf(data) => {
                    self.source[results[0].index()] = Source::Addr(data);
                    true
                }
                _ => false,
            };
            if !settled {
                for &result in results {
                    held.push(result);
                    weight[result.index()] += each;
                }
            }
            for_each_operand(op, program, |value| {
                weight[value.index()] += each;
                uses[value.index()] += 1;
            });
        }
        for &value in program.outgoing(region) {
            weight[value.index()] += each;
            uses[value.index()] += 1;
        }

        self.survey_within(region, depth, weight, uses, held);
    }

    /// The nested regions after the run they sit in, so each stays one scan
    /// rather than a walk interleaved with recursion. A loop's body counts
    /// for more, since everything in it happens more than once.
    fn survey_within(
        &mut self,
        region: RegionId,
        depth: u32,
        weight: &mut [u64],
        uses: &mut [u32],
        held: &mut Vec<ValueId>,
    ) {
        for op in self.program.ops(region) {
            match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.survey(then_region, depth, weight, uses, held);
                    self.survey(else_region, depth, weight, uses, held);
                }
                Op::Loop { body, .. } => self.survey(body, depth + 1, weight, uses, held),
                _ => {}
            }
        }
    }

    /// Spans over the whole function, in the order it is emitted.
    fn spans(&self, body: RegionId) -> Spans {
        let count = self.program.values_count();
        let mut spans = Spans {
            first: vec![usize::MAX; count],
            last: vec![0; count],
            calls: Vec::new(),
        };
        let mut at = 0;
        self.span_region(body, &[], &mut at, &mut spans);
        spans
    }

    fn span_region(&self, region: RegionId, params: &[ValueId], at: &mut usize, spans: &mut Spans) {
        let program = self.program;
        for &param in program.values(program.region(region).params) {
            spans.touch(param, *at);
        }
        let steps: Vec<(&Op, &[ValueId])> = program.walk(region).collect();
        for index in self.order(region, params) {
            let (op, results) = steps[index];
            *at += 1;
            for &result in results {
                spans.touch(result, *at);
            }
            for_each_operand(op, program, |value| spans.touch(value, *at));
            match *op {
                Op::Call { function, .. } if program.function(function).body().is_some() => {
                    spans.calls.push(*at);
                }
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.span_region(then_region, params, at, spans);
                    self.span_region(else_region, params, at, spans);
                }
                Op::Loop { body, .. } => {
                    let from = *at;
                    let inner = program.values(program.region(body).params).to_vec();
                    self.span_region(body, &inner, at, spans);
                    spans.widen(from, *at);
                }
                _ => {}
            }
        }
        *at += 1;
        for &value in program.outgoing(region) {
            spans.touch(value, *at);
        }
    }

    /// The instructions a `continue` carries the results of, which are read
    /// nowhere else in the region and so can be computed last.
    fn deferred(&self, region: RegionId) -> Vec<usize> {
        let program = self.program;
        let Some(terminator) = program.region(region).terminator else {
            return Vec::new();
        };
        if terminator.exit != Exit::Continue {
            return Vec::new();
        }
        let carried = program.values(terminator.values);
        let ops = program.ops(region);
        program
            .walk(region)
            .enumerate()
            .filter_map(|(index, (op, results))| {
                let (Op::Binary { .. }, [value]) = (op, results) else {
                    return None;
                };
                let read_elsewhere = ops.iter().any(|op| op_reads(program, op, *value));
                (carried.contains(value) && !read_elsewhere).then_some(index)
            })
            .collect()
    }

    /// The order a region's instructions are emitted in. Among the deferred
    /// definitions, one that would overwrite a loop parameter goes after
    /// every other that still has to read it, which is what lets the
    /// parameter and its next value share a place.
    fn order(&self, region: RegionId, params: &[ValueId]) -> Vec<usize> {
        let program = self.program;
        let mut deferred = self.deferred(region);
        let ops = program.ops(region);
        let results: Vec<&[ValueId]> = program.walk(region).map(|(_, results)| results).collect();
        let carried = program.outgoing(region);

        // Which parameter the instruction at `index` would overwrite.
        let overwrites = |index: usize| -> Option<ValueId> {
            let [value] = results[index] else {
                return None;
            };
            let slot = carried.iter().position(|carried| carried == value)?;
            params.get(slot).copied()
        };
        for _ in 0..deferred.len() {
            let clash = (0..deferred.len()).find_map(|a| {
                let param = overwrites(deferred[a])?;
                let b = (a + 1..deferred.len())
                    .find(|&b| op_reads(program, &ops[deferred[b]], param))?;
                Some((a, b))
            });
            let Some((a, b)) = clash else { break };
            let moved = deferred.remove(a);
            deferred.insert(b, moved);
        }

        let mut order: Vec<usize> = (0..ops.len()).filter(|i| !deferred.contains(i)).collect();
        order.extend(deferred);
        order
    }

    /// Loop parameters whose `continue` value can simply overwrite them, so
    /// the back edge copies nothing. A pair is safe when the loop has one
    /// `continue`, the value is computed by arithmetic -- which reads both
    /// low bytes before writing the low result, and so tolerates sharing a
    /// place with its own operands -- and nothing reads the parameter
    /// between that computation and the `continue`.
    fn share(&self, region: RegionId) -> Vec<(ValueId, ValueId)> {
        let program = self.program;
        let mut out: Vec<(ValueId, ValueId)> = Vec::new();
        let mut loops = vec![region];
        while let Some(region) = loops.pop() {
            for (op, results) in program.walk(region) {
                match *op {
                    Op::If {
                        then_region,
                        else_region,
                        ..
                    } => {
                        loops.push(then_region);
                        loops.push(else_region);
                        self.share_if(results, [then_region, else_region], &mut out);
                    }
                    Op::Loop { body, .. } => {
                        loops.push(body);
                        self.share_loop(body, &mut out);
                    }
                    Op::Convert { value } => {
                        self.share_convert(region, value, results[0], &mut out);
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// An arm's answer worked out where the branch's answer lives, so that
    /// leaving the arm moves nothing.
    ///
    /// The two are never both wanted: what a branch answers is not read
    /// until the branch is over, and what an arm works out is not read once
    /// it has left. Both arms may do it, being alternatives rather than a
    /// sequence.
    fn share_if(
        &self,
        results: &[ValueId],
        arms: [RegionId; 2],
        out: &mut Vec<(ValueId, ValueId)>,
    ) {
        let program = self.program;
        for arm in arms {
            let carried = program.outgoing(arm);
            for (slot, &value) in carried.iter().enumerate() {
                let Some(&result) = results.get(slot) else {
                    continue;
                };
                if value == result
                    || matches!(
                        self.source[value.index()],
                        Source::Const(_) | Source::Addr(_)
                    )
                    || out
                        .iter()
                        .any(|(v, p)| *v == value || *v == result || *p == value)
                {
                    continue;
                }
                // Only what the arm works out itself, and only where
                // leaving is all the arm does with it. Anything else has a
                // reader this knows nothing about.
                if !written_in(program, arm, value)
                    || carried.iter().filter(|&&held| held == value).count() != 1
                    || program
                        .ops(arm)
                        .iter()
                        .any(|op| op_reads(program, op, value))
                {
                    continue;
                }
                out.push((value, result));
            }
        }
    }

    /// A conversion that takes nothing off lives where what it converts
    /// lives.
    ///
    /// Reading a value at a width it already fits is not something a machine
    /// does; it is something a program says. Where the two are in one place
    /// nothing is said at all.
    fn share_convert(
        &self,
        region: RegionId,
        value: ValueId,
        result: ValueId,
        out: &mut Vec<(ValueId, ValueId)>,
    ) {
        // Nothing taken off, and nothing wanted that the source has not
        // got: a place holding one byte is not a place a two-byte reader
        // can be pointed at, however little the value in it needs.
        if bits(self.program.class(result)) < self.stored(value)
            || (self.wide(result) && !self.wide(value))
        {
            return;
        }
        // What the region works out itself, so that nothing writes it again
        // while the answer is still wanted -- a loop's parameter is written
        // every time round.
        if !written_in(self.program, region, value)
            || !matches!(
                self.source[value.index()],
                Source::Home(_) | Source::Slot(_)
            )
            || out
                .iter()
                .any(|(v, p)| *v == value || *v == result || *p == result)
        {
            return;
        }
        out.push((result, value));
    }

    fn share_loop(&self, body: RegionId, out: &mut Vec<(ValueId, ValueId)>) {
        let program = self.program;
        if continues(program, body) != 1 {
            return;
        }
        let mut path = Vec::new();
        if !path_to_continue(program, body, &mut path) {
            return;
        }
        let (innermost, _) = *path.last().expect("a path to the continue");
        let carried = program.outgoing(innermost).to_vec();
        let params = program.values(program.region(body).params).to_vec();

        for (slot, &value) in carried.iter().enumerate() {
            let Some(&param) = params.get(slot) else {
                continue;
            };
            if value == param
                || params.contains(&value)
                || matches!(
                    self.source[value.index()],
                    Source::Const(_) | Source::Addr(_)
                )
                || out.iter().any(|(v, p)| *v == value || *p == param)
            {
                continue;
            }
            if self.overwrites_safely(&path, &params, value, param)
                && !carried
                    .iter()
                    .enumerate()
                    .any(|(other, &v)| other != slot && v == param)
            {
                out.push((value, param));
            }
        }
    }

    /// Whether computing `value` may write straight into `param`'s place:
    /// it is arithmetic, it runs on the way to the `continue`, and nothing
    /// between it and the `continue` still reads the parameter.
    fn overwrites_safely(
        &self,
        path: &[(RegionId, usize)],
        params: &[ValueId],
        value: ValueId,
        param: ValueId,
    ) -> bool {
        let program = self.program;
        // Where the value is computed, and how far down the path.
        let defined = path.iter().enumerate().find_map(|(level, &(region, _))| {
            let index = program
                .walk(region)
                .position(|(_, results)| results == [value])?;
            Some((level, index))
        });
        let Some((level, index)) = defined else {
            return false;
        };
        let (region, descended) = path[level];
        let ops = program.ops(region);
        if !matches!(ops[index], Op::Binary { .. }) {
            return false;
        }
        // Computed past the instruction the path descends into, so it never
        // runs on the way to this `continue`.
        if level + 1 < path.len() && index > descended {
            return false;
        }

        // Nothing between the computation and the `continue` may read the
        // parameter: the rest of this region in the order it is emitted, and
        // every deeper level in full.
        let order = self.order(region, params);
        let position = order.iter().position(|&at| at == index).expect("emitted");
        let upto = (descended + 1).min(ops.len());
        let after = order[position + 1..]
            .iter()
            .any(|&at| at < upto && op_reads(program, &ops[at], param));
        let deeper = path[level + 1..].iter().any(|&(region, _)| {
            program
                .ops(region)
                .iter()
                .any(|op| op_reads(program, op, param))
        });
        !after && !deeper
    }

    /// Mark adjacent producer/consumer pairs that can share machine state
    /// instead of materializing their intermediate.
    #[expect(
        clippy::too_many_lines,
        reason = "producer and consumer patterns share one ordered region scan"
    )]
    fn mark(&mut self, region: RegionId, uses: &[u32]) {
        let program = self.program;
        let ops: Vec<&Op> = program.ops(region).iter().collect();
        let results: Vec<&[ValueId]> = program.walk(region).map(|(_, results)| results).collect();
        for (index, (op, values)) in program.walk(region).enumerate() {
            let [result] = values else { continue };
            if uses[result.index()] != 1 {
                continue;
            }
            // Constants and addresses emit nothing, so one between the pair
            // cannot disturb accumulator or flags.
            let next = ops[index + 1..]
                .iter()
                .enumerate()
                .find(|(_, op)| !matches!(op, Op::Constant { .. } | Op::AddressOf(_)))
                .map(|(after, op)| (index + 1 + after, *op));
            match (op, next) {
                (Op::Compare { .. }, Some((_, Op::If { condition, .. })))
                    if condition == result =>
                {
                    self.fused.insert(result.index());
                }
                (
                    Op::Binary {
                        op: Binary::Add,
                        left,
                        right,
                    },
                    Some((
                        next,
                        Op::Shift {
                            direction: Direction::Down,
                            value,
                            by: 1,
                        },
                    )),
                ) if value == result
                    && bits(program.class(*left)) <= 8
                    && bits(program.class(*right)) <= 8
                    && bits(program.class(*result)) <= 9
                    && results[next]
                        .first()
                        .is_some_and(|shifted| self.needed(*shifted) <= 8) =>
                {
                    self.fused.insert(result.index());
                    self.halved_sums[result.index()] = Some((*left, *right));
                }
                _ => {}
            }
        }
        for op in ops {
            match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.mark(then_region, uses);
                    self.mark(else_region, uses);
                }
                Op::Loop { body, .. } => self.mark(body, uses),
                _ => {}
            }
        }
    }

    /// Read `value` into a zero-page pair, both bytes of it.
    ///
    /// A scratch pair is read at whatever width the instruction reading it
    /// works at, which is not something the value being read knows, so a
    /// value narrower than a pair is widened on the way in. Nothing else
    /// widens one: a place that holds a narrow value keeps one byte.
    fn read(&mut self, pair: u8, value: ValueId) {
        match self.source[value.index()] {
            Source::Const(word) => {
                let word = u16::try_from(word).expect("a word this target can hold");
                self.set_pair(pair, word);
            }
            Source::Addr(id) => {
                let at = self.address(id);
                self.set_pair(pair, at);
            }
            Source::Home(home) if home == pair => {}
            Source::Home(home) => {
                self.asm.carry(Held::Zero(home), pair);
                let high = if self.wide(value) {
                    Held::Zero(home + 1)
                } else {
                    Held::Imm(0)
                };
                self.asm.carry(high, pair + 1);
            }
            Source::Slot(offset) => {
                self.asm.ldy_imm(offset);
                self.asm.lda_ind_y(FP);
                self.asm.sta_zp(pair);
                if self.wide(value) {
                    self.asm.iny();
                    self.asm.lda_ind_y(FP);
                } else {
                    self.asm.lda_imm(0);
                }
                self.asm.sta_zp(pair + 1);
            }
        }
    }

    /// Whether a value wants both bytes of a place.
    ///
    /// What a class of eight bits or fewer can be fits one, and the tier
    /// above worked out what every value can be, so this is a question
    /// already answered rather than one a target decides.
    fn wide(&self, value: ValueId) -> bool {
        self.needed(value) > 8
    }

    /// How many bits of a value are actually there.
    ///
    /// A place holds whole bytes, so a value nothing reads above its eighth
    /// bit still has eight of them, and whatever the value was above those
    /// eight is in the one byte kept. Asking what is read rather than what
    /// is there is how a mask gets left out that was doing something.
    fn stored(&self, value: ValueId) -> u16 {
        let held = bits(self.program.class(value));
        if self.wide(value) { held } else { held.min(8) }
    }

    /// How many bits of a value anything reads, which is never more than it
    /// can be and is sometimes fewer.
    fn needed(&self, value: ValueId) -> u16 {
        let held = bits(self.program.class(value));
        self.needs
            .get(value.index())
            .copied()
            .map_or(held, |needs| needs.min(held))
    }

    /// The greatest this value can be along the path being emitted.
    fn upper_bound(&self, value: ValueId) -> Option<u64> {
        let declared = self
            .program
            .class(value)
            .facts()
            .and_then(|facts| facts.high);
        self.bounds
            .iter()
            .filter_map(|&(bounded, high)| (bounded == value).then_some(high))
            .fold(declared, |known, high| {
                Some(known.map_or(high, |known| known.min(high)))
            })
    }

    /// Whether taking this many low bits loses nothing on the current path.
    fn fits_on_path(&self, value: ValueId, bits: u16) -> bool {
        self.upper_bound(value).is_some_and(|high| {
            bits >= 64 || (bits == 0 && high == 0) || (bits > 0 && high < (1u64 << bits))
        })
    }

    /// Emit a region under one bound established by the branch entering it.
    fn region_below(&mut self, region: RegionId, bound: Option<(ValueId, u64)>) {
        let depth = self.bounds.len();
        self.bounds.extend(bound);
        self.region(region);
        self.bounds.truncate(depth);
    }

    /// `value` where an instruction can read it, copied into `scratch` only
    /// when it lives in the frame.
    fn operand(&mut self, value: ValueId, scratch: u8) -> Operand {
        match self.source[value.index()] {
            Source::Const(word) => {
                Operand::Imm(u16::try_from(word).expect("a word this target can hold"))
            }
            Source::Addr(id) => Operand::Imm(self.address(id)),
            Source::Home(home) => Operand::Zp {
                at: home,
                wide: self.wide(value),
            },
            Source::Slot(_) => {
                self.read(scratch, value);
                Operand::pair(scratch)
            }
        }
    }

    /// Where a result is computed: its own pair, or the scratch it will be
    /// written out of.
    fn dest(&self, value: ValueId) -> u8 {
        match self.source[value.index()] {
            Source::Home(home) => home,
            _ => T0,
        }
    }

    /// Where a datum sits. The image is loaded into RAM, so both regions
    /// are writable and they differ only in where they begin.
    fn address(&self, data: DataId) -> u16 {
        let span = self.program.datum(data);
        let base = match span.origin {
            Origin::Data => self.data,
            Origin::Globals => {
                self.data + u16::try_from(self.program.data().len()).expect("in range")
            }
        };
        base + u16::try_from(span.start).expect("in range")
    }

    /// A pair holding `value`'s result reaches wherever the value lives.
    ///
    /// Only as much of it as the value can be: a place holding a value of
    /// eight bits or fewer keeps one byte, and whatever the pair had above
    /// it was nought and is not worth writing down.
    fn commit(&mut self, value: ValueId, pair: u8) {
        self.put(value, Operand::pair(pair));
    }

    /// Write `from` wherever `value` lives, a byte at a time, so that a
    /// literal or a one-byte place needs no pair to pass through.
    fn put(&mut self, value: ValueId, from: Operand) {
        let wide = self.wide(value);
        match self.source[value.index()] {
            Source::Home(home) if matches!(from, Operand::Zp { at, .. } if at == home) => {}
            Source::Home(home) => {
                self.asm.carry(from.byte(0), home);
                if wide {
                    self.asm.carry(from.byte(1), home + 1);
                }
            }
            Source::Slot(offset) => {
                self.asm.ldy_imm(offset);
                self.load(from.byte(0));
                self.asm.sta_ind_y(FP);
                if wide {
                    self.asm.iny();
                    self.load(from.byte(1));
                    self.asm.sta_ind_y(FP);
                }
            }
            Source::Const(_) | Source::Addr(_) => panic!("a computed value needs a place"),
        }
    }

    /// Move bytes through sim65's `write(fd, buffer, count)` or
    /// `read(fd, buffer, count)` hook: the first two through `CSP`, the count
    /// in A and X, and what it answers left in A and X.
    fn move_bytes(&mut self, (fd, buffer, count): (Operand, ValueId, ValueId), hook: u16) {
        let at = self.operand(buffer, T1);
        let count = self.operand(count, T0);
        if let (Some(at), Operand::Imm(fd)) = (self.constant(buffer), fd) {
            let block = self.intern([at, fd]);
            self.asm.lda_imm_half(block, Half::Low);
            self.asm.sta_zp(CSP);
            self.asm.lda_imm_half(block, Half::High);
            self.asm.sta_zp(CSP + 1);
        } else {
            self.build_arguments(&[at, fd]);
        }
        match count.byte(1) {
            Held::Imm(high) => self.asm.ldx_imm(high),
            Held::Zero(at) => self.asm.ldx_zp(at),
        }
        self.load(count.byte(0));
        self.jsr_hook(hook);
    }

    /// Move bytes to or from what a descriptor names, and answer how many
    /// moved, or the hook's `-1`, which is a word that far short of the
    /// top: an error, the only one it says.
    fn stream(&mut self, args: &[ValueId], hook: u16, result: ValueId) {
        let fd = self.operand(args[0], PTR);
        self.move_bytes((fd, args[1], args[2]), hook);
        self.answered(result);
    }

    /// Open a name, ended by a nought byte, as cc65's `open` does: the
    /// name, the flags and who may read and write what it makes, on the C
    /// stack, and how many bytes of them in Y, since the last is optional.
    /// The descriptor, or `-1`.
    fn open_at(&mut self, args: &[ValueId], result: ValueId) {
        let name = self.operand(args[0], T1);
        let flags = self.operand(args[2], T0);
        let made = self.operand(args[3], PTR);
        self.build_arguments(&[made, flags, name]);
        self.asm.ldy_imm(6);
        self.jsr_hook(HOOK_OPEN);
        self.answered(result);
    }

    /// Give up a descriptor, handed in A and X: nought, or `-1`.
    fn close_fd(&mut self, args: &[ValueId], result: ValueId) {
        let fd = self.operand(args[0], T0);
        match fd.byte(1) {
            Held::Imm(high) => self.asm.ldx_imm(high),
            Held::Zero(at) => self.asm.ldx_zp(at),
        }
        self.load(fd.byte(0));
        self.jsr_hook(HOOK_CLOSE);
        self.answered(result);
    }

    /// What a hook left in A and X, as `result`.
    fn answered(&mut self, result: ValueId) {
        self.asm.sta_zp(T0);
        self.asm.stx_zp(T0 + 1);
        self.commit(result, T0);
    }

    /// Read one byte through sim65's `read(0, buffer, 1)` hook. Its result
    /// count is at most one, so a low-byte comparison distinguishes success,
    /// EOF, and the hook's `-1` error result.
    fn read_byte(&mut self, result: ValueId) {
        let block = self.intern([u16::from(T0), 0]);
        self.asm.lda_imm_half(block, Half::Low);
        self.asm.sta_zp(CSP);
        self.asm.lda_imm_half(block, Half::High);
        self.asm.sta_zp(CSP + 1);
        self.asm.lda_imm(1);
        self.asm.ldx_imm(0);
        self.jsr_hook(HOOK_READ);

        let eof = self.asm.label();
        let done = self.asm.label();
        self.asm.cmp_imm(1);
        self.asm.branch(Cc::NotEqual, eof);
        self.asm.lda_zp(T0);
        self.asm.clc();
        self.asm.adc_imm(1);
        self.asm.sta_zp(T0);
        self.asm.lda_imm(0);
        self.asm.adc_imm(0);
        self.asm.sta_zp(T0 + 1);
        self.asm.jmp(done);

        self.asm.bind(eof);
        self.set_pair(T0, 0);
        self.asm.bind(done);
        self.commit(result, T0);
    }

    /// Words a hook pops, written into the block below the C stack top,
    /// the first where the C stack pointer is left.
    fn build_arguments(&mut self, words: &[Operand]) {
        let bytes = u16::try_from(2 * words.len()).expect("a few words");
        self.set_pair(CSP, CSTACK_TOP - bytes);
        self.asm.ldy_imm(0);
        for (at, word) in words.iter().enumerate() {
            if at > 0 {
                self.asm.iny();
            }
            self.load(word.byte(0));
            self.asm.sta_ind_y(CSP);
            self.asm.iny();
            self.load(word.byte(1));
            self.asm.sta_ind_y(CSP);
        }
    }

    /// The label of a block holding `words`, added to the pool if it is new.
    fn intern(&mut self, words: [u16; 2]) -> super::asm::Label {
        if let Some((label, _)) = self.pool.iter().find(|(_, held)| *held == words) {
            return *label;
        }
        let label = self.asm.label();
        self.pool.push((label, words));
        label
    }

    /// The pool, after the code it belongs to.
    fn emit_pool(&mut self) {
        for (label, words) in std::mem::take(&mut self.pool) {
            self.asm.bind(label);
            for word in words {
                self.asm.word(word);
            }
        }
    }

    fn region(&mut self, region: RegionId) {
        // The program outlives this, so the walk borrows it rather than
        // `self`, and the loop stays one pass over a contiguous run.
        let program = self.program;
        let steps: Vec<(&Op, &[ValueId])> = program.walk(region).collect();
        let params = self
            .loops
            .last()
            .map(|frame| frame.0.clone())
            .unwrap_or_default();
        for index in self.order(region, &params) {
            let (op, results) = steps[index];
            self.instruction(op, results);
        }
        if let Some(terminator) = program.region(region).terminator {
            self.terminator(terminator);
        }
    }

    /// Store each source into its destination as one simultaneous
    /// assignment.
    fn transfer(&mut self, sources: &[ValueId], destinations: &[ValueId]) {
        assert!(sources.len() <= 2, "at most two values cross a region edge");
        // A value that already lives where it is going does not move, which
        // is what makes a coalesced loop parameter free.
        let moving: Vec<bool> = sources
            .iter()
            .zip(destinations)
            .map(|(&source, &destination)| !self.same_place(source, destination))
            .collect();
        // Writing one destination can only disturb another pair's source
        // when the two share a place; short of that the moves are
        // independent and need no scratch between them.
        let tangled = destinations
            .iter()
            .enumerate()
            .any(|(index, &destination)| {
                sources
                    .iter()
                    .enumerate()
                    .any(|(other, &source)| other != index && self.same_place(destination, source))
            });
        if tangled {
            self.transfer_through_scratch(sources, destinations, &moving);
            return;
        }
        for (index, &source) in sources.iter().enumerate() {
            if !moving[index] {
                continue;
            }
            let from = self.operand(source, T0);
            self.put(destinations[index], from);
        }
    }

    /// Every source read out before any destination is written, so that one
    /// move cannot destroy another's input.
    fn transfer_through_scratch(
        &mut self,
        sources: &[ValueId],
        destinations: &[ValueId],
        moving: &[bool],
    ) {
        for (index, &source) in sources.iter().enumerate() {
            if moving[index] {
                self.read(if index == 0 { T0 } else { T1 }, source);
            }
        }
        for (index, &destination) in destinations.iter().enumerate() {
            if moving[index] {
                self.commit(destination, if index == 0 { T0 } else { T1 });
            }
        }
    }

    /// Whether two values are held in the very same place.
    fn same_place(&self, left: ValueId, right: ValueId) -> bool {
        match (self.source[left.index()], self.source[right.index()]) {
            (Source::Home(a), Source::Home(b)) | (Source::Slot(a), Source::Slot(b)) => a == b,
            _ => false,
        }
    }

    /// Branch when a condition is true.
    fn branch_if_true(
        &mut self,
        condition: ValueId,
        comparison: Option<(Relation, ValueId, ValueId)>,
        target: super::asm::Label,
    ) {
        if let Some((relation, left, right)) = comparison {
            // The operands may load, and the flags have to outlive that, so
            // both are in hand before the comparison itself.
            let left = self.operand(left, T0);
            let right = self.operand(right, T1);
            self.holds(relation, left, right, target);
            return;
        }
        self.read(T0, condition);
        self.asm.lda_zp(T0);
        self.asm.ora_zp(T0 + 1);
        self.asm.branch(Cc::NotEqual, target);
    }

    /// Branch when a condition is false.
    fn branch_if_false(
        &mut self,
        condition: ValueId,
        comparison: Option<(Relation, ValueId, ValueId)>,
        target: super::asm::Label,
    ) {
        if let Some((relation, left, right)) = comparison {
            let left = self.operand(left, T0);
            let right = self.operand(right, T1);
            self.holds_not(relation, left, right, target);
            return;
        }
        self.read(T0, condition);
        self.asm.lda_zp(T0);
        self.asm.ora_zp(T0 + 1);
        self.asm.branch(Cc::Equal, target);
    }

    /// The upper bound established in the true arm of a comparison.
    fn comparison_bound(
        &self,
        comparison: Option<(Relation, ValueId, ValueId)>,
    ) -> Option<(ValueId, u64)> {
        let (Relation::Less, left, right) = comparison? else {
            return None;
        };
        let Source::Const(limit) = self.source[right.index()] else {
            return None;
        };
        limit.checked_sub(1).map(|high| (left, high))
    }

    /// Whether this arm reaches its enclosing `if`'s continuation.
    fn yields(&self, region: RegionId) -> bool {
        self.program
            .region(region)
            .terminator
            .is_some_and(|term| term.exit == Exit::Yield)
    }

    fn conditional(
        &mut self,
        condition: ValueId,
        then_region: RegionId,
        else_region: RegionId,
        results: &[ValueId],
    ) {
        let comparison = self
            .pending
            .take_if(|(value, ..)| *value == condition)
            .map(|(_, relation, left, right)| (relation, left, right));
        let bound = self.comparison_bound(comparison);
        let (then_yields, else_yields) = (self.yields(then_region), self.yields(else_region));

        // Put an arm that cannot reach the continuation before the one that
        // can. The yielding arm then runs straight into the instructions
        // after the `if`, without a transfer through storage or a jump over
        // the terminal arm.
        if then_yields && !else_yields {
            let continuing = self.asm.label();
            self.branch_if_true(condition, comparison, continuing);
            self.region(else_region);
            self.asm.bind(continuing);
            self.ifs.push((results.to_vec(), None));
            self.region_below(then_region, bound);
            self.ifs.pop();
            return;
        }
        let otherwise = self.asm.label();
        let end = self.asm.label();
        self.branch_if_false(condition, comparison, otherwise);
        // Only a then arm with an else arm after it that also reaches the
        // continuation has something to jump over. The else arm, written
        // last, runs straight into it.
        let over = then_yields && else_yields;
        self.ifs.push((results.to_vec(), over.then_some(end)));
        self.region_below(then_region, bound);
        self.ifs.pop();
        self.asm.bind(otherwise);
        self.ifs.push((results.to_vec(), None));
        self.region(else_region);
        self.ifs.pop();
        self.asm.bind(end);
    }

    fn repeat(&mut self, initial: &[ValueId], body: RegionId, results: &[ValueId]) {
        let head = self.asm.label();
        let end = self.asm.label();

        let program = self.program;
        let params = program.values(program.region(body).params);
        self.transfer(initial, params);
        self.asm.bind_reentered(head);
        self.loops
            .push((params.to_vec(), head, results.to_vec(), end));
        self.region(body);
        self.loops.pop();
        self.asm.bind(end);
    }

    fn load_at(&mut self, width: Width, address: ValueId, offset: Offset, result: ValueId) {
        self.read(PTR, address);
        let at = displacement(offset);
        self.asm.ldy_imm(at);
        self.asm.lda_ind_y(PTR);
        self.asm.sta_zp(T0);
        if width == Width::Byte {
            self.asm.lda_imm(0);
        } else {
            self.asm.iny();
            self.asm.lda_ind_y(PTR);
        }
        self.asm.sta_zp(T0 + 1);
        self.commit(result, T0);
    }

    fn store_at(&mut self, width: Width, address: ValueId, offset: Offset, value: ValueId) {
        self.read(T0, value);
        self.read(PTR, address);
        let at = displacement(offset);
        self.asm.ldy_imm(at);
        self.asm.lda_zp(T0);
        self.asm.sta_ind_y(PTR);
        if matches!(width, Width::Word) {
            self.asm.iny();
            self.asm.lda_zp(T0 + 1);
            self.asm.sta_ind_y(PTR);
        }
    }

    fn platform_call(&mut self, name: &str, args: &[ValueId], results: &[ValueId]) {
        match name {
            "write!" => self.move_bytes((Operand::Imm(1), args[0], args[1]), HOOK_WRITE),
            "write_fd!" => self.stream(args, HOOK_WRITE, results[0]),
            "read_fd!" => self.stream(args, HOOK_READ, results[0]),
            "open_at!" => self.open_at(args, results[0]),
            "fd_close!" => self.close_fd(args, results[0]),
            "read_byte!" => self.read_byte(results[0]),
            "exit!" => {
                let status = self.operand(args[0], T0);
                self.load(status.byte(0));
                self.asm.jmp_abs(HOOK_EXIT);
            }
            // There is no kernel to ask, so the region is the next unused
            // memory above the image.
            "grow" => {
                self.read(T0, args[0]);
                self.asm.lda_zp(HEAP);
                self.asm.sta_zp(T1);
                self.asm.lda_zp(HEAP + 1);
                self.asm.sta_zp(T1 + 1);

                self.asm.clc();
                self.asm.lda_zp(HEAP);
                self.asm.adc_zp(T0);
                self.asm.sta_zp(HEAP);
                self.asm.lda_zp(HEAP + 1);
                self.asm.adc_zp(T0 + 1);
                self.asm.sta_zp(HEAP + 1);

                self.commit(results[0], T1);
            }
            other => panic!("`{other}` is not one this answers for, which `accepts` says first"),
        }
    }

    /// Arguments go in fixed pairs, so the callee has to take its copies
    /// before anything it calls overwrites them.
    fn call(&mut self, function: FunctionId, args: &[ValueId], results: &[ValueId]) {
        for (index, &arg) in args.iter().enumerate() {
            let index = u8::try_from(index).expect("a few arguments");
            assert!(index < ARG_COUNT, "at most four arguments");
            self.read(ARGS + 2 * index, arg);
        }
        let target = self.starts[function.index()];
        self.asm.jsr(target);
        if let Some(&result) = results.first() {
            self.commit(result, R0);
        }
    }

    /// Only explicit narrowing discards bits, including widths inside a byte.
    /// A promotion leaves a fitting value unchanged.
    /// A value read at another width.
    ///
    /// An answer of eight bits or fewer is one byte worked out of one byte:
    /// nothing above them survives, so nothing above them is read. Only a
    /// wider answer goes through a scratch pair, where the half being kept
    /// may be the high one.
    fn convert(&mut self, class: Class, value: ValueId, result: ValueId) {
        let kept = bits(class);
        // Nothing to take off, nothing wanted that is not there, and
        // already where it is going.
        if kept >= self.stored(value)
            && (!self.wide(result) || self.wide(value))
            && self.same_place(value, result)
        {
            return;
        }
        if kept <= 8 {
            self.narrow(kept, value, result);
            return;
        }
        self.read(T0, value);
        let wide = self.wide(result);
        if kept == 0 {
            // Fixed0 has exactly one inhabitant: reduction modulo one.
            self.set_place(T0, 0, wide);
        } else if kept < bits(self.program.class(value)) && !self.fits_on_path(value, kept) {
            let byte = if kept <= 8 { T0 } else { T0 + 1 };
            let mask = ((1u16 << ((kept - 1) % 8 + 1)) - 1).to_le_bytes()[0];
            if mask != 0xFF {
                self.asm.lda_zp(byte);
                self.asm.and_imm(mask);
                self.asm.sta_zp(byte);
            }
            // What is left above the bits kept is dropped by not writing it
            // down, wherever the answer is narrow enough not to have any.
            if kept <= 8 && wide {
                self.asm.lda_imm(0);
                self.asm.sta_zp(T0 + 1);
            }
        }
        self.commit(result, T0);
    }

    /// The same, where the answer is one byte: read the byte it is worked
    /// out of, take off what the width does not keep, and write it down.
    fn narrow(&mut self, kept: u16, value: ValueId, result: ValueId) {
        let held = self.stored(value);
        let from = self.operand(value, T0);
        let dest = self.dest(result);
        if kept == 0 {
            // Fixed0 has exactly one inhabitant: reduction modulo one.
            self.asm.lda_imm(0);
        } else {
            // A value already where it is going, with nothing to take off
            // it, is a value this has nothing to do about.
            if kept >= held && matches!(from, Operand::Zp { at, .. } if at == dest) {
                return;
            }
            self.load(from.byte(0));
            let mask = ((1u16 << ((kept - 1) % 8 + 1)) - 1).to_le_bytes()[0];
            if kept < held && !self.fits_on_path(value, kept) && mask != 0xFF {
                self.asm.and_imm(mask);
            }
        }
        self.asm.sta_zp(dest);
        self.commit(result, dest);
    }

    fn arithmetic(
        &mut self,
        op: Binary,
        mut left: Operand,
        mut right: Operand,
        dest: u8,
        width: Width,
        carry_after: Option<bool>,
    ) {
        // A value added to itself is that value moved up one place.
        // `simplify` says so wherever it can see one value read twice; what
        // it cannot see is two values given the same place, and a place
        // holds what it holds. It also never sees a program handed straight
        // to a target.
        if op == Binary::Add && left == right {
            self.shifted(Direction::Up, left, dest, 1, width);
            if let Some(carry) = carry_after {
                self.asm.carry_is(carry);
            }
            return;
        }
        // Addition may start from either side. Keep the source order on a tie,
        // but do not replace the byte already in the accumulator with the
        // other one. This is deliberately byte-only: a word operation starts
        // at its low half while the preceding operation leaves its high half
        // in the accumulator.
        if op == Binary::Add
            && width == Width::Byte
            && self.asm.needs_load(left.byte(0))
            && !self.asm.needs_load(right.byte(0))
        {
            (left, right) = (right, left);
        }
        // A step of one over a pair the result already occupies is an
        // increment, which carries into the high byte only on a wrap.
        if let (Operand::Zp { at, .. }, Operand::Imm(1), Width::Word) = (left, right, width)
            && at == dest
        {
            self.step(op, dest);
            return;
        }
        // Both low bytes are read before the low result is written, and both
        // high bytes before the high one, so the destination may be one of
        // the operands.
        self.load(left.byte(0));
        let low = self.begin_chain(op, right.byte(0));
        self.accumulate(op, low);
        self.asm.sta_zp(dest);
        // An answer of eight bits or fewer has nothing above them to write,
        // and the place it goes to keeps nothing above them either.
        if width == Width::Byte {
            if let Some(carry) = carry_after {
                self.asm.carry_is(carry);
            }
            return;
        }
        self.load(left.byte(1));
        self.accumulate(op, right.byte(1));
        self.asm.sta_zp(dest + 1);
        if let Some(carry) = carry_after {
            self.asm.carry_is(carry);
        }
    }

    /// A step of one over a pair, which reaches the high byte only where the
    /// low one wrapped.
    /// `left - right`, or nought where that borrows.
    ///
    /// The subtraction's carry is the comparison, set exactly where `left`
    /// is at least `right`, so where the borrow is worked out anyway the
    /// subtraction is the test. A one-byte answer out of two-byte operands
    /// would work out a high byte for its borrow alone, pushing the low one
    /// out of A; there the comparison decides first and only the low byte
    /// is subtracted.
    fn monus(&mut self, left: ValueId, right: ValueId, result: ValueId) {
        let left = self.operand(left, T0);
        let right = self.operand(right, T1);
        let dest = self.dest(result);
        let wide = self.wide(result);
        // High bytes that are the same literal or place leave the borrow as
        // the low byte did.
        let ties = left.byte(1) == right.byte(1);
        if ties || wide {
            self.load(left.byte(0));
            let low = self.begin_chain(Binary::Sub, right.byte(0));
            self.accumulate(Binary::Sub, low);
            self.asm.sta_zp(dest);
            if !ties || wide {
                self.load(left.byte(1));
                self.accumulate(Binary::Sub, right.byte(1));
                if wide {
                    self.asm.sta_zp(dest + 1);
                }
            }
            let kept = self.asm.label();
            self.asm.branch(Cc::Carry, kept);
            self.clear(dest, wide);
            self.asm.bind(kept);
        } else {
            let under = self.asm.label();
            let done = self.asm.label();
            self.holds(Relation::Less, left, right, under);
            self.load(left.byte(0));
            let low = self.begin_chain(Binary::Sub, right.byte(0));
            self.accumulate(Binary::Sub, low);
            self.asm.sta_zp(dest);
            self.asm.jmp(done);
            self.asm.bind(under);
            self.clear(dest, false);
            self.asm.bind(done);
        }
        self.commit(result, dest);
    }

    /// Nought in a place, one byte or both.
    fn clear(&mut self, at: u8, wide: bool) {
        self.asm.carry(Held::Imm(0), at);
        if wide {
            self.asm.carry(Held::Imm(0), at + 1);
        }
    }

    /// Ready the carry for the low byte of a sum or difference, and say
    /// what that byte is then combined with.
    ///
    /// A literal can take up a carry already the other way: with carry set,
    /// `adc #v-1` answers what `adc #v` does with it clear, carry out
    /// included, and with carry clear `sbc #v-1` answers `sbc #v`. Nought
    /// has nothing below it to become.
    fn begin_chain(&mut self, op: Binary, right: Held) -> Held {
        match (op, right, self.asm.known_carry()) {
            (Binary::Add, Held::Imm(value), Some(true))
            | (Binary::Sub, Held::Imm(value), Some(false))
                if value > 0 =>
            {
                Held::Imm(value - 1)
            }
            (Binary::Add, ..) => {
                self.asm.clc();
                right
            }
            (Binary::Sub, ..) => {
                self.asm.sec();
                right
            }
            _ => unreachable!("multiply/divide use bitwise legalization"),
        }
    }

    fn step(&mut self, op: Binary, dest: u8) {
        let done = self.asm.label();
        match op {
            Binary::Add => {
                self.asm.inc_zp(dest);
                self.asm.branch(Cc::NotEqual, done);
                self.asm.inc_zp(dest + 1);
            }
            Binary::Sub => {
                self.asm.lda_zp(dest);
                self.asm.branch(Cc::NotEqual, done);
                self.asm.dec_zp(dest + 1);
            }
            _ => unreachable!("multiply/divide use bitwise legalization"),
        }
        self.asm.bind(done);
        if matches!(op, Binary::Sub) {
            self.asm.dec_zp(dest);
        }
    }

    /// A value with its bits moved, which this processor does one place at
    /// a time.
    ///
    /// A byte stays in the accumulator throughout: one instruction a place,
    /// and a single store at the end. Wider than that it cannot, so the
    /// first move reads the value into the answer and the rest move the
    /// answer where it lies, two instructions a place.
    ///
    /// The carry is what joins the halves. Neither the store of one byte nor
    /// the load of the next touches it, so the bit leaving one is still
    /// there to enter the other; moving up that means starting at the low
    /// byte, and moving down, at the high one.
    fn shifted(&mut self, direction: Direction, value: Operand, dest: u8, by: u16, width: Width) {
        if width == Width::Byte {
            self.load(value.byte(0));
            for _ in 0..by {
                match direction {
                    Direction::Up => self.asm.asl(),
                    Direction::Down => self.asm.lsr(),
                }
            }
            self.asm.sta_zp(dest);
            return;
        }
        let (first, second) = match direction {
            Direction::Up => (0, 1),
            Direction::Down => (1, 0),
        };
        self.load(value.byte(first));
        match direction {
            Direction::Up => self.asm.asl(),
            Direction::Down => self.asm.lsr(),
        }
        self.asm.sta_zp(dest + first);
        self.load(value.byte(second));
        match direction {
            Direction::Up => self.asm.rol(),
            Direction::Down => self.asm.ror(),
        }
        self.asm.sta_zp(dest + second);
        for _ in 1..by {
            match direction {
                Direction::Up => {
                    self.asm.asl_zp(dest);
                    self.asm.rol_zp(dest + 1);
                }
                Direction::Down => {
                    self.asm.lsr_zp(dest + 1);
                    self.asm.ror_zp(dest);
                }
            }
        }
    }

    /// Use the accumulator's shift for a byte-sized multiplication by three.
    /// The original remains in its home until the final store, so the result
    /// may share that home without losing the addend.
    fn multiply_by_three(&mut self, value: ValueId, result: ValueId) -> bool {
        if self.needed(result) > 8 {
            return false;
        }
        let from = self.operand(value, T0);
        let dest = self.dest(result);
        self.load(from.byte(0));
        self.asm.asl();
        if self.upper_bound(value).is_some_and(|high| high < 128) {
            self.asm.carry_is(false);
        }
        self.asm.clc();
        self.accumulate(Binary::Add, from.byte(0));
        if self
            .upper_bound(value)
            .and_then(|high| high.checked_mul(3))
            .is_some_and(|high| high < 256)
        {
            self.asm.carry_is(false);
        }
        self.asm.sta_zp(dest);
        self.commit(result, dest);
        true
    }

    /// Keep a byte sum's ninth bit in carry while dividing it by two.
    /// Both source bytes are consumed before the answer is written, so the
    /// answer may share either source's home.
    fn halve_sum(&mut self, left: ValueId, right: ValueId, result: ValueId) {
        let mut left = self.operand(left, T0);
        let mut right = self.operand(right, T1);
        if self.asm.needs_load(left.byte(0)) && !self.asm.needs_load(right.byte(0)) {
            (left, right) = (right, left);
        }
        self.load(left.byte(0));
        self.asm.clc();
        self.accumulate(Binary::Add, right.byte(0));
        self.asm.ror();
        let dest = self.dest(result);
        self.asm.sta_zp(dest);
        self.commit(result, dest);
    }

    /// Shift/add until an eight-bit multiplier is exhausted. Only the low
    /// product byte is retained, so overflow and signedness do not matter.
    /// Source values survive in their homes; the scratch bytes are clobbered.
    /// This is White Flame's 2003 early-exit layout, with target-owned scratch.
    fn multiply_byte(&mut self, left: ValueId, right: ValueId, result: ValueId) {
        let (mut multiplicand, mut multiplier) = (left, right);
        let left_high = self.upper_bound(left);
        let right_high = self.upper_bound(right);
        if left_high.is_some_and(|left| right_high.is_none_or(|right| left < right)) {
            (multiplicand, multiplier) = (multiplier, multiplicand);
        }
        let multiplicand = self.operand(multiplicand, T0);
        let multiplier = self.operand(multiplier, T1);
        self.load(multiplicand.byte(0));
        self.asm.sta_zp(T0);
        self.load(multiplier.byte(0));
        self.asm.sta_zp(T1);

        let add = self.asm.label();
        let loop_ = self.asm.label();
        let enter = self.asm.label();
        self.asm.lda_imm(0);
        self.asm.branch(Cc::Equal, enter);
        self.asm.bind_reentered(add);
        self.asm.clc();
        self.asm.adc_zp(T0);
        self.asm.bind_reentered(loop_);
        self.asm.asl_zp(T0);
        self.asm.bind(enter);
        self.asm.lsr_zp(T1);
        self.asm.branch(Cc::Carry, add);
        self.asm.branch(Cc::NotEqual, loop_);

        let dest = self.dest(result);
        self.asm.sta_zp(dest);
        self.commit(result, dest);
    }

    /// Shift/add in exactly sixteen rounds, independent of operand values.
    /// Only scratch pairs and X are destroyed; homes, ARGC and call arguments
    /// are untouched. The fit proof guarantees the final product fits.
    fn multiply(&mut self) {
        self.set_pair(PTR, 0);
        self.asm.ldx_imm(16);
        let head = self.asm.label();
        let skip = self.asm.label();
        self.asm.bind_reentered(head);
        self.asm.lsr_zp(T1 + 1);
        self.asm.ror_zp(T1);
        self.asm.branch(Cc::NoCarry, skip);
        self.arithmetic(
            Binary::Add,
            Operand::pair(PTR),
            Operand::pair(T0),
            PTR,
            Width::Word,
            None,
        );
        self.asm.bind(skip);
        self.asm.asl_zp(T0);
        self.asm.rol_zp(T0 + 1);
        self.asm.dex();
        self.asm.branch(Cc::NotEqual, head);
    }

    /// Restoring unsigned long division: T0 becomes the quotient and PTR
    /// the remainder. Each round consumes one dividend bit. The carry out
    /// of the remainder is its seventeenth bit, not something to discard
    /// before deciding to subtract. Division by zero is handled separately.
    fn divide(&mut self) {
        let zero = self.asm.label();
        let done = self.asm.label();
        let head = self.asm.label();
        let subtract = self.asm.label();
        let next = self.asm.label();
        self.set_pair(PTR, 0);
        self.asm.lda_zp(T1);
        self.asm.ora_zp(T1 + 1);
        self.asm.branch(Cc::Equal, zero);
        self.asm.ldx_imm(16);
        self.asm.bind_reentered(head);
        self.asm.asl_zp(T0);
        self.asm.rol_zp(T0 + 1);
        self.asm.rol_zp(PTR);
        self.asm.rol_zp(PTR + 1);
        self.asm.branch(Cc::Carry, subtract);
        self.holds(Relation::Less, Operand::pair(PTR), Operand::pair(T1), next);
        self.asm.bind(subtract);
        self.arithmetic(
            Binary::Sub,
            Operand::pair(PTR),
            Operand::pair(T1),
            PTR,
            Width::Word,
            None,
        );
        self.asm.inc_zp(T0); // the shifted-in quotient bit was zero
        self.asm.bind(next);
        self.asm.dex();
        self.asm.branch(Cc::NotEqual, head);
        self.asm.jmp(done);
        self.asm.bind(zero);
        self.asm.carry(Held::Zero(T0), PTR);
        self.asm.carry(Held::Zero(T0 + 1), PTR + 1);
        self.set_pair(T0, 0);
        self.asm.bind(done);
    }

    /// Read a byte the accumulator is about to work on. What it already
    /// holds it does not read again.
    fn load(&mut self, byte: Held) {
        self.asm.load(byte);
    }

    fn accumulate(&mut self, op: Binary, byte: Held) {
        match (op, byte) {
            (Binary::Add, Held::Imm(value)) => self.asm.adc_imm(value),
            (Binary::Add, Held::Zero(at)) => self.asm.adc_zp(at),
            (Binary::Sub, Held::Imm(value)) => self.asm.sbc_imm(value),
            (Binary::Sub, Held::Zero(at)) => self.asm.sbc_zp(at),
            _ => unreachable!("multiply/divide use bitwise legalization"),
        }
    }

    fn compare_byte(&mut self, left: Held, right: Held) {
        // Comparing through X preserves a different byte already in A. The
        // argument hook returns a word in A:X, so this can test its high half
        // without spilling either register merely to load it back.
        if self.asm.needs_load(left) && self.asm.x_holds(left) {
            match right {
                Held::Imm(value) => self.asm.cpx_imm(value),
                Held::Zero(at) => self.asm.cpx_zp(at),
            }
            return;
        }
        self.load(left);
        match right {
            Held::Imm(value) => self.asm.cmp_imm(value),
            Held::Zero(at) => self.asm.cmp_zp(at),
        }
    }

    /// Set Z for a branch on whether two bytes are equal, and nothing a
    /// branch on carry could read. Against nought, a byte Z already
    /// reflects needs no compare at all.
    fn test_equal(&mut self, left: Held, right: Held) {
        if nought(right) && self.asm.zero_reflects(left) {
            return;
        }
        self.compare_byte(left, right);
    }

    /// Branch to `yes` when the relation holds, and fall through when it
    /// does not.
    fn holds(&mut self, relation: Relation, left: Operand, right: Operand, yes: super::asm::Label) {
        let no = self.asm.label();
        match relation {
            Relation::Equal => {
                self.test_equal(left.byte(0), right.byte(0));
                // Narrow values both name immediate zero above their low
                // byte; the same place or literal is necessarily equal too.
                if left.byte(1) != right.byte(1) {
                    self.asm.branch(Cc::NotEqual, no);
                    self.test_equal(left.byte(1), right.byte(1));
                }
                self.asm.branch(Cc::Equal, yes);
            }
            // High bytes that are the same literal or place tie, and the
            // low byte decides alone.
            Relation::Less if left.byte(1) == right.byte(1) => {
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::NoCarry, yes);
            }
            // Unsigned, high byte first; the low byte only decides a tie.
            // Nothing is under nought, so against it only Z is read.
            Relation::Less if nought(right.byte(1)) => {
                self.test_equal(left.byte(1), right.byte(1));
                self.asm.branch(Cc::NotEqual, no);
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::NoCarry, yes);
            }
            Relation::Less => {
                self.compare_byte(left.byte(1), right.byte(1));
                self.asm.branch(Cc::NoCarry, yes);
                self.asm.branch(Cc::NotEqual, no);
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::NoCarry, yes);
            }
        }
        self.asm.bind(no);
    }

    /// Branch to `no` when the relation does not hold, and fall through when
    /// it does.
    fn holds_not(
        &mut self,
        relation: Relation,
        left: Operand,
        right: Operand,
        no: super::asm::Label,
    ) {
        match relation {
            Relation::Equal => {
                self.test_equal(left.byte(0), right.byte(0));
                self.asm.branch(Cc::NotEqual, no);
                if left.byte(1) != right.byte(1) {
                    self.test_equal(left.byte(1), right.byte(1));
                    self.asm.branch(Cc::NotEqual, no);
                }
            }
            Relation::Less if left.byte(1) == right.byte(1) => {
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::Carry, no);
            }
            Relation::Less if nought(right.byte(1)) => {
                self.test_equal(left.byte(1), right.byte(1));
                self.asm.branch(Cc::NotEqual, no);
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::Carry, no);
            }
            Relation::Less => {
                self.compare_byte(left.byte(1), right.byte(1));
                let yes = self.asm.label();
                self.asm.branch(Cc::NoCarry, yes);
                self.asm.branch(Cc::NotEqual, no);
                self.compare_byte(left.byte(0), right.byte(0));
                self.asm.branch(Cc::Carry, no);
                self.asm.bind(yes);
            }
        }
    }

    /// `dest = left relation right`, as one or zero.
    fn comparison(&mut self, relation: Relation, left: Operand, right: Operand, dest: u8) {
        let yes = self.asm.label();
        let done = self.asm.label();
        self.holds(relation, left, right, yes);
        self.set_pair(dest, 0);
        self.asm.jmp(done);
        self.asm.bind(yes);
        self.set_pair(dest, 1);
        self.asm.bind(done);
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one call per op; the length is the patterns"
    )]
    fn instruction(&mut self, op: &Op, results: &[ValueId]) {
        let program = self.program;
        match op {
            Op::NaturalConstant(_) => unreachable!("target acceptance rejects arbitrary precision"),
            Op::Float { .. } => unreachable!("this target says it computes no floats"),
            Op::Cell { .. }
            | Op::CellTag { .. }
            | Op::CellField { .. }
            | Op::BufferEmpty { .. }
            | Op::BufferKnown { .. }
            | Op::BufferPush { .. }
            | Op::BufferPrepend { .. }
            | Op::BufferExtend { .. }
            | Op::BufferRoom { .. }
            | Op::BufferAt { .. }
            | Op::Keep { .. }
            | Op::BufferField { .. } => {
                unreachable!("target preparation legalizes abstract cells")
            }
            Op::Constant { .. } | Op::AddressOf(_) => {}
            Op::Binary {
                op: Binary::Monus,
                left,
                right,
            } => self.monus(*left, *right, results[0]),
            Op::Binary { op, left, right } => {
                if self.halved_sums[results[0].index()].is_some() {
                    return;
                }
                if *op == Binary::Mul {
                    let scaled = match (self.constant(*left), self.constant(*right)) {
                        (Some(3), _) => Some(*right),
                        (_, Some(3)) => Some(*left),
                        _ => None,
                    };
                    if scaled.is_some_and(|value| self.multiply_by_three(value, results[0])) {
                        return;
                    }
                    if self.needed(results[0]) <= 8 {
                        self.multiply_byte(*left, *right, results[0]);
                        return;
                    }
                }
                if matches!(op, Binary::Mul | Binary::Div | Binary::Mod) {
                    // Copy both operands before touching any destination: loop
                    // coalescing may give it the same home as an input.
                    self.read(T0, *left);
                    self.read(T1, *right);
                    let pair = if *op == Binary::Mul {
                        self.multiply();
                        PTR
                    } else {
                        self.divide();
                        if *op == Binary::Div { T0 } else { PTR }
                    };
                    self.commit(results[0], pair);
                    return;
                }
                let left_id = *left;
                let right_id = *right;
                let left = self.operand(left_id, T0);
                let right = self.operand(right_id, T1);
                // As wide as anything reads the answer, which is not always
                // as wide as the answer can be: a sum narrowed straight away
                // has a high half nobody looks at and nothing writes it.
                let width = if self.needed(results[0]) <= 8 {
                    Width::Byte
                } else {
                    Width::Word
                };
                let bits = if width == Width::Byte { 8 } else { 16 };
                let carry_after = (*op == Binary::Add
                    && self
                        .upper_bound(left_id)
                        .zip(self.upper_bound(right_id))
                        .is_some_and(|(left, right)| {
                            left.checked_add(right)
                                .is_some_and(|sum| sum < (1u64 << bits))
                        }))
                .then_some(false);
                let dest = self.dest(results[0]);
                self.arithmetic(*op, left, right, dest, width, carry_after);
                self.commit(results[0], dest);
            }
            Op::Shift {
                direction,
                value,
                by,
            } => {
                if *direction == Direction::Down
                    && *by == 1
                    && let Some((left, right)) = self.halved_sums[value.index()]
                {
                    self.halve_sum(left, right, results[0]);
                    return;
                }
                let value = self.operand(*value, T0);
                let width = if self.needed(results[0]) <= 8 {
                    Width::Byte
                } else {
                    Width::Word
                };
                let dest = self.dest(results[0]);
                self.shifted(*direction, value, dest, *by, width);
                self.commit(results[0], dest);
            }
            Op::Compare {
                relation,
                left,
                right,
            } => {
                // When the next `if` is the only reader, the flags carry the
                // answer and the one-or-zero word is never built.
                if self.fused.contains(&results[0].index()) {
                    self.pending = Some((results[0], *relation, *left, *right));
                    return;
                }
                let left = self.operand(*left, T0);
                let right = self.operand(*right, T1);
                let dest = self.dest(results[0]);
                self.comparison(*relation, left, right, dest);
                self.commit(results[0], dest);
            }
            Op::Load {
                width,
                address,
                offset,
            } => self.load_at(held(*width), *address, *offset, results[0]),
            Op::Store {
                width,
                address,
                offset,
                value,
            } => self.store_at(held(*width), *address, *offset, *value),
            Op::Convert { value } => {
                self.convert(program.class(results[0]), *value, results[0]);
            }
            Op::Call { function, args } => {
                if let Some(symbol) = program.function(*function).external() {
                    self.platform_call(program.name(symbol), program.values(*args), results);
                } else {
                    self.call(*function, program.values(*args), results);
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

    fn terminator(&mut self, terminator: Terminator) {
        let program = self.program;
        let values = program.values(terminator.values);
        match terminator.exit {
            Exit::Yield => {
                let (results, end) = self.ifs.last().expect("a yield inside an if").clone();
                self.transfer(values, &results);
                if let Some(end) = end {
                    self.asm.jmp(end);
                }
            }
            Exit::Continue => {
                let frame = self.loops.last().expect("a continue inside a loop");
                let (params, head) = (frame.0.clone(), frame.1);
                self.transfer(values, &params);
                self.asm.jmp(head);
            }
            Exit::Break => {
                let frame = self.loops.last().expect("a break inside a loop");
                let (results, end) = (frame.2.clone(), frame.3);
                self.transfer(values, &results);
                self.asm.jmp(end);
            }
            Exit::Return => {
                if let Some(&value) = values.first() {
                    self.read(R0, value);
                }
                if self.frame > 0 {
                    let frame = self.frame;
                    self.adjust_frame(frame, FrameAction::Leave);
                }
                self.asm.rts();
            }
        }
    }

    /// `value` when it is known at assembly time, without emitting anything.
    fn constant(&self, value: ValueId) -> Option<u16> {
        match self.source[value.index()] {
            Source::Const(word) => u16::try_from(word).ok(),
            Source::Addr(id) => Some(self.address(id)),
            Source::Home(_) | Source::Slot(_) => None,
        }
    }

    fn jsr_hook(&mut self, at: u16) {
        let back = self.asm.label();
        self.asm.jsr_abs(at, back);
        self.asm.bind(back);
    }
}

/// A memory width as this machine moves it: sixteen bits is its word, and
/// nothing is wider than that.
fn held(width: Width) -> Width {
    match width {
        Width::Byte => Width::Byte,
        Width::Bits16 | Width::Word => Width::Word,
        Width::Bits32 => unreachable!("nothing is wider than a word, which validation checks"),
    }
}

/// How wide a class is held, which for anything unfixed is a word.
fn bits(class: Class) -> u16 {
    class.bits(WORD_BITS)
}

/// A byte distance, which is what the machine addresses in.
fn displacement(offset: Offset) -> u8 {
    let bytes = match offset {
        Offset::Bytes(bytes) => bytes,
        Offset::Words(words) => words * WORD,
    };
    u8::try_from(bytes).expect("an offset a single index register can reach")
}
