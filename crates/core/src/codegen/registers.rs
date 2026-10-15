//! Register allocation for a machine with a file of registers.
//!
//! A target hands over its code as [`Code`]: blocks of instructions over
//! virtual registers, each operand naming its allowed register set and any
//! fixed or tied location, and each instruction the registers it clobbers or
//! uses as scratch. Sets can describe banks without teaching this module
//! target-specific register classes, aliases, encodings or ABI rules. What comes back says where each
//! value is at each point, and the moves between.
//!
//! The allocator walks each block in order, keeps live values in registers,
//! and where they run out puts in memory the value read furthest ahead,
//! loops counted; it splits at fixed operands, ties,
//! register-set requirements, scratch reservations, and clobbers. A block starts where a predecessor
//! already allocated left its values, so an edge moves only what changed.

#[cfg(test)]
mod banks_tests;
mod distance;

use std::collections::HashMap;

use distance::Distances;

use super::parallel_copy::{
    self, Copy as ParallelCopy, CopySource, Move as CopyMove, Place, TransitionCost,
};
use super::{FrameSlot, RegSet, Register};
use crate::index::{BitSet, Pool, Range, SparseSet, index};
use crate::ir::FunctionId;

index!(pub VReg, BlockId, InstId);

/// Where an operand must be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Constraint<R> {
    /// Any register permitted by the operand's allowed set.
    Any,
    Fixed(R),
    /// Where the operand at this position is: only the first, here.
    Tied(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Def,
    Use,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Timing {
    Early,
    Late,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OperandSpec<R> {
    pub role: Role,
    pub timing: Timing,
    pub constraint: Constraint<R>,
    /// Registers this operand may occupy, intersected with the target's
    /// register file. Independent of fixed and tied location constraints.
    pub allowed: RegSet,
}

/// One instruction: what it reads, what it answers, where each must be --
/// its result first where it has one, then each operand -- and what it
/// overwrites besides.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Inst {
    pub operands: Range,
    pub result: Option<VReg>,
    pub specs: Range,
    pub scratch: RegSet,
    pub clobbers: RegSet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Terminator<R> {
    Jump {
        target: BlockId,
        args: Range,
    },
    Branch {
        condition: VReg,
        allowed: RegSet,
        then_target: BlockId,
        then_args: Range,
        else_target: BlockId,
        else_args: Range,
    },
    /// Leaving the function with `values`, in `register`.
    Return {
        values: Range,
        register: R,
    },
    Halt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Block<R> {
    pub owner: FunctionId,
    pub params: Range,
    pub instructions: Range,
    pub terminator: Terminator<R>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Function {
    pub source: FunctionId,
    pub entry: BlockId,
}

/// What a target hands the allocator.
#[derive(Clone, Debug)]
pub struct Code<R> {
    /// How many values there are.
    pub values: usize,
    pub operands: Vec<VReg>,
    pub instructions: Pool<InstId, Inst>,
    pub specs: Vec<OperandSpec<R>>,
    /// Each block's instructions, in order.
    pub order: Vec<InstId>,
    pub block_params: Vec<VReg>,
    pub block_param_specs: Vec<OperandSpec<R>>,
    pub blocks: Pool<BlockId, Block<R>>,
    pub functions: Vec<Function>,
    /// The registers a value may be held in.
    pub registers: Vec<R>,
    /// A register outside `registers`, which moves between memory pass
    /// through, and which otherwise breaks a cycle of moves. The target's
    /// lowering must transfer a complete scalar bit pattern between any
    /// allocatable register, this scratch register, and a frame slot.
    pub copies: Option<R>,
}

impl<R: Register> Code<R> {
    /// Where a cycle among `copies` is broken: the copying register where
    /// no copy between memory needs it, and otherwise slot nought.
    #[must_use]
    pub fn temporary(&self, copies: &[ParallelCopy<R>]) -> Place<R> {
        parallel_copy::temporary(copies, self.copies)
    }

    /// Where the operand at `at` of `inst` must be: its result first.
    #[must_use]
    pub fn spec(&self, inst: &Inst, at: usize) -> Option<OperandSpec<R>> {
        self.specs[inst.specs.range()].get(at).copied()
    }
}

/// Where each value is, and the moves between: what allocating `code`
/// answers, with the points it was worked out at.
///
/// # Errors
///
/// Where the code asks more of the registers than there are, or the
/// allocation it came to does not hold.
pub fn allocate<R: Register>(code: &Code<R>) -> Result<(Liveness, Allocation<R>), String> {
    verify_register_sets(code)?;
    let liveness = Liveness::build(code)?;
    let allocation = Allocator::new(code, &liveness)?.run()?;
    allocation.verify(code, &liveness)?;
    Ok((liveness, allocation))
}

/// The blocks each block reaches.
#[must_use]
pub const fn successors<R: Copy>(terminator: Terminator<R>) -> [Option<BlockId>; 2] {
    match terminator {
        Terminator::Jump { target, .. } => [Some(target), None],
        Terminator::Branch {
            then_target,
            else_target,
            ..
        } => [Some(then_target), Some(else_target)],
        Terminator::Return { .. } | Terminator::Halt => [None, None],
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point(u32);

impl Point {
    /// # Errors
    ///
    /// Past four billion points.
    pub fn at(index: usize) -> Result<Self, String> {
        Ok(Self(
            u32::try_from(index).map_err(|_| "selected function has over 4G points")?,
        ))
    }

    /// # Panics
    ///
    /// Never, on any machine whose pointers reach 32 bits.
    #[must_use]
    pub fn index(self) -> usize {
        usize::try_from(self.0).expect("an allocation point that fits")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpillSlot(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Location<R> {
    Register(R),
    Spill(SpillSlot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment<R> {
    pub value: VReg,
    pub start: Point,
    pub end: Point,
    pub location: Location<R>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Transition<R> {
    pub value: VReg,
    pub at: Point,
    pub from: Location<R>,
    pub to: Location<R>,
}

#[derive(Debug)]
pub struct EdgeMoves<R> {
    pub from: BlockId,
    pub target: BlockId,
    pub moves: Vec<CopyMove<R>>,
}

#[derive(Debug)]
pub struct Allocation<R> {
    pub segments: Vec<Segment<R>>,
    pub transitions: Vec<Transition<R>>,
    pub operand_locations: Vec<Vec<Location<R>>>,
    pub operand_moves: Vec<Vec<CopyMove<R>>>,
    pub edge_moves: Vec<EdgeMoves<R>>,
    pub edge_cost: TransitionCost,
    pub edges: u32,
    pub spill_slots: Vec<u32>,
    /// Where each value that ever waits in memory is written there: at the
    /// point it is made, from the register it is made in, by point. A value
    /// never changes, so its slot holds it from there on, and no other move
    /// of it into memory needs writing: see [`Self::elides`].
    pub stores: Vec<(Point, R, SpillSlot)>,
}

#[derive(Debug)]
pub struct InstPoints {
    pub instruction: InstId,
    pub early: Point,
    pub late: Point,
}

#[derive(Debug)]
pub struct BlockPoints {
    pub block: BlockId,
    pub entry: Point,
    pub instructions: Vec<InstPoints>,
    pub terminator: Point,
}

/// The values live at each point, and where each block's points are.
///
/// Liveness never crosses a function, so each function is solved over its
/// own values alone, and a point keeps only what is live there: the cost is
/// what the program holds live, not every value at every point.
#[derive(Debug)]
pub struct Liveness {
    at: Vec<LiveSet>,
    pub blocks: Vec<BlockPoints>,
}

/// The values live at one point, in ascending order.
#[derive(Debug, Default)]
struct LiveSet(Box<[VReg]>);

impl LiveSet {
    fn iter(&self) -> impl Iterator<Item = VReg> + '_ {
        self.0.iter().copied()
    }

    fn contains(&self, value: VReg) -> bool {
        self.0.binary_search(&value).is_ok()
    }

    /// Where `value` is among the members, if it is one.
    fn position(&self, value: VReg) -> Option<usize> {
        self.0.binary_search(&value).ok()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

// A value's number within the function that holds it.
index!(Local);

#[derive(Debug)]
struct PointState<R> {
    block: BlockId,
    values: Vec<(VReg, Location<R>)>,
}

impl Liveness {
    fn build<R: Register>(code: &Code<R>) -> Result<Self, String> {
        let (blocks, points) = number_points(code)?;
        let mut liveness = Self {
            at: (0..points).map(|_| LiveSet::default()).collect(),
            blocks,
        };
        let mut by_function = vec![Vec::new(); function_count(code)];
        for (id, block) in code.blocks.iter_enumerated() {
            by_function[block.owner.index()].push(id);
        }
        let mut numbering = Numbering {
            local: vec![None; code.values],
            position: vec![0; code.blocks.len()],
        };
        for function in &by_function {
            liveness.solve_function(code, function, &mut numbering);
        }
        Ok(liveness)
    }

    /// Fill the points of one function's `blocks`: solve what is live out
    /// of each, then walk each block back from its end.
    fn solve_function<R: Register>(
        &mut self,
        code: &Code<R>,
        blocks: &[BlockId],
        numbering: &mut Numbering,
    ) {
        let values = numbering.number(code, blocks);
        let number = |value: VReg| numbering.local[value.index()].expect("a value of its function");
        let live_out = live_out(code, blocks, values.len(), numbering);
        // What is live is walked back through each block in a set that
        // costs what it holds, as most of a large function's values are
        // dead at any one point; each point takes it in the order of the
        // values' numbers.
        let mut live = SparseSet::new(values.len());
        let members = |live: &SparseSet<Local>| {
            let mut locals = live.members().to_vec();
            locals.sort_unstable();
            LiveSet(locals.iter().map(|local| values[local.index()]).collect())
        };
        for (at, &id) in blocks.iter().enumerate() {
            let layout = &self.blocks[id.index()];
            let block = code.blocks[id];
            live.clear();
            live.extend(live_out[at].iter());
            let live = &mut live;
            visit_terminator_values(code, block.terminator, |value| {
                live.insert(number(value));
            });
            self.at[layout.terminator.index()] = members(live);
            for points in layout.instructions.iter().rev() {
                let inst = code.instructions[points.instruction];
                if let Some(result) = inst.result {
                    live.insert(number(result));
                    self.at[points.late.index()] = members(live);
                    live.remove(number(result));
                } else {
                    self.at[points.late.index()] = members(live);
                }
                for &operand in &code.operands[inst.operands.range()] {
                    live.insert(number(operand));
                }
                self.at[points.early.index()] = members(live);
            }
            for &param in &code.block_params[block.params.range()] {
                live.insert(number(param));
            }
            self.at[layout.entry.index()] = members(live);
        }
        numbering.forget(&values);
    }
}

/// Each block's points, numbered consecutively in block order: an entry,
/// an early and a late point for each instruction, and a terminator; and
/// how many points there are.
fn number_points<R: Register>(code: &Code<R>) -> Result<(Vec<BlockPoints>, usize), String> {
    let mut cursor = 0;
    let mut blocks = Vec::with_capacity(code.blocks.len());
    for (id, block) in code.blocks.iter_enumerated() {
        let entry = Point::at(cursor)?;
        cursor += 1;
        let mut instructions = Vec::with_capacity(block.instructions.len());
        for &instruction in &code.order[block.instructions.range()] {
            let early = Point::at(cursor)?;
            let late = Point::at(cursor + 1)?;
            cursor += 2;
            instructions.push(InstPoints {
                instruction,
                early,
                late,
            });
        }
        let terminator = Point::at(cursor)?;
        cursor += 1;
        blocks.push(BlockPoints {
            block: id,
            entry,
            instructions,
            terminator,
        });
    }
    Ok((blocks, cursor))
}

/// What is live out of each of one function's `blocks`, over its `bound`
/// local numbers, solved to a fixed point over its CFG.
fn live_out<R: Register>(
    code: &Code<R>,
    blocks: &[BlockId],
    bound: usize,
    numbering: &Numbering,
) -> Vec<BitSet<Local>> {
    let number = |value: VReg| numbering.local[value.index()].expect("a value of its function");
    let (uses, defs) = block_uses_and_defs(code, blocks, bound, number);
    let mut live_in = vec![BitSet::new(bound); blocks.len()];
    let mut live_out = live_in.clone();
    let mut incoming = BitSet::new(bound);
    let mut changed = true;
    while changed {
        changed = false;
        for (at, &id) in blocks.iter().enumerate().rev() {
            for successor in successors(code.blocks[id].terminator).into_iter().flatten() {
                live_out[at].union_with(&live_in[numbering.position[successor.index()]]);
            }
            incoming.clone_from(&live_out[at]);
            incoming.subtract(&defs[at]);
            incoming.union_with(&uses[at]);
            if incoming != live_in[at] {
                live_in[at].clone_from(&incoming);
                changed = true;
            }
        }
    }
    live_out
}

/// Numbers within one function at a time, reused across functions: each
/// value's local number, and each block's position among its function's.
struct Numbering {
    local: Vec<Option<Local>>,
    position: Vec<usize>,
}

impl Numbering {
    /// Number every value `blocks` name, in ascending order of the values
    /// themselves, so a local set lists its members as the program numbers
    /// them; answer the values by local number.
    fn number<R: Register>(&mut self, code: &Code<R>, blocks: &[BlockId]) -> Vec<VReg> {
        let mut values = Vec::new();
        for (at, &id) in blocks.iter().enumerate() {
            self.position[id.index()] = at;
            let block = code.blocks[id];
            values.extend_from_slice(&code.block_params[block.params.range()]);
            for &instruction in &code.order[block.instructions.range()] {
                let inst = code.instructions[instruction];
                values.extend(inst.result);
                values.extend_from_slice(&code.operands[inst.operands.range()]);
            }
            visit_terminator_values(code, block.terminator, |value| values.push(value));
        }
        values.sort_unstable();
        values.dedup();
        for (at, &value) in values.iter().enumerate() {
            self.local[value.index()] = Some(Local::at(at));
        }
        values
    }

    fn forget(&mut self, values: &[VReg]) {
        for &value in values {
            self.local[value.index()] = None;
        }
    }
}

/// What each of `blocks` reads before defining, and what it defines, over
/// its function's local numbers.
fn block_uses_and_defs<R: Register>(
    code: &Code<R>,
    blocks: &[BlockId],
    bound: usize,
    number: impl Fn(VReg) -> Local,
) -> (Vec<BitSet<Local>>, Vec<BitSet<Local>>) {
    let mut uses = vec![BitSet::new(bound); blocks.len()];
    let mut defs = uses.clone();
    for (at, &id) in blocks.iter().enumerate() {
        let block = code.blocks[id];
        for &param in &code.block_params[block.params.range()] {
            defs[at].insert(number(param));
        }
        for &instruction in &code.order[block.instructions.range()] {
            let inst = code.instructions[instruction];
            for &operand in &code.operands[inst.operands.range()] {
                if !defs[at].contains(number(operand)) {
                    uses[at].insert(number(operand));
                }
            }
            if let Some(result) = inst.result {
                defs[at].insert(number(result));
            }
        }
        let (block_uses, block_defs) = (&mut uses[at], &defs[at]);
        visit_terminator_values(code, block.terminator, |value| {
            if !block_defs.contains(number(value)) {
                block_uses.insert(number(value));
            }
        });
    }
    (uses, defs)
}

fn visit_terminator_values<R: Register>(
    code: &Code<R>,
    terminator: Terminator<R>,
    mut visit: impl FnMut(VReg),
) {
    match terminator {
        Terminator::Jump { args, .. } => {
            for &value in &code.operands[args.range()] {
                visit(value);
            }
        }
        Terminator::Branch {
            condition,
            then_args,
            else_args,
            ..
        } => {
            visit(condition);
            for &value in code.operands[then_args.range()]
                .iter()
                .chain(&code.operands[else_args.range()])
            {
                visit(value);
            }
        }
        Terminator::Return { values, .. } => {
            for &value in &code.operands[values.range()] {
                visit(value);
            }
        }
        Terminator::Halt => {}
    }
}

/// Where each value is, kept with each register's occupant and the values
/// placed at all, so that asking who holds a register, or letting go of what
/// is no longer live, costs what is placed rather than every value the
/// program has.
struct Placement<R> {
    locations: Vec<Option<Location<R>>>,
    occupants: [Option<VReg>; 64],
    placed: Vec<VReg>,
}

impl<R: Register> Placement<R> {
    fn new(values: usize) -> Self {
        Self {
            locations: vec![None; values],
            occupants: [None; 64],
            placed: Vec::new(),
        }
    }

    fn get(&self, value: VReg) -> Option<Location<R>> {
        self.locations[value.index()]
    }

    /// Place<R> `value` at `location`, which a register's occupant has left.
    fn set(&mut self, value: VReg, location: Location<R>) {
        match self.locations[value.index()] {
            Some(Location::Register(reg)) => {
                if self.occupants[usize::from(reg.number())] == Some(value) {
                    self.occupants[usize::from(reg.number())] = None;
                }
            }
            Some(Location::Spill(_)) => {}
            None => self.placed.push(value),
        }
        if let Location::Register(reg) = location {
            self.occupants[usize::from(reg.number())] = Some(value);
        }
        self.locations[value.index()] = Some(location);
    }

    fn occupant(&self, reg: R) -> Option<VReg> {
        self.occupants[usize::from(reg.number())]
    }

    /// Let go of every placed value `keep` does not hold on to.
    fn keep(&mut self, keep: impl Fn(VReg) -> bool) {
        let (locations, occupants) = (&mut self.locations, &mut self.occupants);
        self.placed.retain(|&value| {
            if keep(value) {
                return true;
            }
            if let Some(Location::Register(reg)) = locations[value.index()] {
                occupants[usize::from(reg.number())] = None;
            }
            locations[value.index()] = None;
            false
        });
    }
}

struct Allocator<'a, R> {
    code: &'a Code<R>,
    liveness: &'a Liveness,
    states: Vec<Option<PointState<R>>>,
    placement: Placement<R>,
    /// The register each value is best defined in, where every fixed use of
    /// it agrees on one.
    preferred: Vec<Option<R>>,
    /// Preferred bank for otherwise unconstrained placement. Definitions
    /// bound it; agreeing uses narrow it. Uses can still request another bank.
    homes: Vec<RegSet>,
    /// Each value handed along an edge, by value: the block it is handed to
    /// and the parameter it becomes there.
    handed_to: Vec<Vec<(BlockId, VReg)>>,
    operand_locations: Vec<Option<Vec<Location<R>>>>,
    operand_moves: Vec<Option<Vec<CopyMove<R>>>>,
    edge_moves: Vec<EdgeMoves<R>>,
    edge_cost: TransitionCost,
    edges: u32,
    value_spills: Vec<Option<SpillSlot>>,
    /// The function whose blocks are being allocated.
    owner: FunctionId,
    /// Each function's next spill slot. Slots are numbered within a
    /// function, so its frame holds only what it spills.
    next_spill: Vec<u32>,
    /// What the instruction being allocated reads, writes or uses as
    /// scratch: a value put out of its register may wait in any other.
    busy: RegSet,
    /// For each value, every register some instruction it lives across
    /// writes or needs: one outside these holds it without moving.
    hazards: Vec<RegSet>,
    /// How far each value is from being read next: when registers run out,
    /// the one read furthest ahead waits in memory.
    distances: Distances,
    /// The block and point being allocated.
    now: (BlockId, Point),
}

impl<'a, R: Register> Allocator<'a, R> {
    fn new(code: &'a Code<R>, liveness: &'a Liveness) -> Result<Self, String> {
        if code.values > usize::try_from(u32::MAX).expect("u32 fits usize") {
            return Err("selected allocation has over 4G values".to_owned());
        }
        Ok(Self {
            code,
            liveness,
            states: (0..liveness.at.len()).map(|_| None).collect(),
            placement: Placement::new(code.values),
            preferred: preferred_registers(code),
            homes: preferred_sets(code),
            handed_to: handed_to(code),
            operand_locations: vec![None; code.instructions.len()],
            operand_moves: vec![None; code.instructions.len()],
            edge_moves: Vec::new(),
            edge_cost: TransitionCost::default(),
            edges: 0,
            value_spills: vec![None; code.values],
            // Set as each block is allocated.
            owner: FunctionId::at(0),
            // Slot zero is reserved for breaking parallel-copy cycles.
            next_spill: vec![1; function_count(code)],
            busy: RegSet::EMPTY,
            hazards: hazards(code, liveness),
            distances: Distances::new(code, liveness),
            now: (BlockId::at(0), Point(0)),
        })
    }

    fn run(mut self) -> Result<Allocation<R>, String> {
        let predecessors = predecessors(self.code, self.liveness);
        for layout in &self.liveness.blocks {
            self.owner = self.code.blocks[layout.block].owner;
            self.placement.keep(|_| false);
            self.inherit(layout, &predecessors[layout.block.index()]);
            self.allocate_entry(layout)?;
            for points in &layout.instructions {
                self.allocate_instruction(layout.block, points)?;
            }
            self.allocate_terminator(layout)?;
        }
        self.plan_edges()?;
        self.verify_states()?;
        let stores = self.stores();
        let (segments, transitions) = build_segments(&self.states, self.code.values)?;
        let operand_locations =
            collect_instruction_data(self.operand_locations, "operand allocation")?;
        let operand_moves = collect_instruction_data(self.operand_moves, "operand move plan")?;
        let mut spill_slots = function_spill_slots(
            self.code,
            self.liveness,
            &segments,
            &transitions,
            &operand_moves,
            &self.edge_moves,
        )?;
        widen_for_stores(self.code, self.liveness, &stores, &mut spill_slots)?;
        Ok(Allocation {
            segments,
            transitions,
            operand_locations,
            operand_moves,
            edge_moves: self.edge_moves,
            edge_cost: self.edge_cost,
            edges: self.edges,
            spill_slots,
            stores,
        })
    }

    /// Each value that ever waits in memory, written there where it is
    /// made, where it is made in a register: an instruction's result after
    /// the instruction, and a block's parameter on entering it. One handed
    /// to a block already in memory was written there by the edge.
    fn stores(&self) -> Vec<(Point, R, SpillSlot)> {
        let mut stores = Vec::new();
        let mut made = |point: Point, value: VReg| {
            if let Some(slot) = self.value_spills[value.index()]
                && let Ok(Location::Register(reg)) = self.location(point, value)
            {
                stores.push((point, reg, slot));
            }
        };
        for layout in &self.liveness.blocks {
            let block = self.code.blocks[layout.block];
            for &param in &self.code.block_params[block.params.range()] {
                made(layout.entry, param);
            }
            for points in &layout.instructions {
                if let Some(result) = self.code.instructions[points.instruction].result {
                    made(points.late, result);
                }
            }
        }
        stores.sort_by_key(|&(point, ..)| point.0);
        stores
    }

    /// Start a block where a predecessor already allocated left what it
    /// hands on: each value live through the edge where it was, and each
    /// parameter in the register its argument was in. A block started
    /// afresh would put everything in whichever order it met it, and every
    /// edge into it would move everything back.
    fn inherit(&mut self, layout: &BlockPoints, predecessors: &[(BlockId, Range)]) {
        for (value, location) in self.handed(layout, predecessors) {
            let free = match location {
                Location::Register(reg) => self.placement.occupant(reg).is_none(),
                Location::Spill(_) => true,
            };
            if free && self.placement.get(value).is_none() {
                self.placement.set(value, location);
            }
        }
    }

    /// Where the first predecessor already allocated leaves each value the
    /// block starts with: see [`Self::inherit`].
    fn handed(
        &self,
        layout: &BlockPoints,
        predecessors: &[(BlockId, Range)],
    ) -> Vec<(VReg, Location<R>)> {
        let Some((state, args)) = predecessors.iter().find_map(|&(from, args)| {
            let exit = self.liveness.blocks[from.index()].terminator;
            self.states[exit.index()]
                .as_ref()
                .map(|state| (state, args))
        }) else {
            return Vec::new();
        };
        let held = |value: VReg| {
            state
                .values
                .iter()
                .find(|&&(held, _)| held == value)
                .map(|&(_, location)| location)
        };
        let block = self.code.blocks[layout.block];
        let params = &self.code.block_params[block.params.range()];
        let mut handed: Vec<_> = self.liveness.at[layout.entry.index()]
            .iter()
            .filter(|value| !params.contains(value))
            .filter_map(|value| Some((value, held(value)?)))
            .collect();
        let specs = &self.code.block_param_specs[block.params.range()];
        for ((&param, &arg), spec) in params
            .iter()
            .zip(&self.code.operands[args.range()])
            .zip(specs)
        {
            // A parameter starts where its argument was only in the bank it
            // is best in: a loop's would otherwise stay wherever its entry
            // left it, and every time round would move it to where its
            // body works on it and back.
            if let (Some(Location::Register(reg)), Constraint::Any) = (held(arg), spec.constraint)
                && spec.allowed.contains(reg)
                && self.homes[param.index()].contains(reg)
            {
                handed.push((param, Location::Register(reg)));
            }
        }
        handed
    }

    fn allocate_entry(&mut self, layout: &BlockPoints) -> Result<(), String> {
        let block = self.code.blocks[layout.block];
        self.now = (layout.block, layout.entry);
        self.expire_to(layout.entry);
        let params = &self.code.block_params[block.params.range()];
        let specs = &self.code.block_param_specs[block.params.range()];
        let mut protected = Vec::new();
        for (&value, &spec) in params.iter().zip(specs) {
            if let Constraint::Fixed(reg) = spec.constraint {
                self.put_in_register(value, reg, &protected)?;
                protected.push(value);
            }
        }
        for (&value, spec) in params.iter().zip(specs) {
            if self.placement.get(value).is_none() {
                self.put_anywhere(value, &protected, RegSet(!spec.allowed.0))?;
                protected.push(value);
            }
        }
        self.fill_live(layout.entry, &protected, RegSet::EMPTY)?;
        self.record(layout.block, layout.entry);
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "early uses, clobbers, and late definitions are allocated as one instruction"
    )]
    fn allocate_instruction(&mut self, block: BlockId, points: &InstPoints) -> Result<(), String> {
        let inst = self.code.instructions[points.instruction];
        // Waiting somewhere the instruction clobbers would only be waiting
        // to be moved again.
        let requirements = inst;
        self.busy = RegSet(requirements.scratch.0 | requirements.clobbers.0);
        self.now = (block, points.early);
        self.expire_to(points.early);
        self.fill_live(points.early, &[], inst.scratch)?;
        let operands = &self.code.operands[inst.operands.range()];
        let before: Vec<_> = operands
            .iter()
            .map(|&value| self.placement.get(value))
            .collect();
        let def_offset = usize::from(inst.result.is_some());
        let mut protected = Vec::new();
        let mut tied = None;
        let mut assigned = vec![None; operands.len()];

        for (at, &value) in operands.iter().enumerate() {
            let spec = self
                .code
                .spec(&inst, def_offset + at)
                .expect("verified operand");
            if let Constraint::Fixed(reg) = spec.constraint {
                if assigned.iter().zip(operands).any(|(&location, &other)| {
                    location == Some(Location::Register(reg)) && other != value
                }) {
                    return Err("fixed register holds two simultaneous operands".to_owned());
                }
                self.put_in_register(value, reg, &protected)?;
                assigned[at] = Some(Location::Register(reg));
                self.busy.0 |= RegSet::of(&[reg]).0;
                protected.push(value);
            }
        }
        for (at, &value) in operands.iter().enumerate() {
            let spec = self
                .code
                .spec(&inst, def_offset + at)
                .expect("verified operand");
            if matches!(spec.constraint, Constraint::Fixed(_)) {
                continue;
            }
            let mut allowed = spec.allowed;
            let mut fixed = None;
            match spec.constraint {
                Constraint::Tied(0) => {
                    let def = self.code.spec(&inst, 0).expect("verified tied result");
                    allowed.0 &= def.allowed.0;
                    if let Constraint::Fixed(reg) = def.constraint {
                        fixed = Some(reg);
                    }
                }
                Constraint::Any => {}
                Constraint::Tied(other) => {
                    return Err(format!("allocator does not support tie to operand {other}"));
                }
                Constraint::Fixed(_) => unreachable!(),
            }
            let reserved = assigned
                .iter()
                .flatten()
                .fold(inst.scratch.0, |set, location| {
                    if let Location::Register(reg) = location {
                        set | RegSet::of(&[*reg]).0
                    } else {
                        set
                    }
                });
            self.busy.0 |= reserved;
            // Repeated operands may need several physical copies, even in
            // different banks. Never reuse an earlier copy for another value.
            let reused = assigned
                .iter()
                .zip(operands)
                .find_map(|(&location, &other)| {
                    if other == value
                        && let Some(Location::Register(reg)) = location
                        && allowed.contains(reg)
                        && fixed.is_none_or(|fixed| fixed == reg)
                    {
                        Some(reg)
                    } else {
                        None
                    }
                });
            let reg = if let Some(reg) = reused {
                reg
            } else if let Some(reg) = fixed {
                if reserved & RegSet::of(&[reg]).0 != 0 {
                    return Err("tied result conflicts with an assigned operand".to_owned());
                }
                self.put_in_register(value, reg, &protected)?;
                reg
            } else {
                self.put_in_some_register(value, &protected, RegSet(reserved | !allowed.0))?
            };
            if spec.constraint == Constraint::Tied(0) {
                if tied.is_some_and(|before| before != reg) {
                    return Err("tied operands require different registers".to_owned());
                }
                tied = Some(reg);
            }
            assigned[at] = Some(Location::Register(reg));
            self.busy.0 |= RegSet::of(&[reg]).0;
            protected.push(value);
        }
        let assigned = assigned
            .into_iter()
            .map(|location| location.ok_or_else(|| "use has no allocated location".to_owned()))
            .collect::<Result<Vec<_>, _>>()?;
        let read = assigned.iter().fold(0, |held, location| match *location {
            Location::Register(reg) => held | RegSet::of(&[reg]).0,
            Location::Spill(_) => held,
        });
        self.plan_operand_moves(points.instruction, operands, &before, &assigned)?;
        self.operand_locations[points.instruction.index()] = Some(assigned);
        self.evict_reserved(inst.scratch, &protected)?;
        self.record(block, points.early);

        self.now = (block, points.late);
        self.expire_to(points.late);
        let requirements = inst;
        let result = inst.result;
        // What the instruction reads, what it writes, and where its result
        // goes: a value living on past it can wait anywhere else.
        let answered = match self.code.spec(&inst, 0).map(|spec| spec.constraint) {
            Some(Constraint::Fixed(reg)) if result.is_some() => Some(reg),
            _ => tied,
        };
        let written = RegSet(
            read | requirements.clobbers.0
                | requirements.scratch.0
                | answered.map_or(0, |reg| RegSet::of(&[reg]).0),
        );
        self.busy = written;
        for &reg in &self.code.registers {
            if requirements.clobbers.contains(reg) || requirements.scratch.contains(reg) {
                self.evacuate(reg, result)?;
            }
        }
        if let Some(value) = result {
            let spec = self
                .code
                .spec(&inst, 0)
                .ok_or_else(|| "selected result has no allocation constraint".to_owned())?;
            if let Some(reg) = tied {
                self.put_in_register(value, reg, &[])?;
            } else {
                match spec.constraint {
                    Constraint::Fixed(reg) => self.put_in_register(value, reg, &[])?,
                    Constraint::Any => {
                        // A preferred register is worth taking where it is
                        // free, not worth putting something else out for.
                        if let Some(reg) =
                            self.preferred[value.index()].or_else(|| self.awaited(value))
                            && !requirements.scratch.contains(reg)
                            && spec.allowed.contains(reg)
                            && self.register_occupant(reg).is_none()
                        {
                            self.put_in_register(value, reg, &[])?;
                        } else {
                            self.put_in_some_register(
                                value,
                                &[],
                                RegSet(requirements.scratch.0 | !spec.allowed.0),
                            )?;
                        }
                    }
                    Constraint::Tied(other) => {
                        return Err(format!("allocator does not support result tie {other}"));
                    }
                }
            }
        }
        self.fill_live(
            points.late,
            &result.into_iter().collect::<Vec<_>>(),
            requirements.scratch,
        )?;
        self.record(block, points.late);
        self.busy = RegSet::EMPTY;
        Ok(())
    }

    fn allocate_terminator(&mut self, layout: &BlockPoints) -> Result<(), String> {
        let block = self.code.blocks[layout.block];
        self.now = (layout.block, layout.terminator);
        self.expire_to(layout.terminator);
        self.fill_live(layout.terminator, &[], RegSet::EMPTY)?;
        let mut protected = Vec::new();
        match block.terminator {
            Terminator::Branch {
                condition, allowed, ..
            } => {
                self.put_in_some_register(condition, &protected, RegSet(!allowed.0))?;
                protected.push(condition);
            }
            Terminator::Return {
                values,
                register: result_reg,
            } => {
                for &value in &self.code.operands[values.range()] {
                    self.put_in_register(value, result_reg, &protected)?;
                    protected.push(value);
                }
            }
            Terminator::Jump { .. } | Terminator::Halt => {}
        }
        self.record(layout.block, layout.terminator);
        Ok(())
    }

    fn fill_live(
        &mut self,
        point: Point,
        protected: &[VReg],
        reserved: RegSet,
    ) -> Result<(), String> {
        let live = &self.liveness.at[point.index()];
        if live.iter().all(|value| self.placement.get(value).is_some()) {
            return Ok(());
        }
        let mut unplaced: Vec<_> = live
            .iter()
            .filter(|&value| self.placement.get(value).is_none())
            .collect();
        unplaced.sort_by_cached_key(|&value| self.ahead(value));
        for value in unplaced {
            self.put_anywhere(value, protected, reserved)?;
        }
        Ok(())
    }

    fn expire_to(&mut self, point: Point) {
        let live = &self.liveness.at[point.index()];
        self.placement.keep(|value| live.contains(value));
    }

    fn put_anywhere(
        &mut self,
        value: VReg,
        protected: &[VReg],
        reserved: RegSet,
    ) -> Result<(), String> {
        let reserved = RegSet(reserved.0 | !self.homes[value.index()].0);
        if let Some(reg) = self.free_register_for(value, reserved) {
            return self.put_in_register(value, reg, protected);
        }
        // A register is worth taking from a value read further ahead.
        if let Some(reg) = self.furthest(protected, reserved)
            && self
                .register_occupant(reg)
                .is_some_and(|held| self.ahead(held) > self.ahead(value))
        {
            return self.put_in_register(value, reg, protected);
        }
        let spilled = self.spill(value)?;
        self.placement.set(value, spilled);
        Ok(())
    }

    /// The register a block already allocated holds the parameter `value`
    /// is handed to as, where it holds it in one: a value going round a loop
    /// made where the loop's start holds what it becomes goes round without
    /// moving.
    fn awaited(&self, value: VReg) -> Option<R> {
        self.handed_to[value.index()]
            .iter()
            .find_map(|&(target, param)| {
                let entry = self.liveness.blocks[target.index()].entry;
                let state = self.states[entry.index()].as_ref()?;
                match state.values.iter().find(|&&(held, _)| held == param)?.1 {
                    Location::Register(reg) => Some(reg),
                    Location::Spill(_) => None,
                }
            })
    }

    /// How far from where allocation is `value` is next read.
    fn ahead(&self, value: VReg) -> u32 {
        let (block, point) = self.now;
        self.distances.next(self.liveness, block, point, value)
    }

    /// Of the registers outside `reserved` holding none of `protected`, the
    /// one whose value is read furthest ahead.
    fn furthest(&self, protected: &[VReg], reserved: RegSet) -> Option<R> {
        self.code
            .registers
            .iter()
            .copied()
            .filter(|&candidate| {
                !reserved.contains(candidate)
                    && self
                        .register_occupant(candidate)
                        .is_none_or(|held| !protected.contains(&held))
            })
            .max_by_key(|&candidate| {
                self.register_occupant(candidate)
                    .map_or(u32::MAX, |held| self.ahead(held))
            })
    }

    fn put_in_some_register(
        &mut self,
        value: VReg,
        protected: &[VReg],
        reserved: RegSet,
    ) -> Result<R, String> {
        if let Some(Location::Register(reg)) = self.placement.get(value)
            && !reserved.contains(reg)
        {
            return Ok(reg);
        }
        let reg = self
            .free_register_for(value, reserved)
            .or_else(|| self.furthest(protected, reserved));
        let reg = reg.ok_or_else(|| "instruction needs more registers than exist".to_owned())?;
        self.put_in_register(value, reg, protected)?;
        Ok(reg)
    }

    fn put_in_register(&mut self, value: VReg, reg: R, protected: &[VReg]) -> Result<(), String> {
        if let Some(held) = self.register_occupant(reg)
            && held != value
        {
            if protected.contains(&held) {
                return Err(format!(
                    "fixed register {reg:?} holds two simultaneous operands"
                ));
            }
            // Where `value` is going is taken, so the other cannot wait there.
            let busy = self.busy;
            self.busy = RegSet(busy.0 | RegSet::of(&[reg]).0);
            self.displace(held)?;
            self.busy = busy;
        }
        self.placement.set(value, Location::Register(reg));
        Ok(())
    }

    fn spill(&mut self, value: VReg) -> Result<Location<R>, String> {
        let slot = if let Some(slot) = self.value_spills[value.index()] {
            slot
        } else {
            let next = &mut self.next_spill[self.owner.index()];
            let slot = SpillSlot(*next);
            *next = next
                .checked_add(1)
                .ok_or_else(|| "allocation has over 4G spill slots".to_owned())?;
            self.value_spills[value.index()] = Some(slot);
            slot
        };
        Ok(Location::Spill(slot))
    }

    /// Move what `reg` holds out of the way of the instruction being
    /// allocated.
    fn evacuate(&mut self, reg: R, except: Option<VReg>) -> Result<(), String> {
        if let Some(value) = self.register_occupant(reg)
            && Some(value) != except
        {
            self.displace(value)?;
        }
        Ok(())
    }

    /// Put `value` out of its register: into one the instruction being
    /// allocated leaves alone where one is free, and otherwise to memory.
    /// Either way it moves before the instruction writes the one it left.
    fn displace(&mut self, value: VReg) -> Result<(), String> {
        let moved = match self
            .free_register_for(value, RegSet(self.busy.0 | !self.homes[value.index()].0))
        {
            Some(free) => Location::Register(free),
            None => self.spill(value)?,
        };
        self.placement.set(value, moved);
        Ok(())
    }

    fn evict_reserved(&mut self, reserved: RegSet, protected: &[VReg]) -> Result<(), String> {
        for &reg in &self.code.registers {
            if reserved.contains(reg)
                && let Some(value) = self.register_occupant(reg)
            {
                if protected.contains(&value) {
                    return Err(format!(
                        "scratch register {reg:?} conflicts with an operand"
                    ));
                }
                let spilled = self.spill(value)?;
                self.placement.set(value, spilled);
            }
        }
        Ok(())
    }

    fn register_occupant(&self, reg: R) -> Option<VReg> {
        self.placement.occupant(reg)
    }

    fn free_register(&self, reserved: RegSet) -> Option<R> {
        self.code
            .registers
            .iter()
            .copied()
            .find(|&reg| !reserved.contains(reg) && self.register_occupant(reg).is_none())
    }

    /// A free register for `value`: one nothing it lives across disturbs
    /// where there is one, and otherwise any.
    fn free_register_for(&self, value: VReg, reserved: RegSet) -> Option<R> {
        let home = RegSet(reserved.0 | !self.homes[value.index()].0);
        let undisturbed = RegSet(home.0 | self.hazards[value.index()].0);
        self.free_register(undisturbed)
            .or_else(|| self.free_register(home))
            .or_else(|| self.free_register(reserved))
    }

    fn record(&mut self, block: BlockId, point: Point) {
        let values = self.liveness.at[point.index()]
            .iter()
            .map(|value| {
                (
                    value,
                    self.placement
                        .get(value)
                        .expect("every live value has a location"),
                )
            })
            .collect();
        self.states[point.index()] = Some(PointState { block, values });
    }

    fn plan_operand_moves(
        &mut self,
        instruction: InstId,
        operands: &[VReg],
        before: &[Option<Location<R>>],
        assigned: &[Location<R>],
    ) -> Result<(), String> {
        let mut copies = Vec::new();
        for ((&value, &source), &destination) in operands.iter().zip(before).zip(assigned) {
            let source = source
                .ok_or_else(|| format!("operand v{} has no incoming location", value.index()))?;
            let copy = ParallelCopy::between(place(source), place(destination));
            if !copies.contains(&copy) {
                copies.push(copy);
            }
        }
        let plan = parallel_copy::plan(&copies, Some(self.code.temporary(&copies)))?;
        self.operand_moves[instruction.index()] = Some(plan.moves().to_vec());
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "parameter and live-through transfers form one edge copy set"
    )]
    fn plan_edges(&mut self) -> Result<(), String> {
        for layout in &self.liveness.blocks {
            let terminator = self.code.blocks[layout.block].terminator;
            for (target, args) in edges(terminator) {
                let target_layout = &self.liveness.blocks[target.index()];
                let params = self.code.blocks[target].params;
                let parameters = &self.code.block_params[params.range()];
                let mut copies: Vec<_> = self.code.operands[args.range()]
                    .iter()
                    .zip(parameters)
                    .map(|(&source, &destination)| {
                        Ok(ParallelCopy::between(
                            place(self.location(layout.terminator, source)?),
                            place(self.location(target_layout.entry, destination)?),
                        ))
                    })
                    .collect::<Result<_, String>>()?;
                // A dominating value used directly in the successor is not
                // a block parameter, but independently allocated blocks may
                // still choose different locations for it.
                for value in self.liveness.at[target_layout.entry.index()].iter() {
                    if parameters.contains(&value) {
                        continue;
                    }
                    if !self.liveness.at[layout.terminator.index()].contains(value) {
                        return Err(format!(
                            "edge does not carry live-through v{}",
                            value.index()
                        ));
                    }
                    let copy = ParallelCopy::between(
                        place(self.location(layout.terminator, value)?),
                        place(self.location(target_layout.entry, value)?),
                    );
                    if !copies.contains(&copy) {
                        copies.push(copy);
                    }
                }
                let plan = parallel_copy::plan(&copies, Some(self.code.temporary(&copies)))?;
                self.edge_moves.push(EdgeMoves {
                    from: layout.block,
                    target,
                    moves: plan.moves().to_vec(),
                });
                self.edges = self
                    .edges
                    .checked_add(1)
                    .ok_or_else(|| "edge count overflow".to_owned())?;
                self.edge_cost.instructions = self
                    .edge_cost
                    .instructions
                    .checked_add(plan.cost().instructions)
                    .ok_or_else(|| "edge-copy instruction cost overflow".to_owned())?;
                self.edge_cost.memory_accesses = self
                    .edge_cost
                    .memory_accesses
                    .checked_add(plan.cost().memory_accesses)
                    .ok_or_else(|| "edge-copy memory cost overflow".to_owned())?;
            }
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "all selected operand and resource constraints are checked at their points"
    )]
    fn verify_states(&self) -> Result<(), String> {
        for (at, state) in self.states.iter().enumerate() {
            let state = state
                .as_ref()
                .ok_or_else(|| format!("allocation has no state at p{at}"))?;
            let live = &self.liveness.at[at];
            if state.values.len() != live.len()
                || state.values.iter().any(|(value, _)| !live.contains(*value))
            {
                return Err(format!("allocation state p{at} disagrees with liveness"));
            }
            for (left_at, &(left, left_location)) in state.values.iter().enumerate() {
                if let Location::Register(reg) = left_location
                    && state.values[..left_at].iter().any(|&(right, location)| {
                        right != left && location == Location::Register(reg)
                    })
                {
                    return Err(format!("allocation assigns {reg:?} twice at p{at}"));
                }
            }
        }
        for layout in &self.liveness.blocks {
            let block = self.code.blocks[layout.block];
            for (&param, &spec) in self.code.block_params[block.params.range()]
                .iter()
                .zip(&self.code.block_param_specs[block.params.range()])
            {
                if let Location::Register(reg) = self.location(layout.entry, param)?
                    && !spec.allowed.contains(reg)
                {
                    return Err("block parameter is in a disallowed register".to_owned());
                }
                match spec.constraint {
                    Constraint::Fixed(reg) => verify_constraint(
                        self.location(layout.entry, param)?,
                        Constraint::Fixed(reg),
                        None,
                    )?,
                    Constraint::Any => {}
                    Constraint::Tied(_) => {
                        return Err("block parameter has a tied constraint".to_owned());
                    }
                }
            }
            for points in &layout.instructions {
                let inst = self.code.instructions[points.instruction];
                let operands = &self.code.operands[inst.operands.range()];
                let def_offset = usize::from(inst.result.is_some());
                let allocated = self.operand_locations[points.instruction.index()]
                    .as_ref()
                    .ok_or_else(|| "instruction operands were not allocated".to_owned())?;
                if allocated.len() != operands.len() {
                    return Err("instruction operand allocation has the wrong arity".to_owned());
                }
                let mut tied = None;
                for (at, &location) in allocated.iter().enumerate() {
                    let spec = self
                        .code
                        .spec(&inst, def_offset + at)
                        .expect("verified operand");
                    let constraint = spec.constraint;
                    verify_allowed(location, spec.allowed)?;
                    verify_constraint(location, constraint, tied)?;
                    if constraint == Constraint::Tied(0) {
                        tied = Some(location);
                    }
                }
                let requirements = inst;
                for &reg in &self.code.registers {
                    if requirements.scratch.contains(reg)
                        && allocated.contains(&Location::Register(reg))
                    {
                        return Err(format!(
                            "scratch register {reg:?} is an instruction operand"
                        ));
                    }
                    if requirements.scratch.contains(reg)
                        && self.states[points.early.index()]
                            .as_ref()
                            .expect("point state")
                            .values
                            .iter()
                            .any(|&(_, location)| location == Location::Register(reg))
                    {
                        return Err(format!(
                            "scratch register {reg:?} is occupied at p{}",
                            points.early.index()
                        ));
                    }
                }
                if let Some(result) = inst.result {
                    let location = self.location(points.late, result)?;
                    let spec = self.code.spec(&inst, 0).expect("verified result");
                    verify_allowed(location, spec.allowed)?;
                    verify_constraint(location, spec.constraint, None)?;
                    if let Some(tied) = tied {
                        if location != tied {
                            return Err("tied input and result have different locations".to_owned());
                        }
                    } else {
                        let constraint = self
                            .code
                            .spec(&inst, 0)
                            .expect("selected result")
                            .constraint;
                        verify_constraint(location, constraint, None)?;
                    }
                }
                for &(value, location) in &self.states[points.late.index()]
                    .as_ref()
                    .expect("point state")
                    .values
                {
                    if Some(value) != inst.result
                        && matches!(location, Location::Register(reg) if requirements.clobbers.contains(reg))
                    {
                        return Err(format!(
                            "value v{} survives a clobber in a register",
                            value.index()
                        ));
                    }
                }
            }
            match block.terminator {
                Terminator::Branch {
                    condition, allowed, ..
                } => {
                    verify_allowed(self.location(layout.terminator, condition)?, allowed)?;
                }
                Terminator::Return {
                    values,
                    register: result_reg,
                } => {
                    for &value in &self.code.operands[values.range()] {
                        verify_constraint(
                            self.location(layout.terminator, value)?,
                            Constraint::Fixed(result_reg),
                            None,
                        )?;
                    }
                }
                Terminator::Jump { .. } | Terminator::Halt => {}
            }
        }
        Ok(())
    }

    fn location(&self, point: Point, value: VReg) -> Result<Location<R>, String> {
        self.states[point.index()]
            .as_ref()
            .and_then(|state| {
                state
                    .values
                    .iter()
                    .find_map(|&(held, location)| (held == value).then_some(location))
            })
            .ok_or_else(|| format!("v{} has no location at p{}", value.index(), point.index()))
    }
}

/// Check masks before allocation, including intersections imposed by ties.
#[expect(
    clippy::too_many_lines,
    reason = "validate register sets, fixed locations and ties together"
)]
fn verify_register_sets<R: Register>(code: &Code<R>) -> Result<(), String> {
    let mut file = RegSet::EMPTY;
    for &reg in &code.registers {
        if reg.number() >= 64 || file.contains(reg) {
            return Err("register file has duplicate or out-of-range numbers".to_owned());
        }
        file.0 |= RegSet::of(&[reg]).0;
    }
    if let Some(reg) = code.copies
        && (reg.number() >= 64 || file.contains(reg))
    {
        return Err("copy scratch must be outside the allocatable register file".to_owned());
    }
    let check = |spec: OperandSpec<R>| -> Result<(), String> {
        if spec.allowed.0 & file.0 == 0 {
            return Err("operand has no allowed allocatable register".to_owned());
        }
        if let Constraint::Fixed(reg) = spec.constraint
            && (reg.number() >= 64 || !file.contains(reg) || !spec.allowed.contains(reg))
        {
            return Err("fixed register is outside its allowed register set".to_owned());
        }
        Ok(())
    };
    for &spec in code.specs.iter().chain(&code.block_param_specs) {
        check(spec)?;
    }
    if code.block_param_specs.len() != code.block_params.len() {
        return Err("block parameters have the wrong specification count".to_owned());
    }
    for inst in &code.instructions {
        if code.specs.get(inst.specs.range()).is_none()
            || inst.specs.len() != inst.operands.len() + usize::from(inst.result.is_some())
        {
            return Err("instruction has the wrong specification count".to_owned());
        }
        for at in usize::from(inst.result.is_some())..inst.specs.len() {
            let spec = code.spec(inst, at).expect("operand spec");
            if let Constraint::Tied(_) = spec.constraint {
                let def = code.spec(inst, 0).ok_or("tie has no result")?;
                if inst.result.is_none() || spec.allowed.0 & def.allowed.0 & file.0 == 0 {
                    return Err("tied operand and result have no common register".to_owned());
                }
                if let Constraint::Fixed(reg) = def.constraint
                    && !spec.allowed.contains(reg)
                {
                    return Err("tied operand excludes the fixed result register".to_owned());
                }
            }
        }
    }
    for block in &code.blocks {
        if let Terminator::Branch { allowed, .. } = block.terminator
            && allowed.0 & file.0 == 0
        {
            return Err("branch has no allowed condition register".to_owned());
        }
    }
    Ok(())
}

fn verify_allowed<R: Register>(location: Location<R>, allowed: RegSet) -> Result<(), String> {
    if matches!(location, Location::Register(reg) if allowed.contains(reg)) {
        Ok(())
    } else {
        Err(format!(
            "allocation location {location:?} is outside {allowed:?}"
        ))
    }
}

/// Prefer a definition's bank, narrowed by uses when they agree. Conflicting
/// uses require transfers; they do not make a value impossible to allocate.
#[expect(
    clippy::too_many_lines,
    reason = "derive and coalesce bank preferences in one monotonic analysis"
)]
fn preferred_sets<R: Register>(code: &Code<R>) -> Vec<RegSet> {
    let file = RegSet::of(&code.registers);
    let mut definitions = vec![file; code.values];
    let mut uses = vec![file; code.values];
    for (&value, spec) in code.block_params.iter().zip(&code.block_param_specs) {
        definitions[value.index()].0 &= spec.allowed.0;
    }
    for inst in &code.instructions {
        let offset = usize::from(inst.result.is_some());
        if let Some(value) = inst.result {
            definitions[value.index()].0 &= code.spec(inst, 0).expect("result spec").allowed.0;
        }
        for (at, &value) in code.operands[inst.operands.range()].iter().enumerate() {
            uses[value.index()].0 &= code.spec(inst, offset + at).expect("use spec").allowed.0;
        }
    }
    for block in &code.blocks {
        if let Terminator::Branch {
            condition, allowed, ..
        } = block.terminator
        {
            uses[condition.index()].0 &= allowed.0;
        }
    }
    // A return names an exact register, not a bank. Keep that preference
    // in preferred_registers: narrowing a home to it would prevent a live
    // value from waiting in a callee-saved register across a call.
    let mut homes: Vec<_> = definitions
        .into_iter()
        .zip(uses)
        .map(|(definition, uses)| {
            let common = definition.0 & uses.0;
            if common == 0 {
                definition
            } else {
                RegSet(common)
            }
        })
        .collect();
    let mut reads = vec![0u8; code.values];
    for &value in &code.operands {
        reads[value.index()] = reads[value.index()].saturating_add(1);
    }
    for block in &code.blocks {
        if let Terminator::Branch { condition, .. } = block.terminator {
            reads[condition.index()] = reads[condition.index()].saturating_add(1);
        }
    }
    // Coalesce a single-use tied input into its consumer's preferred bank.
    // This includes representation-only copies; otherwise a word load before
    // a float bitcast would choose a GPR simply because its copy allows both.
    loop {
        let mut changed = false;
        for inst in code.instructions.iter().rev() {
            let Some(result) = inst.result else { continue };
            for (at, &input) in code.operands[inst.operands.range()].iter().enumerate() {
                if reads[input.index()] != 1
                    || code.spec(inst, at + 1).expect("use spec").constraint != Constraint::Tied(0)
                {
                    continue;
                }
                let common = homes[input.index()].0 & homes[result.index()].0;
                if common != 0 && common != homes[input.index()].0 {
                    homes[input.index()].0 = common;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    homes
}

/// Each value handed along an edge, by value: where to, as which parameter.
fn handed_to<R: Register>(code: &Code<R>) -> Vec<Vec<(BlockId, VReg)>> {
    let mut handed = vec![Vec::new(); code.values];
    for block in &code.blocks {
        for (target, args) in edges(block.terminator) {
            let params = &code.block_params[code.blocks[target].params.range()];
            for (&arg, &param) in code.operands[args.range()].iter().zip(params) {
                handed[arg.index()].push((target, param));
            }
        }
    }
    handed
}

/// The register each value is best defined in: the one every fixed use of
/// it, and every return of it, asks for, where they agree; none where they
/// differ or nothing asks.
fn preferred_registers<R: Register>(code: &Code<R>) -> Vec<Option<R>> {
    // `None` is asked for by nothing yet, `Some(None)` by uses that differ.
    let mut asked: Vec<Option<Option<R>>> = vec![None; code.values];
    let mut ask = |value: VReg, reg: Option<R>| {
        let held = &mut asked[value.index()];
        *held = match *held {
            None => Some(reg),
            Some(Some(before)) if Some(before) == reg => Some(Some(before)),
            Some(_) => Some(None),
        };
    };
    for inst in &code.instructions {
        let def_offset = usize::from(inst.result.is_some());
        for (at, &operand) in code.operands[inst.operands.range()].iter().enumerate() {
            match code.spec(inst, def_offset + at).map(|spec| spec.constraint) {
                Some(Constraint::Fixed(reg)) => ask(operand, Some(reg)),
                Some(_) => {}
                None => ask(operand, None),
            }
        }
    }
    for block in &code.blocks {
        let Terminator::Return {
            values,
            register: result,
        } = block.terminator
        else {
            continue;
        };
        for &value in &code.operands[values.range()] {
            ask(value, Some(result));
        }
    }
    let mut preferred: Vec<_> = asked.into_iter().map(Option::flatten).collect();
    tie_back(code, &mut preferred);
    preferred
}

/// Every register each value would have to leave: what an instruction it
/// is live across clobbers, uses as scratch, or takes an operand or answers
/// in, by a register of its own.
fn hazards<R: Register>(code: &Code<R>, liveness: &Liveness) -> Vec<RegSet> {
    let mut hazards = vec![RegSet::EMPTY; code.values];
    for layout in &liveness.blocks {
        for points in &layout.instructions {
            let inst = code.instructions[points.instruction];
            let requirements = inst;
            let mut disturbed = requirements.clobbers.0 | requirements.scratch.0;
            let count = usize::from(inst.result.is_some()) + inst.operands.range().len();
            for at in 0..count {
                if let Some(Constraint::Fixed(reg)) =
                    code.spec(&inst, at).map(|spec| spec.constraint)
                {
                    disturbed |= RegSet::of(&[reg]).0;
                }
            }
            let before = &liveness.at[points.early.index()];
            for value in liveness.at[points.late.index()].iter() {
                if before.contains(value) && Some(value) != inst.result {
                    hazards[value.index()].0 |= disturbed;
                }
            }
        }
    }
    tie_hazards(code, liveness, &mut hazards);
    hazards
}

/// What a block is handed, where it is not needed past the handing, is
/// where the block's parameter will be. Answers whether anything was
/// learned.
fn handed_hazards<R: Register>(
    code: &Code<R>,
    liveness: &Liveness,
    entries: &[Option<Point>],
    hazards: &mut [RegSet],
) -> bool {
    let mut learned = false;
    for block in &code.blocks {
        let edges: &[(BlockId, Range)] = &match block.terminator {
            Terminator::Jump { target, args } => vec![(target, args)],
            Terminator::Branch {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => vec![(then_target, then_args), (else_target, else_args)],
            Terminator::Return { .. } | Terminator::Halt => Vec::new(),
        };
        for &(target, args) in edges {
            let target_block = code.blocks[target];
            let params = &code.block_params[target_block.params.range()];
            let Some(entry) = entries[target.index()] else {
                continue;
            };
            for (&arg, &param) in code.operands[args.range()].iter().zip(params) {
                if arg == param || liveness.at[entry.index()].contains(arg) {
                    continue;
                }
                let joined = hazards[arg.index()].0 | hazards[param.index()].0;
                if joined != hazards[arg.index()].0 {
                    hazards[arg.index()].0 = joined;
                    learned = true;
                }
            }
        }
    }
    learned
}

/// An operand overwritten with the result where it is read for the last
/// time is where that result will be, so it had best avoid what the result
/// must.
fn tie_hazards<R: Register>(code: &Code<R>, liveness: &Liveness, hazards: &mut [RegSet]) {
    let mut entries = vec![None; code.blocks.len()];
    for layout in &liveness.blocks {
        entries[layout.block.index()] = Some(layout.entry);
    }
    loop {
        let mut learned = handed_hazards(code, liveness, &entries, hazards);
        for points in liveness
            .blocks
            .iter()
            .rev()
            .flat_map(|layout| layout.instructions.iter().rev())
        {
            let inst = code.instructions[points.instruction];
            let (Some(result), Some(&tied)) =
                (inst.result, code.operands[inst.operands.range()].first())
            else {
                continue;
            };
            if code.spec(&inst, 1).map(|spec| spec.constraint) != Some(Constraint::Tied(0))
                || liveness.at[points.late.index()].contains(tied)
            {
                continue;
            }
            let joined = hazards[tied.index()].0 | hazards[result.index()].0;
            if joined != hazards[tied.index()].0 {
                hazards[tied.index()].0 = joined;
                learned = true;
            }
        }
        if !learned {
            return;
        }
    }
}

/// An operand an instruction overwrites with its result is best held where
/// that result is, so nothing moves between them; and so is what a block is
/// handed, where its parameter is. Back along a run of such instructions and
/// jumps until nothing more is learned.
///
/// Even an operand read elsewhere too: what it is read by first is read
/// where it is, and only a preference is learned, which liveness overrides
/// where the two would meet.
fn tie_back<R: Register>(code: &Code<R>, preferred: &mut [Option<R>]) {
    loop {
        let mut learned = hand_back(code, preferred);
        for inst in code.instructions.iter().rev() {
            let Some(result) = inst.result else {
                continue;
            };
            let Some(&tied) = code.operands[inst.operands.range()].first() else {
                continue;
            };
            if code.spec(inst, 1).map(|spec| spec.constraint) != Some(Constraint::Tied(0))
                || preferred[tied.index()].is_some()
            {
                continue;
            }
            if let Some(reg) = preferred[result.index()] {
                preferred[tied.index()] = Some(reg);
                learned = true;
            }
        }
        if !learned {
            return;
        }
    }
}

/// What a jump hands a block is best held where the block's parameter is,
/// so the jump moves nothing. Answers whether anything was learned.
fn hand_back<R: Register>(code: &Code<R>, preferred: &mut [Option<R>]) -> bool {
    let mut learned = false;
    for block in &code.blocks {
        let edges = match block.terminator {
            Terminator::Jump { target, args } => [Some((target, args)), None],
            Terminator::Branch {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => [
                Some((then_target, then_args)),
                Some((else_target, else_args)),
            ],
            Terminator::Return { .. } | Terminator::Halt => [None, None],
        };
        for (target, args) in edges.into_iter().flatten() {
            let params = &code.block_params[code.blocks[target].params.range()];
            for (&arg, &param) in code.operands[args.range()].iter().zip(params) {
                if preferred[arg.index()].is_none()
                    && let Some(reg) = preferred[param.index()]
                {
                    preferred[arg.index()] = Some(reg);
                    learned = true;
                }
            }
        }
    }
    learned
}

/// The frame slots each function needs: past the last slot any of its
/// values or moves uses, and one at least where a move it makes goes through
/// the frame, if only for the temporary slot nought that breaks a cycle of
/// copies; none where it uses no frame.
///
/// Slots are numbered within a function, and a move is within one function,
/// so each function is sized by its own. The transitions at one point are
/// planned together once, as the moves made there.
fn function_spill_slots<R: Register>(
    code: &Code<R>,
    liveness: &Liveness,
    segments: &[Segment<R>],
    transitions: &[Transition<R>],
    operand_moves: &[Vec<CopyMove<R>>],
    edge_moves: &[EdgeMoves<R>],
) -> Result<Vec<u32>, String> {
    // Whether each function uses its frame, and the last slot it names.
    let mut frame: Vec<(bool, Option<u32>)> = vec![(false, None); function_count(code)];
    let owner_at = |point| owner_at(code, liveness, point);
    for segment in segments {
        let owner = owner_at(segment.start)
            .ok_or_else(|| "spill segment has no owning function".to_owned())?;
        frame_note(&mut frame, owner, place(segment.location));
    }
    // The transitions at each point are planned as the moves made there.
    for (point, copies) in &copies_at_points(transitions) {
        let owner =
            owner_at(*point).ok_or_else(|| "transition has no owning function".to_owned())?;
        let plan = parallel_copy::plan(copies, Some(code.temporary(copies)))
            .expect("allocation transition copies were already planned");
        note_moves(&mut frame, owner, plan.moves());
    }
    for layout in &liveness.blocks {
        let owner = code.blocks[layout.block].owner;
        for points in &layout.instructions {
            note_moves(
                &mut frame,
                owner,
                &operand_moves[points.instruction.index()],
            );
        }
    }
    for edge in edge_moves {
        note_moves(&mut frame, code.blocks[edge.from].owner, &edge.moves);
    }
    frame
        .into_iter()
        .map(|(uses, last)| {
            if !uses {
                return Ok(0);
            }
            last.unwrap_or(0)
                .checked_add(1)
                .ok_or_else(|| "spill frame exceeds 4G slots".to_owned())
        })
        .collect()
}

/// Each function's frame widened to hold every slot a value is written to
/// where it is made: one read back by nothing that names its slot is still
/// written there, and must not land on what lies past the spills.
fn widen_for_stores<R: Register>(
    code: &Code<R>,
    liveness: &Liveness,
    stores: &[(Point, R, SpillSlot)],
    spill_slots: &mut [u32],
) -> Result<(), String> {
    for &(point, _, SpillSlot(slot)) in stores {
        let owner = owner_at(code, liveness, point)
            .ok_or_else(|| "spill store has no owning function".to_owned())?;
        let needed = slot
            .checked_add(1)
            .ok_or_else(|| "spill frame exceeds 4G slots".to_owned())?;
        let held = &mut spill_slots[owner.index()];
        *held = (*held).max(needed);
    }
    Ok(())
}

/// How many functions an index by function source needs room for.
fn function_count<R>(code: &Code<R>) -> usize {
    code.functions
        .iter()
        .map(|function| function.source.index())
        .max()
        .map_or(0, |last| last + 1)
}

/// The function whose block holds `point`: blocks take consecutive runs of
/// points in order, so it is the last block beginning at or before it.
fn owner_at<R>(code: &Code<R>, liveness: &Liveness, point: Point) -> Option<FunctionId> {
    let after = liveness
        .blocks
        .partition_point(|layout| layout.entry.index() <= point.index());
    let layout = &liveness.blocks[after.checked_sub(1)?];
    (point.index() <= layout.terminator.index()).then(|| code.blocks[layout.block].owner)
}

/// The copies each transition makes, gathered by the point they are made
/// at, in the order the points first appear.
fn copies_at_points<R: Register>(
    transitions: &[Transition<R>],
) -> Vec<(Point, Vec<ParallelCopy<R>>)> {
    let mut at_point: Vec<(Point, Vec<ParallelCopy<R>>)> = Vec::new();
    let mut found: HashMap<usize, usize> = HashMap::new();
    for transition in transitions {
        let copy = ParallelCopy::between(place(transition.from), place(transition.to));
        if let Some(&group) = found.get(&transition.at.index()) {
            at_point[group].1.push(copy);
        } else {
            found.insert(transition.at.index(), at_point.len());
            at_point.push((transition.at, vec![copy]));
        }
    }
    at_point
}

/// Note that `owner` uses its frame wherever `moves` go through it.
fn note_moves<R: Register>(
    frame: &mut [(bool, Option<u32>)],
    owner: FunctionId,
    moves: &[CopyMove<R>],
) {
    for movement in moves {
        let CopySource::Place(source) = movement.source();
        frame_note(frame, owner, source);
        frame_note(frame, owner, movement.destination());
    }
}

/// Note that `owner` uses its frame at `place`, when `place` is in it.
fn frame_note<R: Copy>(frame: &mut [(bool, Option<u32>)], owner: FunctionId, place: Place<R>) {
    let held = &mut frame[owner.index()];
    if let Place::Frame(slot) = place {
        held.0 = true;
        held.1 = Some(
            held.1
                .map_or_else(|| slot.number(), |last| last.max(slot.number())),
        );
    }
}

fn collect_instruction_data<T>(
    data: Vec<Option<Vec<T>>>,
    what: &str,
) -> Result<Vec<Vec<T>>, String> {
    data.into_iter()
        .enumerate()
        .map(|(at, held)| held.ok_or_else(|| format!("instruction i{at} has no {what}")))
        .collect()
}

fn verify_constraint<R: Register>(
    location: Location<R>,
    constraint: Constraint<R>,
    tied: Option<Location<R>>,
) -> Result<(), String> {
    let valid = match constraint {
        Constraint::Any => matches!(location, Location::Register(_)),
        Constraint::Fixed(reg) => location == Location::Register(reg),
        Constraint::Tied(0) => {
            matches!(location, Location::Register(_)) && tied.is_none_or(|tied| tied == location)
        }
        Constraint::Tied(_) => false,
    };
    if valid {
        Ok(())
    } else {
        Err(format!(
            "allocation location {location:?} violates {constraint:?}"
        ))
    }
}

/// Each block's predecessors, with the arguments each hands it.
fn predecessors<R: Register>(code: &Code<R>, liveness: &Liveness) -> Vec<Vec<(BlockId, Range)>> {
    let mut found = vec![Vec::new(); code.blocks.len()];
    for layout in &liveness.blocks {
        for (target, args) in edges(code.blocks[layout.block].terminator) {
            found[target.index()].push((layout.block, args));
        }
    }
    found
}

fn edges<R: Copy>(terminator: Terminator<R>) -> Vec<(BlockId, Range)> {
    match terminator {
        Terminator::Jump { target, args } => vec![(target, args)],
        Terminator::Branch {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => vec![(then_target, then_args), (else_target, else_args)],
        Terminator::Return { .. } | Terminator::Halt => Vec::new(),
    }
}

#[must_use]
pub const fn place<R: Register>(location: Location<R>) -> Place<R> {
    match location {
        Location::Register(reg) => Place::Register(reg),
        Location::Spill(SpillSlot(slot)) => Place::Frame(FrameSlot::at(slot)),
    }
}

/// Each value's runs of one location, and the moves between them.
type Segmented<R> = (Vec<Segment<R>>, Vec<Transition<R>>);

/// Each value's runs of consecutive points in one block and one location,
/// ordered by value and then by start, and the transitions between a
/// value's runs, ordered by the point each is made at.
fn build_segments<R: Register>(
    states: &[Option<PointState<R>>],
    values: usize,
) -> Result<Segmented<R>, String> {
    let mut segments: Vec<Segment<R>> = Vec::new();
    let mut transitions = Vec::new();
    // Each value's latest segment, the only one that can run on into the
    // next point.
    let mut latest: Vec<Option<usize>> = vec![None; values];
    for (point_at, state) in states.iter().enumerate() {
        let Some(state) = state else { continue };
        let point = Point::at(point_at)?;
        let same_block = point_at > 0
            && states[point_at - 1]
                .as_ref()
                .is_some_and(|before| before.block == state.block);
        for &(value, location) in &state.values {
            let previous = latest[value.index()]
                .filter(|&at| same_block && segments[at].end.index() == point_at);
            if let Some(previous) = previous
                && segments[previous].location == location
            {
                segments[previous].end = Point::at(point_at + 1)?;
                continue;
            }
            if let Some(previous) = previous {
                transitions.push(Transition {
                    value,
                    at: point,
                    from: segments[previous].location,
                    to: location,
                });
            }
            latest[value.index()] = Some(segments.len());
            segments.push(Segment {
                value,
                start: point,
                end: Point::at(point_at + 1)?,
                location,
            });
        }
    }
    segments.sort_unstable_by_key(|segment| (segment.value, segment.start.0));
    Ok((segments, transitions))
}

impl<R: Register> Allocation<R> {
    /// The values written to memory where they are made at `point`, each
    /// from its register.
    pub fn stores_at(&self, point: Point) -> impl Iterator<Item = (R, SpillSlot)> + '_ {
        let start = self.stores.partition_point(|&(at, ..)| at.0 < point.0);
        self.stores[start..]
            .iter()
            .take_while(move |&&(at, ..)| at == point)
            .map(|&(_, reg, slot)| (reg, slot))
    }

    /// Whether a move into `slot` writes nothing new: every slot but the
    /// one breaking a cycle of moves is a value's, written where the value
    /// was made. A move defining a block's parameter is not such a move.
    #[must_use]
    pub const fn elides(slot: FrameSlot) -> bool {
        slot.number() != 0
    }

    /// The transitions made at `point`.
    #[must_use]
    pub fn transitions_at(&self, point: Point) -> &[Transition<R>] {
        let start = self
            .transitions
            .partition_point(|transition| transition.at.0 < point.0);
        let end = self
            .transitions
            .partition_point(|transition| transition.at.0 <= point.0);
        &self.transitions[start..end]
    }

    /// Where `value` is at `point`, if it is live there.
    #[must_use]
    pub fn location(&self, point: Point, value: VReg) -> Option<Location<R>> {
        let after = self
            .segments
            .partition_point(|segment| (segment.value, segment.start.0) <= (value, point.0));
        let segment = self.segments[..after].last()?;
        (segment.value == value && point.0 < segment.end.0).then_some(segment.location)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "the allocation boundary verifies ranges, transitions, moves, and costs"
    )]
    fn verify(&self, code: &Code<R>, liveness: &Liveness) -> Result<(), String> {
        if self.operand_locations.len() != code.instructions.len()
            || self.operand_moves.len() != code.instructions.len()
        {
            return Err("allocation omitted instruction operands".to_owned());
        }
        for (inst, locations) in code.instructions.iter().zip(&self.operand_locations) {
            if locations.len() != inst.operands.len() {
                return Err("allocation has the wrong operand-location arity".to_owned());
            }
        }
        for segment in &self.segments {
            if segment.start.index() >= segment.end.index()
                || segment.end.index() > liveness.at.len()
                || segment.value.index() >= code.values
            {
                return Err("allocation contains an invalid live segment".to_owned());
            }
            if let Location::Spill(SpillSlot(slot)) = segment.location {
                let owner = owner_at(code, liveness, segment.start)
                    .ok_or_else(|| "spill segment has no owning function".to_owned())?;
                if self
                    .spill_slots
                    .get(owner.index())
                    .is_none_or(|&slots| slot >= slots)
                {
                    return Err("allocation refers past its spill frame".to_owned());
                }
            }
        }
        for &(point, _, SpillSlot(slot)) in &self.stores {
            let owner = owner_at(code, liveness, point)
                .ok_or_else(|| "spill store has no owning function".to_owned())?;
            if self
                .spill_slots
                .get(owner.index())
                .is_none_or(|&slots| slot >= slots)
            {
                return Err("allocation stores past its spill frame".to_owned());
            }
        }
        if !self
            .transitions
            .is_sorted_by_key(|transition| transition.at.0)
        {
            return Err("allocation transitions are out of point order".to_owned());
        }
        for transition in &self.transitions {
            if transition.from == transition.to
                || transition.at.index() >= liveness.at.len()
                || transition.value.index() >= code.values
            {
                return Err("allocation contains an invalid split transition".to_owned());
            }
        }
        if usize::try_from(self.edges).expect("edge count fits") != self.edge_moves.len() {
            return Err("allocation omitted edge move plans".to_owned());
        }
        let mut cost = TransitionCost::default();
        for movement in self.edge_moves.iter().flat_map(|edge| &edge.moves) {
            let requirements = movement.requirements();
            cost.instructions = cost
                .instructions
                .checked_add(u32::from(requirements.instructions))
                .ok_or_else(|| "verified edge instruction cost overflow".to_owned())?;
            cost.memory_accesses = cost
                .memory_accesses
                .checked_add(
                    u32::from(requirements.memory_reads) + u32::from(requirements.memory_writes),
                )
                .ok_or_else(|| "verified edge memory cost overflow".to_owned())?;
        }
        if cost != self.edge_cost {
            return Err("allocation edge cost disagrees with its moves".to_owned());
        }
        if self.edges > u32::try_from(liveness.blocks.len().saturating_mul(2)).unwrap_or(u32::MAX) {
            return Err("allocation has too many CFG edges".to_owned());
        }
        Ok(())
    }
}

impl<R: Register> From<parallel_copy::PlanError<R>> for String {
    fn from(error: parallel_copy::PlanError<R>) -> Self {
        format!("edge copy cannot be planned: {error:?}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::Range;

    /// A machine of two registers, nothing else known of it.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Two {
        A,
        B,
    }

    impl Register for Two {
        fn number(self) -> u8 {
            match self {
                Self::A => 0,
                Self::B => 1,
            }
        }
    }

    const ANY: OperandSpec<Two> = OperandSpec {
        role: Role::Use,
        timing: Timing::Early,
        constraint: Constraint::Any,
        allowed: RegSet(u64::MAX),
    };

    /// `count` values made, then each read once, last first, and nothing
    /// answered: more live at once than two registers hold.
    fn pressed(count: usize) -> Code<Two> {
        let reads: Vec<_> = (0..count).rev().collect();
        made_then_read(count, &reads)
    }

    /// `count` values made, then each read once in the order `reads` gives.
    #[expect(
        clippy::too_many_lines,
        reason = "one straight-line function built by hand"
    )]
    fn made_then_read(count: usize, reads: &[usize]) -> Code<Two> {
        let mut code = Code {
            values: count,
            operands: Vec::new(),
            instructions: Pool::default(),
            specs: Vec::new(),
            order: Vec::new(),
            block_params: Vec::new(),
            block_param_specs: Vec::new(),
            blocks: Pool::default(),
            functions: vec![Function {
                source: FunctionId::at(0),
                entry: BlockId::at(0),
            }],
            registers: vec![Two::A, Two::B],
            copies: None,
        };
        let make = |code: &mut Code<Two>, operands: &[VReg], result: Option<VReg>| {
            let start = code.operands.len();
            code.operands.extend_from_slice(operands);
            let specs = code.specs.len();
            let count = usize::from(result.is_some()) + operands.len();
            code.specs.extend((0..count).map(|_| ANY));
            let id = code.instructions.push(Inst {
                operands: Range::of(start, operands.len()),
                result,
                specs: Range::of(specs, count),
                scratch: RegSet::EMPTY,
                clobbers: RegSet::EMPTY,
            });
            code.order.push(id);
        };
        for at in 0..count {
            make(&mut code, &[], Some(VReg::at(at)));
        }
        for &at in reads {
            make(&mut code, &[VReg::at(at)], None);
        }
        code.blocks.push(Block {
            owner: FunctionId::at(0),
            params: Range::EMPTY,
            instructions: Range::of(0, code.order.len()),
            terminator: Terminator::Halt,
        });
        code
    }

    #[test]
    fn a_machine_of_two_registers_spills_what_it_cannot_hold() {
        let (_, allocation) = allocate(&pressed(5)).unwrap();
        assert!(
            allocation
                .segments
                .iter()
                .any(|segment| matches!(segment.location, Location::Spill(_)))
        );
        let (_, allocation) = allocate(&pressed(2)).unwrap();
        assert!(
            allocation
                .segments
                .iter()
                .all(|segment| matches!(segment.location, Location::Register(_)))
        );
    }

    #[test]
    fn what_is_read_furthest_ahead_waits_in_memory() {
        let (_, allocation) = allocate(&made_then_read(3, &[1, 2, 0])).unwrap();
        let spilled = |value: usize| {
            allocation.segments.iter().any(|segment| {
                segment.value == VReg::at(value) && matches!(segment.location, Location::Spill(_))
            })
        };
        assert!(spilled(0));
        assert!(!spilled(1));
    }
}
