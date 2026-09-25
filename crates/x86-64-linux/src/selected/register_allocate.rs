//! Segmented liveness and split allocation for selected x86 code.
//!
//! The allocator walks each CFG block in target instruction order, keeps
//! profitable live values in registers, spills under pressure, and splits at
//! fixed operands, ties, scratch reservations, and implicit clobbers. Its
//! verified output is the symbolic instruction sequence consumed by encoding.

mod lower;

use super::{BlockId, Constraint, InstId, Reg, RegSet, Selected, Terminator, VReg, successors};
use crate::machine::FrameSlot;
use crate::parallel_copy::{
    self, Copy as ParallelCopy, CopySource, Move as CopyMove, Place, TransitionCost,
};
use faun_core::index::{BitSet, Range};
use faun_core::ir::FunctionId;

const REGISTERS: [Reg; 8] = [
    Reg::Rax,
    Reg::Rcx,
    Reg::Rdx,
    Reg::Rsi,
    Reg::Rdi,
    Reg::R8,
    Reg::R9,
    Reg::R10,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Point(u32);

impl Point {
    fn at(index: usize) -> Result<Self, String> {
        Ok(Self(
            u32::try_from(index).map_err(|_| "x86 selected function has over 4G points")?,
        ))
    }

    fn index(self) -> usize {
        usize::try_from(self.0).expect("an allocation point that fits")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SpillSlot(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Location {
    Register(Reg),
    Spill(SpillSlot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Segment {
    value: VReg,
    start: Point,
    end: Point,
    location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Transition {
    value: VReg,
    at: Point,
    from: Location,
    to: Location,
}

#[derive(Debug)]
struct EdgeMoves {
    from: BlockId,
    target: BlockId,
    moves: Vec<CopyMove>,
}

#[derive(Debug)]
pub(super) struct Allocation {
    segments: Vec<Segment>,
    transitions: Vec<Transition>,
    operand_locations: Vec<Vec<Location>>,
    operand_moves: Vec<Vec<CopyMove>>,
    edge_moves: Vec<EdgeMoves>,
    edge_cost: TransitionCost,
    edges: u32,
    spill_slots: Vec<u32>,
}

#[derive(Debug)]
struct InstPoints {
    instruction: InstId,
    early: Point,
    late: Point,
}

#[derive(Debug)]
struct BlockPoints {
    block: BlockId,
    entry: Point,
    instructions: Vec<InstPoints>,
    terminator: Point,
}

#[derive(Debug)]
pub(super) struct Liveness {
    at: Vec<BitSet<VReg>>,
    blocks: Vec<BlockPoints>,
}

#[derive(Debug)]
struct PointState {
    block: BlockId,
    values: Vec<(VReg, Location)>,
}

pub(super) fn allocate(
    selected: &Selected,
    entry: FunctionId,
) -> Result<crate::machine::Allocated, String> {
    let liveness = Liveness::build(selected)?;
    let allocation = Allocator::new(selected, &liveness, entry)?.run()?;
    allocation.verify(selected, &liveness)?;
    lower::lower(selected, &liveness, &allocation, entry)
}

impl Liveness {
    #[expect(
        clippy::too_many_lines,
        reason = "point numbering, CFG dataflow, and per-point liveness form one analysis"
    )]
    fn build(selected: &Selected) -> Result<Self, String> {
        let values = selected.widths.len();
        let mut cursor = 0;
        let mut blocks = Vec::with_capacity(selected.blocks.len());
        for (id, block) in selected.blocks.iter_enumerated() {
            let entry = Point::at(cursor)?;
            cursor += 1;
            let mut instructions = Vec::with_capacity(block.instructions.len());
            for &instruction in &selected.order[block.instructions.range()] {
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

        let (uses, defs) = block_uses_and_defs(selected, values);
        let mut live_in = vec![BitSet::new(values); selected.blocks.len()];
        let mut live_out = live_in.clone();
        loop {
            let previous_in = live_in.clone();
            let previous_out = live_out.clone();
            for (at, block) in selected.blocks.iter().enumerate().rev() {
                let mut outgoing = BitSet::new(values);
                for successor in successors(block.terminator).into_iter().flatten() {
                    outgoing.union_with(&previous_in[successor.index()]);
                }
                let mut incoming = outgoing.clone();
                incoming.subtract(&defs[at]);
                incoming.union_with(&uses[at]);
                live_out[at] = outgoing;
                live_in[at] = incoming;
            }
            if live_in == previous_in && live_out == previous_out {
                break;
            }
        }

        let mut at = vec![BitSet::new(values); cursor];
        for layout in &blocks {
            let block = selected.blocks[layout.block];
            let mut live = live_out[layout.block.index()].clone();
            add_terminator_uses(selected, block.terminator, &mut live);
            at[layout.terminator.index()].clone_from(&live);
            for points in layout.instructions.iter().rev() {
                let inst = selected.instructions[points.instruction];
                let mut late = live.clone();
                if let Some(result) = inst.result {
                    late.insert(result);
                    live.remove(result);
                }
                at[points.late.index()] = late;
                for &operand in &selected.operands[inst.operands.range()] {
                    live.insert(operand);
                }
                at[points.early.index()].clone_from(&live);
            }
            let mut entry = live;
            for &param in &selected.block_params[block.params.range()] {
                entry.remove(param);
                entry.insert(param);
            }
            at[layout.entry.index()] = entry;
        }
        Ok(Self { at, blocks })
    }
}

fn block_uses_and_defs(
    selected: &Selected,
    values: usize,
) -> (Vec<BitSet<VReg>>, Vec<BitSet<VReg>>) {
    let mut uses = vec![BitSet::new(values); selected.blocks.len()];
    let mut defs = uses.clone();
    for (at, block) in selected.blocks.iter().enumerate() {
        for &param in &selected.block_params[block.params.range()] {
            defs[at].insert(param);
        }
        for &instruction in &selected.order[block.instructions.range()] {
            let inst = selected.instructions[instruction];
            for &operand in &selected.operands[inst.operands.range()] {
                if !defs[at].contains(operand) {
                    uses[at].insert(operand);
                }
            }
            if let Some(result) = inst.result {
                defs[at].insert(result);
            }
        }
        add_terminator_uses_if_undefined(selected, block.terminator, &defs[at], &mut uses[at]);
    }
    (uses, defs)
}

fn add_terminator_uses_if_undefined(
    selected: &Selected,
    terminator: Terminator,
    defs: &BitSet<VReg>,
    uses: &mut BitSet<VReg>,
) {
    visit_terminator_values(selected, terminator, |value| {
        if !defs.contains(value) {
            uses.insert(value);
        }
    });
}

fn add_terminator_uses(selected: &Selected, terminator: Terminator, live: &mut BitSet<VReg>) {
    visit_terminator_values(selected, terminator, |value| live.insert(value));
}

fn visit_terminator_values(
    selected: &Selected,
    terminator: Terminator,
    mut visit: impl FnMut(VReg),
) {
    match terminator {
        Terminator::Jump { args, .. } => {
            for &value in &selected.operands[args.range()] {
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
            for &value in selected.operands[then_args.range()]
                .iter()
                .chain(&selected.operands[else_args.range()])
            {
                visit(value);
            }
        }
        Terminator::Return { values } => {
            for &value in &selected.operands[values.range()] {
                visit(value);
            }
        }
        Terminator::Halt => {}
    }
}

struct Allocator<'a> {
    selected: &'a Selected,
    liveness: &'a Liveness,
    states: Vec<Option<PointState>>,
    locations: Vec<Option<Location>>,
    operand_locations: Vec<Option<Vec<Location>>>,
    operand_moves: Vec<Option<Vec<CopyMove>>>,
    edge_moves: Vec<EdgeMoves>,
    edge_cost: TransitionCost,
    edges: u32,
    entry: FunctionId,
    value_spills: Vec<Option<SpillSlot>>,
    next_spill: u32,
}

impl<'a> Allocator<'a> {
    fn new(
        selected: &'a Selected,
        liveness: &'a Liveness,
        entry: FunctionId,
    ) -> Result<Self, String> {
        if selected.widths.len() > usize::try_from(u32::MAX).expect("u32 fits usize") {
            return Err("x86 selected allocation has over 4G values".to_owned());
        }
        Ok(Self {
            selected,
            liveness,
            states: (0..liveness.at.len()).map(|_| None).collect(),
            locations: vec![None; selected.widths.len()],
            operand_locations: vec![None; selected.instructions.len()],
            operand_moves: vec![None; selected.instructions.len()],
            edge_moves: Vec::new(),
            edge_cost: TransitionCost::default(),
            edges: 0,
            entry,
            value_spills: vec![None; selected.widths.len()],
            // Slot zero is reserved for breaking parallel-copy cycles.
            next_spill: 1,
        })
    }

    fn run(mut self) -> Result<Allocation, String> {
        for layout in &self.liveness.blocks {
            self.locations.fill(None);
            self.allocate_entry(layout)?;
            for points in &layout.instructions {
                self.allocate_instruction(points)?;
            }
            self.allocate_terminator(layout)?;
        }
        self.plan_edges()?;
        self.verify_states()?;
        let (segments, transitions) = build_segments(&self.states)?;
        let operand_locations =
            collect_instruction_data(self.operand_locations, "operand allocation")?;
        let operand_moves = collect_instruction_data(self.operand_moves, "operand move plan")?;
        let total_spill_slots =
            required_spill_slots(&segments, &transitions, &operand_moves, &self.edge_moves)?;
        let spill_slots = function_spill_slots(
            self.selected,
            self.liveness,
            &transitions,
            &operand_moves,
            &self.edge_moves,
            total_spill_slots,
        );
        Ok(Allocation {
            segments,
            transitions,
            operand_locations,
            operand_moves,
            edge_moves: self.edge_moves,
            edge_cost: self.edge_cost,
            edges: self.edges,
            spill_slots,
        })
    }

    fn allocate_entry(&mut self, layout: &BlockPoints) -> Result<(), String> {
        let block = self.selected.blocks[layout.block];
        self.expire_to(layout.entry);
        let params = &self.selected.block_params[block.params.range()];
        let specs = &self.selected.block_param_specs[block.params.range()];
        let mut protected = Vec::new();
        for (&value, &spec) in params.iter().zip(specs) {
            if let Constraint::Fixed(reg) = spec.constraint {
                self.put_in_register(value, reg, &protected)?;
                protected.push(value);
            }
        }
        for &value in params {
            if self.locations[value.index()].is_none() {
                self.put_anywhere(value, &protected, RegSet(0))?;
                protected.push(value);
            }
        }
        self.fill_live(layout.entry, &protected, RegSet(0))?;
        self.record(layout.block, layout.entry);
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "early uses, clobbers, and late definitions are allocated as one instruction"
    )]
    fn allocate_instruction(&mut self, points: &InstPoints) -> Result<(), String> {
        let inst = self.selected.instructions[points.instruction];
        self.expire_to(points.early);
        self.fill_live(points.early, &[], inst.opcode.requirements().scratch)?;
        let before = self.locations.clone();
        let operands = &self.selected.operands[inst.operands.range()];
        let def_offset = usize::from(inst.result.is_some());
        let mut protected = Vec::new();
        let mut tied = None;
        let mut assigned = vec![None; operands.len()];

        for (at, &value) in operands.iter().enumerate() {
            let spec = inst
                .operand_spec(def_offset + at)
                .ok_or_else(|| "x86 selected use has no allocation constraint".to_owned())?;
            if let Constraint::Fixed(reg) = spec.constraint {
                self.put_in_register(value, reg, &protected)?;
                assigned[at] = Some(Location::Register(reg));
                protected.push(value);
            }
        }
        for (at, &value) in operands.iter().enumerate() {
            let spec = inst
                .operand_spec(def_offset + at)
                .expect("verified operand");
            match spec.constraint {
                Constraint::Tied(0) => {
                    let reg = self.put_in_some_register(
                        value,
                        &protected,
                        inst.opcode.requirements().scratch,
                    )?;
                    tied = Some(reg);
                    assigned[at] = Some(Location::Register(reg));
                    protected.push(value);
                }
                Constraint::Any => {
                    let reg = self.put_in_some_register(
                        value,
                        &protected,
                        inst.opcode.requirements().scratch,
                    )?;
                    assigned[at] = Some(Location::Register(reg));
                    protected.push(value);
                }
                Constraint::Fixed(_) => {}
                Constraint::Tied(other) => {
                    return Err(format!(
                        "x86 allocator does not support tie to operand {other}"
                    ));
                }
            }
        }
        let assigned = assigned
            .into_iter()
            .map(|location| location.ok_or_else(|| "x86 use has no allocated location".to_owned()))
            .collect::<Result<Vec<_>, _>>()?;
        self.plan_operand_moves(points.instruction, operands, &before, &assigned)?;
        self.operand_locations[points.instruction.index()] = Some(assigned);
        self.evict_reserved(inst.opcode.requirements().scratch, &protected)?;
        self.record(self.point_block(points.early), points.early);

        self.expire_to(points.late);
        let requirements = inst.opcode.requirements();
        let result = inst.result;
        for reg in REGISTERS {
            if requirements.effects.clobbers.contains(reg) || requirements.scratch.contains(reg) {
                self.spill_register(reg, result)?;
            }
        }
        if let Some(value) = result {
            let spec = inst
                .operand_spec(0)
                .ok_or_else(|| "x86 selected result has no allocation constraint".to_owned())?;
            if let Some(reg) = tied {
                self.put_in_register(value, reg, &[])?;
            } else {
                match spec.constraint {
                    Constraint::Fixed(reg) => self.put_in_register(value, reg, &[])?,
                    Constraint::Any => {
                        if let Some(reg) = self.preferred_register(value)
                            && !requirements.scratch.contains(reg)
                        {
                            self.put_in_register(value, reg, &[])?;
                        } else {
                            self.put_in_some_register(value, &[], requirements.scratch)?;
                        }
                    }
                    Constraint::Tied(other) => {
                        return Err(format!("x86 allocator does not support result tie {other}"));
                    }
                }
            }
        }
        self.fill_live(
            points.late,
            &result.into_iter().collect::<Vec<_>>(),
            requirements.scratch,
        )?;
        self.record(self.point_block(points.late), points.late);
        Ok(())
    }

    fn preferred_register(&self, value: VReg) -> Option<Reg> {
        let mut preferred = None;
        for inst in &self.selected.instructions {
            let def_offset = usize::from(inst.result.is_some());
            for (at, &operand) in self.selected.operands[inst.operands.range()]
                .iter()
                .enumerate()
            {
                if operand != value {
                    continue;
                }
                let Constraint::Fixed(reg) = inst.operand_spec(def_offset + at)?.constraint else {
                    continue;
                };
                if preferred.is_some_and(|held| held != reg) {
                    return None;
                }
                preferred = Some(reg);
            }
        }
        for block in &self.selected.blocks {
            let Terminator::Return { values } = block.terminator else {
                continue;
            };
            if self.selected.operands[values.range()].contains(&value) {
                let result_reg = if block.owner == self.entry {
                    Reg::Rdi
                } else {
                    Reg::Rax
                };
                if preferred.is_some_and(|held| held != result_reg) {
                    return None;
                }
                preferred = Some(result_reg);
            }
        }
        preferred
    }

    fn allocate_terminator(&mut self, layout: &BlockPoints) -> Result<(), String> {
        let block = self.selected.blocks[layout.block];
        self.expire_to(layout.terminator);
        self.fill_live(layout.terminator, &[], RegSet(0))?;
        let mut protected = Vec::new();
        match block.terminator {
            Terminator::Branch { condition, .. } => {
                self.put_in_some_register(condition, &protected, RegSet(0))?;
                protected.push(condition);
            }
            Terminator::Return { values } => {
                let result_reg = if block.owner == self.entry {
                    Reg::Rdi
                } else {
                    Reg::Rax
                };
                for &value in &self.selected.operands[values.range()] {
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
        for value in self.liveness.at[point.index()].iter() {
            if self.locations[value.index()].is_none() {
                self.put_anywhere(value, protected, reserved)?;
            }
        }
        Ok(())
    }

    fn expire_to(&mut self, point: Point) {
        for (at, location) in self.locations.iter_mut().enumerate() {
            if location.is_some() && !self.liveness.at[point.index()].contains(VReg::at(at)) {
                *location = None;
            }
        }
    }

    fn put_anywhere(
        &mut self,
        value: VReg,
        protected: &[VReg],
        reserved: RegSet,
    ) -> Result<(), String> {
        if let Some(reg) = self.free_register(reserved) {
            self.put_in_register(value, reg, protected)
        } else {
            self.locations[value.index()] = Some(self.spill(value)?);
            Ok(())
        }
    }

    fn put_in_some_register(
        &mut self,
        value: VReg,
        protected: &[VReg],
        reserved: RegSet,
    ) -> Result<Reg, String> {
        if let Some(Location::Register(reg)) = self.locations[value.index()]
            && !reserved.contains(reg)
        {
            return Ok(reg);
        }
        let reg = self.free_register(reserved).or_else(|| {
            REGISTERS.into_iter().rev().find(|&candidate| {
                !reserved.contains(candidate)
                    && self
                        .register_occupant(candidate)
                        .is_none_or(|held| !protected.contains(&held))
            })
        });
        let reg =
            reg.ok_or_else(|| "x86 instruction needs more registers than exist".to_owned())?;
        self.put_in_register(value, reg, protected)?;
        Ok(reg)
    }

    fn put_in_register(&mut self, value: VReg, reg: Reg, protected: &[VReg]) -> Result<(), String> {
        if let Some(held) = self.register_occupant(reg)
            && held != value
        {
            if protected.contains(&held) {
                return Err(format!(
                    "x86 fixed register {reg:?} holds two simultaneous operands"
                ));
            }
            self.locations[held.index()] = Some(self.spill(held)?);
        }
        self.locations[value.index()] = Some(Location::Register(reg));
        Ok(())
    }

    fn spill(&mut self, value: VReg) -> Result<Location, String> {
        let slot = if let Some(slot) = self.value_spills[value.index()] {
            slot
        } else {
            let slot = SpillSlot(self.next_spill);
            self.next_spill = self
                .next_spill
                .checked_add(1)
                .ok_or_else(|| "x86 allocation has over 4G spill slots".to_owned())?;
            self.value_spills[value.index()] = Some(slot);
            slot
        };
        Ok(Location::Spill(slot))
    }

    fn spill_register(&mut self, reg: Reg, except: Option<VReg>) -> Result<(), String> {
        if let Some(value) = self.register_occupant(reg)
            && Some(value) != except
        {
            self.locations[value.index()] = Some(self.spill(value)?);
        }
        Ok(())
    }

    fn evict_reserved(&mut self, reserved: RegSet, protected: &[VReg]) -> Result<(), String> {
        for reg in REGISTERS {
            if reserved.contains(reg)
                && let Some(value) = self.register_occupant(reg)
            {
                if protected.contains(&value) {
                    return Err(format!(
                        "x86 scratch register {reg:?} conflicts with an operand"
                    ));
                }
                self.locations[value.index()] = Some(self.spill(value)?);
            }
        }
        Ok(())
    }

    fn register_occupant(&self, reg: Reg) -> Option<VReg> {
        self.locations
            .iter()
            .enumerate()
            .find_map(|(at, &location)| {
                (location == Some(Location::Register(reg))).then_some(VReg::at(at))
            })
    }

    fn free_register(&self, reserved: RegSet) -> Option<Reg> {
        REGISTERS
            .into_iter()
            .find(|&reg| !reserved.contains(reg) && self.register_occupant(reg).is_none())
    }

    fn record(&mut self, block: BlockId, point: Point) {
        let values = self.liveness.at[point.index()]
            .iter()
            .map(|value| {
                (
                    value,
                    self.locations[value.index()].expect("every live value has a location"),
                )
            })
            .collect();
        self.states[point.index()] = Some(PointState { block, values });
    }

    fn point_block(&self, point: Point) -> BlockId {
        self.liveness
            .blocks
            .iter()
            .find(|layout| {
                layout.entry.index() <= point.index() && point.index() <= layout.terminator.index()
            })
            .expect("every point belongs to a block")
            .block
    }

    fn plan_operand_moves(
        &mut self,
        instruction: InstId,
        operands: &[VReg],
        before: &[Option<Location>],
        assigned: &[Location],
    ) -> Result<(), String> {
        let mut copies = Vec::new();
        for (&value, &destination) in operands.iter().zip(assigned) {
            let source = before[value.index()].ok_or_else(|| {
                format!("x86 operand v{} has no incoming location", value.index())
            })?;
            let copy = ParallelCopy::between(place(source), place(destination));
            if !copies.contains(&copy) {
                copies.push(copy);
            }
        }
        let temporary = Place::Frame(FrameSlot::at(0));
        let plan = parallel_copy::plan(&copies, Some(temporary))?;
        self.operand_moves[instruction.index()] = Some(plan.moves().to_vec());
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "parameter and live-through transfers form one edge copy set"
    )]
    fn plan_edges(&mut self) -> Result<(), String> {
        let temporary = Place::Frame(FrameSlot::at(0));
        for layout in &self.liveness.blocks {
            let terminator = self.selected.blocks[layout.block].terminator;
            for (target, args) in edges(terminator) {
                let target_layout = &self.liveness.blocks[target.index()];
                let params = self.selected.blocks[target].params;
                let parameters = &self.selected.block_params[params.range()];
                let mut copies: Vec<_> = self.selected.operands[args.range()]
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
                            "x86 edge does not carry live-through v{}",
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
                let plan = parallel_copy::plan(&copies, Some(temporary))?;
                self.edge_moves.push(EdgeMoves {
                    from: layout.block,
                    target,
                    moves: plan.moves().to_vec(),
                });
                self.edges = self
                    .edges
                    .checked_add(1)
                    .ok_or_else(|| "x86 edge count overflow".to_owned())?;
                self.edge_cost.instructions = self
                    .edge_cost
                    .instructions
                    .checked_add(plan.cost().instructions)
                    .ok_or_else(|| "x86 edge-copy instruction cost overflow".to_owned())?;
                self.edge_cost.memory_accesses = self
                    .edge_cost
                    .memory_accesses
                    .checked_add(plan.cost().memory_accesses)
                    .ok_or_else(|| "x86 edge-copy memory cost overflow".to_owned())?;
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
                .ok_or_else(|| format!("x86 allocation has no state at p{at}"))?;
            let live = &self.liveness.at[at];
            if state.values.len() != live.iter().count()
                || state.values.iter().any(|(value, _)| !live.contains(*value))
            {
                return Err(format!(
                    "x86 allocation state p{at} disagrees with liveness"
                ));
            }
            for (left_at, &(left, left_location)) in state.values.iter().enumerate() {
                if let Location::Register(reg) = left_location
                    && state.values[..left_at].iter().any(|&(right, location)| {
                        right != left && location == Location::Register(reg)
                    })
                {
                    return Err(format!("x86 allocation assigns {reg:?} twice at p{at}"));
                }
            }
        }
        for layout in &self.liveness.blocks {
            let block = self.selected.blocks[layout.block];
            for (&param, &spec) in self.selected.block_params[block.params.range()]
                .iter()
                .zip(&self.selected.block_param_specs[block.params.range()])
            {
                match spec.constraint {
                    Constraint::Fixed(reg) => verify_constraint(
                        self.location(layout.entry, param)?,
                        Constraint::Fixed(reg),
                        None,
                    )?,
                    Constraint::Any => {}
                    Constraint::Tied(_) => {
                        return Err("x86 block parameter has a tied constraint".to_owned());
                    }
                }
            }
            for points in &layout.instructions {
                let inst = self.selected.instructions[points.instruction];
                let operands = &self.selected.operands[inst.operands.range()];
                let def_offset = usize::from(inst.result.is_some());
                let allocated = self.operand_locations[points.instruction.index()]
                    .as_ref()
                    .ok_or_else(|| "x86 instruction operands were not allocated".to_owned())?;
                if allocated.len() != operands.len() {
                    return Err("x86 instruction operand allocation has the wrong arity".to_owned());
                }
                let mut tied = None;
                for (at, &location) in allocated.iter().enumerate() {
                    let constraint = inst
                        .operand_spec(def_offset + at)
                        .expect("selected instruction was verified")
                        .constraint;
                    verify_constraint(location, constraint, tied)?;
                    if constraint == Constraint::Tied(0) {
                        tied = Some(location);
                    }
                }
                let requirements = inst.opcode.requirements();
                for reg in REGISTERS {
                    if requirements.scratch.contains(reg)
                        && allocated.contains(&Location::Register(reg))
                    {
                        return Err(format!(
                            "x86 scratch register {reg:?} is an instruction operand"
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
                            "x86 scratch register {reg:?} is occupied at p{}",
                            points.early.index()
                        ));
                    }
                }
                if let Some(result) = inst.result {
                    let location = self.location(points.late, result)?;
                    if let Some(tied) = tied {
                        if location != tied {
                            return Err(
                                "x86 tied input and result have different locations".to_owned()
                            );
                        }
                    } else {
                        let constraint = inst.operand_spec(0).expect("selected result").constraint;
                        verify_constraint(location, constraint, None)?;
                    }
                }
                for &(value, location) in &self.states[points.late.index()]
                    .as_ref()
                    .expect("point state")
                    .values
                {
                    if Some(value) != inst.result
                        && matches!(location, Location::Register(reg) if requirements.effects.clobbers.contains(reg))
                    {
                        return Err(format!(
                            "x86 value v{} survives a clobber in a register",
                            value.index()
                        ));
                    }
                }
            }
            match block.terminator {
                Terminator::Branch { condition, .. } => verify_constraint(
                    self.location(layout.terminator, condition)?,
                    Constraint::Any,
                    None,
                )?,
                Terminator::Return { values } => {
                    let result_reg = if block.owner == self.entry {
                        Reg::Rdi
                    } else {
                        Reg::Rax
                    };
                    for &value in &self.selected.operands[values.range()] {
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

    fn location(&self, point: Point, value: VReg) -> Result<Location, String> {
        self.states[point.index()]
            .as_ref()
            .and_then(|state| {
                state
                    .values
                    .iter()
                    .find_map(|&(held, location)| (held == value).then_some(location))
            })
            .ok_or_else(|| {
                format!(
                    "x86 v{} has no location at p{}",
                    value.index(),
                    point.index()
                )
            })
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "frame use combines split, operand, and CFG-edge move plans"
)]
fn function_spill_slots(
    selected: &Selected,
    liveness: &Liveness,
    transitions: &[Transition],
    operand_moves: &[Vec<CopyMove>],
    edge_moves: &[EdgeMoves],
    total: u32,
) -> Vec<u32> {
    let slots = selected
        .functions
        .iter()
        .map(|function| function.source.index())
        .max()
        .map_or(0, |last| last + 1);
    let mut required = vec![0; slots];
    let uses_frame = |owner: FunctionId| {
        let owns_point = |point: Point| {
            liveness.blocks.iter().any(|layout| {
                selected.blocks[layout.block].owner == owner
                    && layout.entry.index() <= point.index()
                    && point.index() <= layout.terminator.index()
            })
        };
        let transition_moves_use_frame = transitions.iter().enumerate().any(|(at, transition)| {
            if !owns_point(transition.at)
                || transitions[..at]
                    .iter()
                    .any(|held| held.at == transition.at)
            {
                return false;
            }
            let copies: Vec<_> = transitions
                .iter()
                .filter(|held| held.at == transition.at)
                .map(|held| ParallelCopy::between(place(held.from), place(held.to)))
                .collect();
            parallel_copy::plan(&copies, (total > 0).then(|| Place::Frame(FrameSlot::at(0))))
                .expect("allocation transition copies were already planned")
                .moves()
                .iter()
                .any(move_uses_frame)
        });
        transition_moves_use_frame
            || liveness.blocks.iter().any(|layout| {
                selected.blocks[layout.block].owner == owner
                    && layout.instructions.iter().any(|points| {
                        operand_moves[points.instruction.index()]
                            .iter()
                            .any(move_uses_frame)
                    })
            })
            || edge_moves.iter().any(|edge| {
                selected.blocks[edge.from].owner == owner && edge.moves.iter().any(move_uses_frame)
            })
    };
    for function in &selected.functions {
        if uses_frame(function.source) {
            required[function.source.index()] = total;
        }
    }
    required
}

const fn move_uses_frame(movement: &CopyMove) -> bool {
    let CopySource::Place(source) = movement.source();
    matches!(source, Place::Frame(_)) || matches!(movement.destination(), Place::Frame(_))
}

fn required_spill_slots(
    segments: &[Segment],
    transitions: &[Transition],
    operand_moves: &[Vec<CopyMove>],
    edge_moves: &[EdgeMoves],
) -> Result<u32, String> {
    let mut last = None;
    let mut note_location = |location: Location| {
        if let Location::Spill(SpillSlot(slot)) = location {
            last = Some(last.map_or(slot, |held: u32| held.max(slot)));
        }
    };
    for segment in segments {
        note_location(segment.location);
    }
    for transition in transitions {
        note_location(transition.from);
        note_location(transition.to);
    }
    let mut note_move = |movement: &CopyMove| {
        let CopySource::Place(source) = movement.source();
        for place in [source, movement.destination()] {
            if let Place::Frame(slot) = place {
                last = Some(last.map_or_else(|| slot.number(), |held| held.max(slot.number())));
            }
        }
    };
    for movement in operand_moves
        .iter()
        .flatten()
        .chain(edge_moves.iter().flat_map(|edge| &edge.moves))
    {
        note_move(movement);
    }
    // Transition groups are replanned together during final lowering and may
    // discover a cycle not present in an individual operand plan. Slot zero
    // is reserved for that temporary.
    if !transitions.is_empty() && last.is_none() {
        last = Some(0);
    }
    last.map_or(Ok(0), |last| {
        last.checked_add(1)
            .ok_or_else(|| "x86 spill frame exceeds 4G slots".to_owned())
    })
}

fn collect_instruction_data<T>(
    data: Vec<Option<Vec<T>>>,
    what: &str,
) -> Result<Vec<Vec<T>>, String> {
    data.into_iter()
        .enumerate()
        .map(|(at, held)| held.ok_or_else(|| format!("x86 instruction i{at} has no {what}")))
        .collect()
}

fn verify_constraint(
    location: Location,
    constraint: Constraint,
    tied: Option<Location>,
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
            "x86 allocation location {location:?} violates {constraint:?}"
        ))
    }
}

fn edges(terminator: Terminator) -> Vec<(BlockId, Range)> {
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

const fn place(location: Location) -> Place {
    match location {
        Location::Register(reg) => Place::Register(reg),
        Location::Spill(SpillSlot(slot)) => Place::Frame(FrameSlot::at(slot)),
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "segment compression also records each location transition"
)]
fn build_segments(
    states: &[Option<PointState>],
) -> Result<(Vec<Segment>, Vec<Transition>), String> {
    let mut segments: Vec<Segment> = Vec::new();
    let mut transitions = Vec::new();
    for (point_at, state) in states.iter().enumerate() {
        let Some(state) = state else { continue };
        let point = Point::at(point_at)?;
        for &(value, location) in &state.values {
            let previous = segments.iter_mut().rev().find(|segment| {
                segment.value == value
                    && segment.end.index() == point_at
                    && states[point_at - 1]
                        .as_ref()
                        .is_some_and(|before| before.block == state.block)
            });
            if let Some(previous) = previous {
                if previous.location == location {
                    previous.end = Point::at(point_at + 1)?;
                } else {
                    transitions.push(Transition {
                        value,
                        at: point,
                        from: previous.location,
                        to: location,
                    });
                    segments.push(Segment {
                        value,
                        start: point,
                        end: Point::at(point_at + 1)?,
                        location,
                    });
                }
            } else {
                segments.push(Segment {
                    value,
                    start: point,
                    end: Point::at(point_at + 1)?,
                    location,
                });
            }
        }
    }
    Ok((segments, transitions))
}

impl Allocation {
    #[expect(
        clippy::too_many_lines,
        reason = "the allocation boundary verifies ranges, transitions, moves, and costs"
    )]
    fn verify(&self, selected: &Selected, liveness: &Liveness) -> Result<(), String> {
        if self.operand_locations.len() != selected.instructions.len()
            || self.operand_moves.len() != selected.instructions.len()
        {
            return Err("x86 allocation omitted instruction operands".to_owned());
        }
        for (inst, locations) in selected.instructions.iter().zip(&self.operand_locations) {
            if locations.len() != inst.operands.len() {
                return Err("x86 allocation has the wrong operand-location arity".to_owned());
            }
        }
        for segment in &self.segments {
            if segment.start.index() >= segment.end.index()
                || segment.end.index() > liveness.at.len()
                || segment.value.index() >= selected.widths.len()
            {
                return Err("x86 allocation contains an invalid live segment".to_owned());
            }
            if let Location::Spill(SpillSlot(slot)) = segment.location {
                let owner = liveness
                    .blocks
                    .iter()
                    .find(|layout| {
                        layout.entry.index() <= segment.start.index()
                            && segment.start.index() <= layout.terminator.index()
                    })
                    .map(|layout| selected.blocks[layout.block].owner)
                    .ok_or_else(|| "x86 spill segment has no owning function".to_owned())?;
                if self
                    .spill_slots
                    .get(owner.index())
                    .is_none_or(|&slots| slot >= slots)
                {
                    return Err("x86 allocation refers past its spill frame".to_owned());
                }
            }
        }
        for transition in &self.transitions {
            if transition.from == transition.to
                || transition.at.index() >= liveness.at.len()
                || transition.value.index() >= selected.widths.len()
            {
                return Err("x86 allocation contains an invalid split transition".to_owned());
            }
        }
        if usize::try_from(self.edges).expect("edge count fits") != self.edge_moves.len() {
            return Err("x86 allocation omitted edge move plans".to_owned());
        }
        let mut cost = TransitionCost::default();
        for movement in self.edge_moves.iter().flat_map(|edge| &edge.moves) {
            let requirements = movement.requirements();
            cost.instructions = cost
                .instructions
                .checked_add(u32::from(requirements.instructions))
                .ok_or_else(|| "x86 verified edge instruction cost overflow".to_owned())?;
            cost.memory_accesses = cost
                .memory_accesses
                .checked_add(
                    u32::from(requirements.memory_reads) + u32::from(requirements.memory_writes),
                )
                .ok_or_else(|| "x86 verified edge memory cost overflow".to_owned())?;
        }
        if cost != self.edge_cost {
            return Err("x86 allocation edge cost disagrees with its moves".to_owned());
        }
        if self.edges > u32::try_from(liveness.blocks.len().saturating_mul(2)).unwrap_or(u32::MAX) {
            return Err("x86 allocation has too many CFG edges".to_owned());
        }
        Ok(())
    }
}

impl From<parallel_copy::PlanError> for String {
    fn from(error: parallel_copy::PlanError) -> Self {
        format!("x86 edge copy cannot be planned: {error:?}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::selected::select;
    use faun_core::ir::{Binary, Class, Program};

    #[test]
    fn loops_produce_segmented_live_ranges_and_edge_costs() {
        let program = faun_core::programs::carries_a_total_into_an_arm(3);
        let selected = select(&program).unwrap();
        let liveness = Liveness::build(&selected).unwrap();
        let allocation = Allocator::new(&selected, &liveness, program.entry())
            .unwrap()
            .run()
            .unwrap();
        allocation.verify(&selected, &liveness).unwrap();
        assert!(!allocation.segments.is_empty());
        assert!(allocation.edges > 0);
    }

    #[test]
    fn repeated_values_receive_each_fixed_operand_register() {
        let (mut program, main) = Program::new("main");
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let two = builder.constant(Class::Word, 2);
            let value = builder.binary(Binary::Add, one, two);
            let product = builder.binary(Binary::Mul, value, value);
            builder.ret(&[product]);
        });
        let selected = select(&program).unwrap();
        let multiply = selected
            .instructions
            .iter()
            .position(|inst| inst.opcode == super::super::Opcode::Multiply)
            .unwrap();
        let liveness = Liveness::build(&selected).unwrap();
        let allocation = Allocator::new(&selected, &liveness, program.entry())
            .unwrap()
            .run()
            .unwrap();
        allocation.verify(&selected, &liveness).unwrap();
        assert_eq!(
            allocation.operand_locations[multiply],
            [Location::Register(Reg::Rax), Location::Register(Reg::Rcx)]
        );
        assert!(!allocation.operand_moves[multiply].is_empty());
    }

    #[test]
    fn register_pressure_creates_spilled_segments() {
        let (mut program, main) = Program::new("main");
        program.define(main, |builder, _| {
            let mut values: Vec<_> = (0..12)
                .map(|value| builder.constant(Class::Word, value))
                .collect();
            while values.len() > 1 {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                values.push(builder.binary(Binary::Add, left, right));
            }
            builder.ret(&values);
        });
        let selected = select(&program).unwrap();
        let liveness = Liveness::build(&selected).unwrap();
        let allocation = Allocator::new(&selected, &liveness, program.entry())
            .unwrap()
            .run()
            .unwrap();
        allocation.verify(&selected, &liveness).unwrap();
        assert!(
            allocation
                .segments
                .iter()
                .any(|segment| matches!(segment.location, Location::Spill(_)))
        );
    }

    #[test]
    fn calls_split_values_around_their_clobber_mask() {
        let (mut program, main) = Program::new("main");
        let helper = program.declare("helper", &[], &[Class::Word]);
        program.define(helper, |builder, _| {
            let answer = builder.constant(Class::Word, 3);
            builder.ret(&[answer]);
        });
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let two = builder.constant(Class::Word, 2);
            let across = builder.binary(Binary::Add, one, two);
            let answer = builder.call_one(helper, &[]);
            let sum = builder.binary(Binary::Add, across, answer);
            builder.ret(&[sum]);
        });
        let selected = select(&program).unwrap();
        let liveness = Liveness::build(&selected).unwrap();
        let allocation = Allocator::new(&selected, &liveness, program.entry())
            .unwrap()
            .run()
            .unwrap();
        allocation.verify(&selected, &liveness).unwrap();
        assert!(allocation.transitions.iter().any(|transition| {
            matches!(transition.from, Location::Register(_))
                && matches!(transition.to, Location::Spill(_))
        }));
    }
}
