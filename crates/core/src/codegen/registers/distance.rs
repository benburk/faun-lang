//! How far each value is from where it is next read, loops counted.
//!
//! Where registers run out, the value read furthest ahead is the one to put
//! in memory: it is the longest before it has to come back. Distance is
//! counted in points along the nearest path, and leaving a loop costs as
//! much as a long way round, so a value read after a loop gives way to one
//! read inside it.

use super::{BlockId, Code, Liveness, Point, Register, VReg, successors, visit_terminator_values};

/// What leaving one loop counts as, in points.
const LEAVING: u32 = 1 << 16;

/// No read ahead at all.
pub(super) const NEVER: u32 = u32::MAX;

pub(super) struct Distances {
    /// For each block, each value read in it with the point it is read at,
    /// in order.
    reads: Vec<Vec<(VReg, u32)>>,
    /// For each block, how far from its end each value live at its end is
    /// next read, in the order they are live there.
    out: Vec<Vec<u32>>,
    /// For each block, its terminator's point.
    ends: Vec<Point>,
}

impl Distances {
    pub(super) fn new<R: Register>(code: &Code<R>, liveness: &Liveness) -> Self {
        let blocks = code.blocks.len();
        let mut reads = vec![Vec::new(); blocks];
        let mut out = vec![Vec::new(); blocks];
        let mut ends = vec![Point(0); blocks];
        for layout in &liveness.blocks {
            let at = layout.block.index();
            let block = code.blocks[layout.block];
            let read = &mut reads[at];
            for points in &layout.instructions {
                let inst = code.instructions[points.instruction];
                for &operand in &code.operands[inst.operands.range()] {
                    read.push((operand, points.early.0));
                }
            }
            visit_terminator_values(code, block.terminator, |value| {
                read.push((value, layout.terminator.0));
            });
            read.sort_unstable();
            read.dedup();
            out[at] = vec![NEVER; liveness.at[layout.terminator.index()].len()];
            ends[at] = layout.terminator;
        }
        let leaving = leaving(code);
        let mut distances = Self { reads, out, ends };
        distances.solve(code, liveness, &leaving);
        distances
    }

    /// Carry each block's distances back to its predecessors until none
    /// shortens, revisiting only the blocks whose successors changed.
    fn solve<R: Register>(&mut self, code: &Code<R>, liveness: &Liveness, leaving: &[Vec<u32>]) {
        let predecessors = predecessors(code);
        let mut pending: Vec<BlockId> = liveness.blocks.iter().map(|layout| layout.block).collect();
        let mut queued = vec![true; code.blocks.len()];
        while let Some(id) = pending.pop() {
            let at = id.index();
            queued[at] = false;
            let mut changed = false;
            for (edge, target) in successors(code.blocks[id].terminator)
                .into_iter()
                .enumerate()
            {
                if let Some(target) = target {
                    changed |= self.relax(code, liveness, id, target, leaving[at][edge]);
                }
            }
            if changed {
                for &from in &predecessors[at] {
                    if !queued[from.index()] {
                        queued[from.index()] = true;
                        pending.push(from);
                    }
                }
            }
        }
    }

    /// Shorten what `from` has for each value it hands `target` by what
    /// `target` has, taking the edge costing `leaving`; answer whether any
    /// shortened.
    fn relax<R: Register>(
        &mut self,
        code: &Code<R>,
        liveness: &Liveness,
        from: BlockId,
        target: BlockId,
        leaving: u32,
    ) -> bool {
        let at = from.index();
        let end = &liveness.at[self.ends[at].index()];
        let entry = liveness.blocks[target.index()].entry;
        let params = &code.block_params[code.blocks[target].params.range()];
        let mut changed = false;
        for value in liveness.at[entry.index()].iter() {
            if params.contains(&value) {
                continue;
            }
            let Some(position) = end.position(value) else {
                continue;
            };
            let far = self
                .next(liveness, target, entry, value)
                .saturating_add(leaving)
                .saturating_add(1);
            let held = &mut self.out[at][position];
            if far < *held {
                *held = far;
                changed = true;
            }
        }
        changed
    }

    /// How many points from `point`, in `block`, `value` is next read.
    pub(super) fn next(
        &self,
        liveness: &Liveness,
        block: BlockId,
        point: Point,
        value: VReg,
    ) -> u32 {
        let at = block.index();
        let reads = &self.reads[at];
        let ahead = reads.partition_point(|&read| read < (value, point.0));
        if let Some(&(read, read_at)) = reads.get(ahead)
            && read == value
        {
            return read_at - point.0;
        }
        let end = self.ends[at];
        liveness.at[end.index()]
            .position(value)
            .map_or(NEVER, |position| {
                self.out[at][position].saturating_add(end.0 - point.0)
            })
    }
}

fn predecessors<R: Register>(code: &Code<R>) -> Vec<Vec<BlockId>> {
    let mut predecessors = vec![Vec::new(); code.blocks.len()];
    for (id, block) in code.blocks.iter_enumerated() {
        for target in successors(block.terminator).into_iter().flatten() {
            predecessors[target.index()].push(id);
        }
    }
    predecessors
}

/// For each block, what taking each of its edges counts as for the loops
/// it leaves. A loop is found by an edge back to a block no later than its
/// source; its body is what reaches that source without passing its head.
fn leaving<R: Register>(code: &Code<R>) -> Vec<Vec<u32>> {
    let predecessors = predecessors(code);
    // The loops each block is in, by the order they were found.
    let mut within: Vec<Vec<usize>> = vec![Vec::new(); code.blocks.len()];
    let mut loops = 0;
    for (id, block) in code.blocks.iter_enumerated() {
        for head in successors(block.terminator).into_iter().flatten() {
            if head.index() > id.index() {
                continue;
            }
            within[head.index()].push(loops);
            let mut pending = vec![id];
            while let Some(member) = pending.pop() {
                if within[member.index()].last() != Some(&loops) {
                    within[member.index()].push(loops);
                    pending.extend(&predecessors[member.index()]);
                }
            }
            loops += 1;
        }
    }
    code.blocks
        .iter_enumerated()
        .map(|(id, block)| {
            successors(block.terminator)
                .into_iter()
                .map(|target| {
                    target.map_or(0, |target| {
                        let left = within[id.index()]
                            .iter()
                            .filter(|found| !within[target.index()].contains(found))
                            .count();
                        LEAVING.saturating_mul(u32::try_from(left).unwrap_or(u32::MAX))
                    })
                })
                .collect()
        })
        .collect()
}
