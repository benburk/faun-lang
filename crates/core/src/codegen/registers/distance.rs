//! How far each value is from where it is next read, loops counted.
//!
//! Where registers run out, the value read furthest ahead is the one to put
//! in memory: it is the longest before it has to come back. Distance is
//! counted in points along the nearest path, and leaving a loop costs as
//! much as a long way round, so a value read after a loop gives way to one
//! read inside it.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

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
        let walk = walk(code);
        let leaving = leaving(code, &walk.back);
        let mut distances = Self { reads, out, ends };
        distances.solve(code, liveness, &leaving, &walk.left);
        distances
    }

    /// Carry each block's distances back to its predecessors until none
    /// shortens, revisiting only the blocks whose successors changed.
    ///
    /// The pending block the walk left first goes next, so a block is
    /// mostly carried back once its successors are settled: outside loops
    /// once, and a loop's body as often as the loop has to go round. Taken
    /// in any other order, a distance shortened late is carried back again
    /// through every block it already went through.
    fn solve<R: Register>(
        &mut self,
        code: &Code<R>,
        liveness: &Liveness,
        leaving: &[Vec<u32>],
        left: &[BlockId],
    ) {
        let predecessors = predecessors(code);
        let mut rank = vec![0; code.blocks.len()];
        for (order, id) in left.iter().enumerate() {
            rank[id.index()] = order;
        }
        let mut pending: BinaryHeap<Reverse<usize>> = (0..left.len()).map(Reverse).collect();
        let mut queued = vec![true; code.blocks.len()];
        while let Some(Reverse(order)) = pending.pop() {
            let id = left[order];
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
                        pending.push(Reverse(rank[from.index()]));
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

/// What walking depth first from each function's entry finds.
struct Walk {
    /// For each block, which of its edges go back to a block the walk is
    /// still within: the edges that close a loop. Block order says nothing
    /// of this, as a branch's join may be made before its arms, so each is
    /// found by walking.
    back: Vec<[bool; 2]>,
    /// Every block, in the order the walk left it: each after every
    /// successor it reaches by an edge that is not a back edge.
    left: Vec<BlockId>,
}

fn walk<R: Register>(code: &Code<R>) -> Walk {
    let count = code.blocks.len();
    let mut seen = vec![Seen::Not; count];
    let mut walk = Walk {
        back: vec![[false; 2]; count],
        left: Vec::with_capacity(count),
    };
    // Every function from its entry, then any block no entry reaches.
    let roots = code
        .functions
        .iter()
        .map(|function| function.entry)
        .chain((0..count).map(BlockId::at));
    for root in roots {
        if seen[root.index()] == Seen::Not {
            walk_from(code, root, &mut seen, &mut walk);
        }
    }
    walk
}

/// Where a block stands in the walk [`back_edges`] makes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Seen {
    Not,
    Within,
    Left,
}

/// Walk depth first from `root`, marking each edge to a block the walk is
/// still within, and noting each block as the walk leaves it.
fn walk_from<R: Register>(code: &Code<R>, root: BlockId, seen: &mut [Seen], walk: &mut Walk) {
    seen[root.index()] = Seen::Within;
    // Each block being walked, and which of its edges is next.
    let mut walking = vec![(root, 0)];
    while let Some(top) = walking.last_mut() {
        let (at, edge) = *top;
        if edge == 2 {
            seen[at.index()] = Seen::Left;
            walk.left.push(at);
            walking.pop();
            continue;
        }
        top.1 += 1;
        let Some(target) = successors(code.blocks[at].terminator)[edge] else {
            continue;
        };
        match seen[target.index()] {
            Seen::Not => {
                seen[target.index()] = Seen::Within;
                walking.push((target, 0));
            }
            Seen::Within => walk.back[at.index()][edge] = true,
            Seen::Left => {}
        }
    }
}

/// For each block, what taking each of its edges counts as for the loops
/// it leaves. A loop is found by an edge back to a block the walk is still
/// within; its body is what reaches that edge's source without passing its
/// head.
fn leaving<R: Register>(code: &Code<R>, back: &[[bool; 2]]) -> Vec<Vec<u32>> {
    let predecessors = predecessors(code);
    // The loops each block is in, by the order they were found.
    let mut within: Vec<Vec<usize>> = vec![Vec::new(); code.blocks.len()];
    let mut loops = 0;
    for (id, block) in code.blocks.iter_enumerated() {
        for (edge, head) in successors(block.terminator).into_iter().enumerate() {
            let Some(head) = head.filter(|_| back[id.index()][edge]) else {
                continue;
            };
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
