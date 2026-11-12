//! A region for a closed recursive constructor. Every non-static cell in
//! the result is made by this invocation or one of its recursive calls.
//! Outside the constructor the root may only be handed to readers that
//! neither publish it nor return any descendant. Its last use can therefore
//! release all the storage without walking the nodes.

mod nullable;

use std::collections::{HashMap, HashSet};

use super::natural::{Helper, Library};
use super::packing::Packed;
use super::{
    Binary, Builder, Class, DataId, FunctionId, Offset, Op, Program, RegionId, Relation, Returns,
    ValueId, Width,
};

const W: Class = Class::Word;
const A: Class = Class::Address;
const CAPACITY: u64 = 4096;
const WORD: u64 = 8;

/// Each region node starts at its tag. Readers use ordinary cell offsets,
/// so its virtual base precedes it by the two omitted heap header words.
const PREFIX: u64 = 2 * WORD;

pub(super) const fn node_bytes(packed: &Packed) -> u64 {
    (PREFIX + packed.size).next_multiple_of(WORD)
}

#[derive(Default)]
pub(super) struct Plan {
    pub(super) constructors: HashSet<FunctionId>,
    pub(super) roots: HashSet<ValueId>,
    pub(super) nullable: nullable::Layout,
}

fn returns_cell(p: &Program, id: FunctionId) -> bool {
    matches!(p.function(id).returns, Returns::Values(r) if p.signature(r) == [Class::Cell])
}

/// Require scalar or child fields and no way for an intermediate cell to
/// come from outside, or be published before the constructor returns.
fn constructor(p: &Program, id: FunctionId, packed: &[Packed]) -> bool {
    let f = p.function(id);
    let Some(body) = f.body() else { return false };
    if id == p.entry()
        || !returns_cell(p, id)
        || p.signature(f.params)
            .iter()
            .any(|c| !matches!(c, Class::Held(_) | Class::Word | Class::Natural))
    {
        return false;
    }
    let mut recursive = false;
    let mut builds = false;
    for op in p.every(body) {
        match *op {
            Op::Call { function, .. } if function == id => recursive = true,
            Op::Cell { shape, fields, .. }
                if p.shaped(shape)
                    .iter()
                    .all(|c| matches!(c, Class::Held(_) | Class::Word | Class::Cell))
                    && node_bytes(&packed[shape.index()]) <= CAPACITY =>
            {
                builds |= !fields.is_empty();
            }
            Op::If { .. }
            | Op::Constant { .. }
            | Op::NaturalConstant(_)
            | Op::Compare { .. }
            | Op::Binary { .. }
            | Op::Shift { .. }
            | Op::Float { .. }
            | Op::Convert { .. } => {}
            _ => return false,
        }
    }
    recursive && builds && connected(p, body, super::Exit::Return)
}

/// Every cell created here becomes a field or an outgoing value in the
/// same region. This rules out accumulating discarded intermediate trees,
/// including paths that return early while another subtree is live.
fn connected(p: &Program, region: RegionId, exit: super::Exit) -> bool {
    if p.region(region)
        .terminator
        .is_none_or(|term| term.exit != exit)
    {
        return false;
    }
    let mut live = HashSet::new();
    for (op, results) in p.walk(region) {
        for v in p.operands(op).filter(|&v| p.class(v) == Class::Cell) {
            if !matches!(op, Op::Cell { .. }) || !live.remove(&v) {
                return false;
            }
        }
        for &v in results.iter().filter(|&&v| p.class(v) == Class::Cell) {
            if !matches!(op, Op::Cell { .. } | Op::Call { .. } | Op::If { .. }) {
                return false;
            }
            live.insert(v);
        }
        if let Op::If {
            then_region,
            else_region,
            ..
        } = *op
            && ![then_region, else_region]
                .iter()
                .all(|&r| connected(p, r, super::Exit::Yield))
        {
            return false;
        }
    }
    p.outgoing(region)
        .iter()
        .filter(|&&v| p.class(v) == Class::Cell)
        .all(|v| live.remove(v))
        && live.is_empty()
}

/// A reader may recurse with a projected child. No cell can leave through
/// a join, loop, result, call to another routine or stored value.
fn reader(p: &Program, id: FunctionId) -> bool {
    let f = p.function(id);
    let Some(body) = f.body() else { return false };
    if !p.signature(f.params).contains(&Class::Cell) {
        return false;
    }
    let mut regions = vec![body];
    while let Some(r) = regions.pop() {
        if p.outgoing(r).iter().any(|&v| p.class(v) == Class::Cell) {
            return false;
        }
        for op in p.ops(r) {
            if p.operands(op).any(|v| p.class(v) == Class::Cell)
                && !matches!(*op, Op::CellTag { .. } | Op::CellField { .. })
                && !matches!(*op, Op::Call { function, .. } if function == id)
            {
                return false;
            }

            match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => regions.extend([then_region, else_region]),
                Op::Loop { body, .. } => regions.push(body),
                _ => {}
            }
        }
    }
    true
}

fn caller_roots(p: &Program, constructors: &HashSet<FunctionId>) -> HashMap<ValueId, FunctionId> {
    let mut roots = HashMap::new();
    for (caller, f) in p.functions.iter_enumerated() {
        if let Some(body) = f.body() {
            for (op, results) in p.walk_within(body) {
                if let Op::Call { function, .. } = *op
                    && caller != function
                    && constructors.contains(&function)
                {
                    roots.insert(results[0], function);
                }
            }
        }
    }
    roots
}

impl Plan {
    fn shapes<'a>(
        &'a self,
        p: &'a Program,
        regional: bool,
    ) -> impl Iterator<Item = super::ShapeId> + 'a {
        p.functions
            .iter_enumerated()
            .filter(move |(id, _)| self.constructors.contains(id) == regional)
            .filter_map(|(_, f)| f.body())
            .flat_map(|body| p.every(body))
            .filter_map(|op| match *op {
                Op::Cell { shape, fields, .. } if !fields.is_empty() => Some(shape),
                _ => None,
            })
    }

    /// If removing region nodes leaves a single layout of owned fields
    /// among ordinary allocations, its destructor can release them directly.
    /// A foreign cell or buffer could carry a layout absent from our sites.
    pub(super) fn remaining_claims(
        &self,
        p: &Program,
        packed: &[Packed],
    ) -> Option<Vec<(u64, u64)>> {
        if self.constructors.is_empty() {
            return None;
        }
        for (id, f) in p.functions.iter_enumerated() {
            if (f.body().is_none() || id == p.entry())
                && p.signature(f.params)
                    .iter()
                    .chain(p.signature(f.returns.classes()))
                    .any(|c| matches!(c, Class::Cell | Class::Buffer))
            {
                return None;
            }
        }
        let mut shapes = self.shapes(p, false);
        let fixed: Vec<_> = packed[shapes.next()?.index()].managed().collect();
        if fixed.len() <= 1
            && shapes.all(|s| packed[s.index()].managed().eq(fixed.iter().copied()))
            && self
                .shapes(p, true)
                .any(|s| !packed[s.index()].managed().eq(fixed.iter().copied()))
        {
            Some(fixed)
        } else {
            None
        }
    }

    pub(super) fn of(p: &Program, packed: &[Packed]) -> Self {
        let mut constructors: HashSet<_> = p
            .functions
            .ids()
            .filter(|&id| constructor(p, id, packed))
            .collect();
        if constructors.is_empty() {
            return Self::default();
        }
        let readers: HashSet<_> = p.functions.ids().filter(|&id| reader(p, id)).collect();
        let mut roots = caller_roots(p, &constructors);
        for r in p.regions.ids() {
            let uses = p.ops(r).iter().filter(
                |op| !matches!(op, Op::Call { function, .. } if readers.contains(function)),
            );
            for value in uses
                .flat_map(|op| p.operands(op))
                .chain(p.outgoing(r).iter().copied())
            {
                if let Some(producer) = roots.get(&value) {
                    constructors.remove(producer);
                }
            }
        }
        constructors.retain(|id| roots.values().any(|f| f == id));
        roots.retain(|_, f| constructors.contains(f));
        let nullable = nullable::Layout::of(p, &roots);
        Self {
            constructors,
            roots: roots.into_keys().collect(),
            nullable,
        }
    }
}

/// Only the construction itself uses the current chunk. The outer call
/// detaches the list before another construction can start. Independent
/// roots, including overlapping long-lived roots, own separate lists.
#[derive(Clone, Copy)]
pub(super) struct Chunks {
    head: DataId,
    pub(super) allocate: FunctionId,
    pub(super) release: FunctionId,
    /// Distance from a returned pointer to the beginning of its reservation.
    /// Ordinary region cells use a virtual base to match heap field offsets.
    pub(super) payload_offset: u64,
}

impl Chunks {
    pub(super) fn append(p: &mut Program, library: &Library, plan: &Plan) -> Self {
        let head = p.global(&[0; 8]);
        let allocate = p.declare("region.bump", &[W], &[A]);
        let release = p.declare("region.release", &[W], &[]);
        let payload_offset = if plan.nullable.builders.len() == plan.constructors.len() {
            0
        } else {
            PREFIX
        };
        define_allocate(p, allocate, head, library, payload_offset);
        p.define(release, |b, args| {
            b.loop_(args, &[], |b, state| {
                b.if_(state[0], &[], |b| b.yield_(&[]), |b| b.ret(&[]));
                let block = b.convert(A, state[0]);
                let next = b.load(Width::Word, block, Offset::Words(3));
                // A chunk is exclusively owned from allocation to here.
                let free = b.constant(W, 0);
                b.store(Width::Word, block, Offset::Words(1), free);
                b.continue_(&[next]);
            });
        });
        Self {
            head,
            allocate,
            release,
            payload_offset,
        }
    }

    pub(super) fn detach(self, b: &mut Builder) -> ValueId {
        let at = b.address_of(self.head);
        let head = b.load(Width::Word, at, Offset::Words(0));
        let zero = b.constant(W, 0);
        b.store(Width::Word, at, Offset::Words(0), zero);
        head
    }
}

fn define_allocate(
    p: &mut Program,
    allocate: FunctionId,
    head: DataId,
    library: &Library,
    payload_offset: u64,
) {
    p.define(allocate, |b, args| {
        let head_at = b.address_of(head);
        let head = b.load(Width::Word, head_at, Offset::Words(0));
        let current = b.convert(A, head);
        let room = b.if_(
            head,
            &[W],
            |b| {
                let room = b.load(Width::Word, current, Offset::Words(2));
                b.yield_(&[room]);
            },
            |b| b.yield_(&[head]),
        )[0];
        let short = b.compare(Relation::Less, room, args[0]);
        let chunk = b.if_(
            short,
            &[A, W],
            |b| {
                let bytes = b.constant(W, CAPACITY + WORD);
                let block = b.call_one(library.require(Helper::Allocate), &[bytes]);
                b.store(Width::Word, block, Offset::Words(3), head);
                let address = b.convert(W, block);
                b.store(Width::Word, head_at, Offset::Words(0), address);
                let room = b.constant(W, CAPACITY);
                b.yield_(&[block, room]);
            },
            |b| b.yield_(&[current, room]),
        );
        bump(b, chunk[0], chunk[1], args[0], payload_offset);
    });
}

fn bump(b: &mut Builder, block: ValueId, room: ValueId, bytes: ValueId, payload_offset: u64) {
    let left = b.binary(Binary::Sub, room, bytes);
    b.store(Width::Word, block, Offset::Words(2), left);
    // The first reservation begins after the four chunk header words.
    let prefix = b.constant(W, 4 * WORD - payload_offset);
    let offset = b.binary(Binary::Add, prefix, left);
    let result = super::cell::byte_offset(b, block, offset);
    b.ret(&[result]);
}
