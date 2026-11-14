//! A closed region tree with one nullary tag and one payload tag can use
//! the null pointer for the first. Non-null pointers identify reservations
//! containing only fields. Every caller of a reader must agree on the layout.

use std::collections::{HashMap, HashSet};

use super::super::{Builder, Class, FunctionId, Op, Program, Range, Relation, ValueId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::ir) struct Tags {
    empty: u32,
    payload: u32,
}

impl Tags {
    pub(in crate::ir) fn read(self, b: &mut Builder, pointer: ValueId) -> ValueId {
        let null = b.constant(Class::Address, 0);
        if (self.empty, self.payload) == (0, 1) {
            return b.compare(Relation::Less, null, pointer);
        }
        let empty = b.compare(Relation::Equal, pointer, null);
        if (self.empty, self.payload) == (1, 0) {
            return empty;
        }
        b.if_(
            empty,
            &[Class::Word],
            |b| {
                let tag = b.constant(Class::Word, u64::from(self.empty));
                b.yield_(&[tag]);
            },
            |b| {
                let tag = b.constant(Class::Word, u64::from(self.payload));
                b.yield_(&[tag]);
            },
        )[0]
    }
}

fn tags(p: &Program, id: FunctionId) -> Option<Tags> {
    let mut empty = None;
    let mut payload = None;
    for op in p.every(p.function(id).body()?) {
        if let Op::Cell { tag, fields, .. } = *op {
            let slot = if fields.is_empty() {
                &mut empty
            } else {
                &mut payload
            };
            if slot.replace(tag).is_some_and(|previous| previous != tag) {
                return None;
            }
        }
    }
    let tags = Tags {
        empty: empty?,
        payload: payload?,
    };
    (tags.empty != tags.payload).then_some(tags)
}

type Calls = HashMap<FunctionId, Vec<(FunctionId, Range)>>;

fn calls(p: &Program) -> Calls {
    let mut calls = Calls::new();
    for (caller, f) in p.functions.iter_enumerated() {
        if let Some(body) = f.body() {
            for op in p.every(body) {
                if let Op::Call { function, args } = *op {
                    calls.entry(function).or_default().push((caller, args));
                }
            }
        }
    }
    calls
}

/// Follow a single borrowed cell parameter through immutable projections.
/// A recursive call can only continue from such a value. Calls from outside
/// must all supply roots of this same constructor.
fn reader_cells(
    p: &Program,
    reader: FunctionId,
    from: FunctionId,
    roots: &HashMap<ValueId, FunctionId>,
    calls: &Calls,
) -> Option<HashSet<ValueId>> {
    if reader == p.entry() {
        return None;
    }
    let body = p.function(reader).body()?;
    let mut params = p
        .values(p.region(body).params)
        .iter()
        .enumerate()
        .filter(|&(_, v)| p.class(*v) == Class::Cell);
    let (position, &param) = params.next()?;
    if params.next().is_some() {
        return None;
    }
    let mut descendants = HashSet::from([param]);
    for (op, results) in p.walk_within(body) {
        if let Op::CellField { cell, .. } = *op
            && p.class(results[0]) == Class::Cell
            && descendants.contains(&cell)
        {
            descendants.insert(results[0]);
        }
    }
    for &(caller, args) in calls.get(&reader)? {
        let arg = p.values(args)[position];
        if !(roots.get(&arg) == Some(&from) || caller == reader && descendants.contains(&arg)) {
            return None;
        }
    }
    Some(descendants)
}

#[derive(Default)]
pub(in crate::ir) struct Layout {
    pub(in crate::ir) builders: HashSet<FunctionId>,
    pub(in crate::ir) cells: HashMap<ValueId, Tags>,
}

impl Layout {
    pub(super) fn of(p: &Program, roots: &HashMap<ValueId, FunctionId>) -> Self {
        let mut layout = Self::default();
        if roots.is_empty() {
            return layout;
        }
        let calls = calls(p);
        let mut consumers = HashMap::<FunctionId, HashSet<FunctionId>>::new();
        for (&reader, sites) in &calls {
            for &(_, args) in sites {
                for root in p.values(args) {
                    if let Some(&from) = roots.get(root) {
                        consumers.entry(from).or_default().insert(reader);
                    }
                }
            }
        }
        for (&from, readers) in &consumers {
            let Some(tags) = tags(p, from) else { continue };
            let Some(groups) = readers
                .iter()
                .map(|&reader| reader_cells(p, reader, from, roots, &calls))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            layout.builders.insert(from);
            for cell in groups.into_iter().flatten() {
                layout.cells.insert(cell, tags);
            }
        }
        layout
    }
}
