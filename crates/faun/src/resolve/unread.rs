//! Names bound again on ways that meet, never read after they meet. Each
//! such name is a local every way going on binds, or one a loop hands from
//! round to round and out; dropping the ones nothing reads holds only a
//! name read where ways meet to one type there, as Python's would be.

use std::collections::{HashMap, HashSet};

use super::h;
use crate::Symbol;

/// Drops from `body` each local of `merged`, and each name a loop carries,
/// that nothing reads, and answers the joins kept. What is dropped is a
/// local's read handed to another, so nothing else changes.
pub(super) fn drop_unread(
    body: &mut h::Body,
    merged: Vec<(h::LocalId, Symbol)>,
) -> Vec<(h::LocalId, Symbol)> {
    let joins: HashSet<_> = merged.iter().map(|(local, _)| *local).collect();
    let mut reads = Reads {
        joins: &joins,
        read: Vec::new(),
        feeds: HashMap::new(),
    };
    reads.body(body, None, &[]);
    let live = reads.live();
    Dropper {
        joins: &joins,
        live: &live,
    }
    .body(body, None);
    merged
        .into_iter()
        .filter(|(local, _)| live.contains(local))
        .collect()
}

/// Which locals are read: by a line, or by a merge or a carried name that
/// is itself read.
struct Reads<'a> {
    joins: &'a HashSet<h::LocalId>,
    read: Vec<h::LocalId>,
    /// What each merge and carried name is handed, read only where it is.
    feeds: HashMap<h::LocalId, Vec<h::LocalId>>,
}

impl Reads<'_> {
    fn live(mut self) -> HashSet<h::LocalId> {
        let mut live = HashSet::new();
        while let Some(local) = self.read.pop() {
            if live.insert(local) {
                self.read
                    .extend(self.feeds.remove(&local).unwrap_or_default());
            }
        }
        live
    }

    fn feed(&mut self, into: h::LocalId, from: h::LocalId) {
        self.feeds.entry(into).or_default().push(from);
    }

    /// `owner` is the merge or carried name what `body` reads is handed
    /// to, if any; `carried` is the innermost loop's, within a round and
    /// after the loop, which its `continue` and `break` hand on.
    fn body(
        &mut self,
        body: &h::Body,
        owner: Option<h::LocalId>,
        carried: &[(h::LocalId, h::LocalId)],
    ) {
        for binding in &body.bindings {
            let owner = match binding.pattern {
                h::Pattern::Bind(local) if self.joins.contains(&local) => Some(local),
                _ => owner,
            };
            self.expr(&binding.value, owner, carried);
        }
        self.expr(&body.result, owner, carried);
    }

    fn expr(
        &mut self,
        expression: &h::Expr,
        owner: Option<h::LocalId>,
        carried: &[(h::LocalId, h::LocalId)],
    ) {
        match &expression.kind {
            h::ExprKind::Local(local) => match owner {
                Some(owner) => self.feed(owner, *local),
                None => self.read.push(*local),
            },
            h::ExprKind::Continue(values) => {
                for (value, (within, _)) in values.iter().zip(carried) {
                    self.expr(value, Some(*within), carried);
                }
            }
            h::ExprKind::Break(values) => {
                for (value, (_, after)) in values.iter().zip(carried) {
                    self.expr(value, Some(*after), carried);
                }
            }
            h::ExprKind::Loop(looped) => {
                let inner: Vec<_> = looped
                    .carried
                    .iter()
                    .map(|(_, within, after)| (*within, *after))
                    .collect();
                for ((initial, _, _), (within, after)) in looped.carried.iter().zip(&inner) {
                    self.expr(initial, Some(*within), carried);
                    // A loop that ends of itself hands on what its round had.
                    self.feed(*after, *within);
                }
                self.expr(looped.head.value(), owner, carried);
                self.body(&looped.body, owner, &inner);
                self.body(&looped.rest, owner, carried);
            }
            h::ExprKind::Block(body) => self.body(body, owner, carried),
            _ => expression.for_each_child(|inner| self.expr(inner, owner, carried)),
        }
    }
}

/// Drops the bindings of joins nothing reads, and the names loops carry
/// that nothing reads, with what each `continue` and `break` hands them.
struct Dropper<'a> {
    joins: &'a HashSet<h::LocalId>,
    live: &'a HashSet<h::LocalId>,
}

impl Dropper<'_> {
    /// `kept` says which of the innermost loop's carried names stay.
    fn body(&self, body: &mut h::Body, kept: Option<&[bool]>) {
        body.bindings.retain(|binding| match binding.pattern {
            h::Pattern::Bind(local) => !self.joins.contains(&local) || self.live.contains(&local),
            _ => true,
        });
        for binding in &mut body.bindings {
            self.expr(&mut binding.value, kept);
        }
        self.expr(&mut body.result, kept);
    }

    fn expr(&self, expression: &mut h::Expr, kept: Option<&[bool]>) {
        match &mut expression.kind {
            h::ExprKind::Continue(values) | h::ExprKind::Break(values) => {
                if let Some(kept) = kept {
                    let mut kept = kept.iter();
                    values.retain(|_| kept.next().copied().unwrap_or(true));
                }
            }
            h::ExprKind::Loop(looped) => {
                let inner: Vec<bool> = looped
                    .carried
                    .iter()
                    .map(|(_, within, after)| {
                        self.live.contains(within) || self.live.contains(after)
                    })
                    .collect();
                let mut keep = inner.iter();
                looped
                    .carried
                    .retain(|_| keep.next().copied().unwrap_or(true));
                self.expr(looped.head.value_mut(), kept);
                self.body(&mut looped.body, Some(&inner));
                self.body(&mut looped.rest, kept);
            }
            h::ExprKind::Block(body) => self.body(body, kept),
            _ => expression.for_each_child_mut(|inner| self.expr(inner, kept)),
        }
    }
}
