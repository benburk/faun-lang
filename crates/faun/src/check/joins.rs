//! Where ways meet: the branches of an `if`, the arms of an `is`, and what
//! a clause or lambda answers, by its body and its `return`s. Each way
//! answers the join's type, except one whose type is `[]`, the empty tag
//! row: it never answers, so it takes the type the others answer. Where
//! every way is `[]`, the join is too.
//!
//! The rule is one way: a value of another type never flows into `[]`. A
//! way whose type is not yet known where it stands, a call whose receiver
//! or callee is still being worked out, waits for it, and is settled with
//! what else waits. One still unknown when the line holding it, or its
//! clause or group of definitions, takes its defaults answers the join's
//! type, as any way does: a call through a generic receiver, whose answer
//! is `[]` only once a caller says what the receiver is, is one.

use std::rc::Rc;

use super::unify::Ty;
use super::{Checker, Marks};
use crate::ModuleId;
use crate::ast::Span;
use crate::diagnostic::{Advised, Refusal};
use crate::hir as h;

/// A join's ways, as far as they are known.
#[derive(Clone, Debug)]
pub(super) struct Join {
    module: ModuleId,
    span: Span,
    /// What the join answers.
    answer: Ty,
    /// Whether a way of a type other than `[]` met the answer, or the
    /// answer was decided before any way did, as a signature decides it.
    met: bool,
    /// How many ways wait for their type.
    waiting: usize,
    /// Whether every way is in.
    closed: bool,
}

/// How a way's value meets its join's answer.
#[derive(Clone, Copy, Debug)]
pub(super) enum Meeting {
    /// Unified, with a note on what must agree where they do not.
    Unified(Option<&'static str>),
    /// Subsumed, as a clause's body meets its signature: a closed row may
    /// be widened where it is answered, at this site.
    Subsumed(h::SiteId),
}

/// A way whose type was not known where it stood.
#[derive(Clone, Debug)]
pub(super) struct PendingWay {
    join: usize,
    module: ModuleId,
    span: Span,
    ty: Ty,
    meeting: Meeting,
    resolved: bool,
}

/// Whether `ty`, resolved, is `[]`.
fn never(ty: &Ty) -> bool {
    matches!(ty, Ty::Variants(tags, None) if tags.is_empty())
}

/// Whether `expression` may turn out never to answer once what it waits
/// on is settled: a call, or what answers one. A word or tag applied
/// builds a value, and its position is what decides its reading.
pub(super) fn may_never_answer(expression: &h::Expr) -> bool {
    match &expression.kind {
        h::ExprKind::Call(head, _) => !matches!(
            head.kind,
            h::ExprKind::Constructor(_) | h::ExprKind::Dual(_) | h::ExprKind::Tag(_)
        ),
        h::ExprKind::Method(..)
        | h::ExprKind::Member(..)
        | h::ExprKind::Associated(..)
        | h::ExprKind::Try(_)
        | h::ExprKind::If(..)
        | h::ExprKind::Match(..) => true,
        h::ExprKind::Block(body) => may_never_answer(&body.result),
        h::ExprKind::Loop(looped) => may_never_answer(&looped.rest.result),
        _ => false,
    }
}

impl Checker<'_> {
    /// A join answering `answer`, at `span`. An answer already decided,
    /// as a signature's is, counts as a way of its type.
    pub(super) fn join(&mut self, module: ModuleId, span: Span, answer: Ty) -> usize {
        let met = !matches!(self.infer.resolve(&answer), Ty::Var(_));
        self.joins.push(Join {
            module,
            span,
            answer,
            met,
            waiting: 0,
            closed: false,
        });
        self.joins.len() - 1
    }

    pub(super) fn join_answer(&self, join: usize) -> Ty {
        self.joins[join].answer.clone()
    }

    /// Note that a way of another type than `[]` met `join`'s answer, as a
    /// `?` does when it answers an `Err` early.
    pub(super) fn join_met(&mut self, join: usize) {
        self.joins[join].met = true;
    }

    /// The way `expression`, of type `ty`, into `join`: skipped where it
    /// is `[]`, waiting where it may yet be, and otherwise meeting the
    /// answer.
    pub(super) fn way(
        &mut self,
        join: usize,
        module: ModuleId,
        expression: &h::Expr,
        ty: &Ty,
        meeting: Meeting,
    ) -> Result<(), Refusal> {
        let resolved = self.infer.resolve(ty);
        if never(&resolved) {
            return Ok(());
        }
        if matches!(resolved, Ty::Var(_)) && may_never_answer(expression) {
            self.joins[join].waiting += 1;
            self.pending_ways.push(PendingWay {
                join,
                module,
                span: expression.span,
                ty: ty.clone(),
                meeting,
                resolved: false,
            });
            return Ok(());
        }
        self.meet(join, module, expression.span, ty, meeting)
    }

    /// Every way of `join` is in: where none waits, it is decided.
    pub(super) fn close_join(&mut self, join: usize) -> Result<(), Refusal> {
        self.joins[join].closed = true;
        self.decide(join)
    }

    /// A way's value meeting its join's answer.
    fn meet(
        &mut self,
        join: usize,
        module: ModuleId,
        span: Span,
        ty: &Ty,
        meeting: Meeting,
    ) -> Result<(), Refusal> {
        self.joins[join].met = true;
        let answer = self.joins[join].answer.clone();
        match meeting {
            Meeting::Unified(note) => {
                self.unify_at(module, span, ty, &answer)
                    .map_err(|error| match note {
                        Some(note) => error.note(note),
                        None => error,
                    })
            }
            Meeting::Subsumed(site) => {
                let widened = self
                    .infer
                    .subsume(ty, &answer)
                    .map_err(|reason| self.mismatch(module, span, ty, &answer, &reason))?;
                if widened {
                    self.widenings.push((module, span, site, answer));
                }
                Ok(())
            }
        }
    }

    /// A join every way of which is in and known: where each was `[]`,
    /// so is the answer.
    fn decide(&mut self, join: usize) -> Result<(), Refusal> {
        let Join {
            module,
            span,
            ref answer,
            met,
            waiting,
            closed,
        } = self.joins[join];
        if !closed || waiting > 0 || met {
            return Ok(());
        }
        let answer = answer.clone();
        let never = Ty::Variants(Rc::default(), None);
        self.unify_at(module, span, &never, &answer)
    }

    /// Settle each way since `marks` whose type is now known, or with
    /// `flush`, every one: what is still unknown answers its join's type.
    /// Answers whether any was settled.
    pub(super) fn settle_ways(&mut self, marks: Marks, flush: bool) -> Result<bool, Refusal> {
        let mut progress = false;
        loop {
            let mut moved = false;
            for index in marks.ways..self.pending_ways.len() {
                let way = self.pending_ways[index].clone();
                if way.resolved {
                    continue;
                }
                let resolved = self.infer.resolve(&way.ty);
                if matches!(resolved, Ty::Var(_)) && !flush {
                    continue;
                }
                self.pending_ways[index].resolved = true;
                self.joins[way.join].waiting -= 1;
                if !never(&resolved) {
                    self.meet(way.join, way.module, way.span, &way.ty, way.meeting)?;
                }
                self.decide(way.join)?;
                moved = true;
            }
            if !moved {
                return Ok(progress);
            }
            progress = true;
        }
    }
}
