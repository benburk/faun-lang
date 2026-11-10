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

use super::unify::{Mismatch, Ty, show};
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
    ways: Ways,
    /// What the join answers.
    answer: Ty,
    /// Each way that met the answer, and its type, in the order they met.
    answered: Vec<(Span, Ty)>,
    /// Whether a way of a type other than `[]` met the answer, or the
    /// answer was decided before any way did, as a signature decides it.
    met: bool,
    /// How many ways wait for their type.
    waiting: usize,
    /// Whether every way is in.
    closed: bool,
}

/// What a join's ways are, which says why one that does not fit was
/// wanted to be of the type it was.
#[derive(Clone, Copy, Debug)]
pub(super) enum Ways {
    /// The branches of an `if`.
    Branches,
    /// The arms of an `is`, taking apart the value at this span.
    Arms(Span),
    /// What a clause or lambda answers, by its body and its `return`s, and
    /// where its signature writes that type, where one does.
    Answers(Option<Span>),
}

/// How a way's value meets its join's answer.
#[derive(Clone, Copy, Debug)]
pub(super) enum Meeting {
    /// Unified.
    Unified,
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
        _ => false,
    }
}

impl Checker<'_> {
    /// A join answering `answer`, at `span`. An answer already decided,
    /// as a signature's is, counts as a way of its type.
    pub(super) fn join(&mut self, module: ModuleId, span: Span, ways: Ways, answer: Ty) -> usize {
        let met = !matches!(self.infer.resolve(&answer), Ty::Var(_));
        self.joins.push(Join {
            module,
            span,
            ways,
            answer,
            answered: Vec::new(),
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
            Meeting::Unified => self
                .infer
                .unify(ty, &answer)
                .map_err(|reason| self.unmet(join, module, span, ty, &reason))?,
            Meeting::Subsumed(site) => {
                let widened = self
                    .infer
                    .subsume(ty, &answer)
                    .map_err(|reason| self.unmet(join, module, span, ty, &reason))?;
                if widened {
                    self.widenings.push((module, span, site, answer));
                }
            }
        }
        self.joins[join].answered.push((span, ty.clone()));
        Ok(())
    }

    /// Why a way at `span`, of type `ty`, does not meet `join`'s answer,
    /// pointing as Rust does at what made the answer the type it is: the
    /// branch before it, the arms before it, or the signature.
    fn unmet(
        &self,
        join: usize,
        module: ModuleId,
        span: Span,
        ty: &Ty,
        reason: &Mismatch,
    ) -> Refusal {
        let Join {
            module: at,
            ways,
            ref answer,
            ref answered,
            ..
        } = self.joins[join];
        let refused = self.mismatch(module, span, ty, answer, reason);
        let shown = |ty: &Ty| show(&self.infer.resolve(ty), self.symbols);
        let among = matches!(reason, Mismatch::NotAmong { .. });
        match ways {
            Ways::Branches if !among => match answered.first() {
                Some((first, _)) => refused
                    .retitled("`if` and `else` have incompatible types")
                    .also(at, *first, "expected because of this"),
                None => refused,
            },
            Ways::Arms(tested) if !among => answered.iter().fold(
                refused.retitled("`is` arms have incompatible types").also(
                    at,
                    tested,
                    "`is` arms have incompatible types",
                ),
                |refused, (arm, ty)| {
                    refused.also(
                        at,
                        *arm,
                        format!("this is found to be of type `{}`", shown(ty)),
                    )
                },
            ),
            Ways::Answers(Some(written)) => {
                let refused = refused.also(
                    at,
                    written,
                    format!("expected `{}` because of return type", shown(answer)),
                );
                // Nothing answers `[]`, so a body of that type ends by
                // leaving, as an exit does.
                if never(&self.infer.resolve(answer)) {
                    refused.help("end it with a call that never answers, as `host.exit!(0)`")
                } else {
                    refused
                }
            }
            Ways::Branches | Ways::Arms(_) | Ways::Answers(None) => refused,
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
            ..
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
