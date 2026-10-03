//! Fusing a walk that builds a list with the walk that takes it apart.
//!
//! A producer walks a list and pushes one element onto an accumulator for
//! each it passes, then answers the accumulator reversed: the elements in
//! the order it made them. `map` and `trail` are written this way. A
//! consumer walks a list from the front, reading each element once and
//! going on with nothing but the rest, in tail position: `fold`, `trail`,
//! `find_index`. Where a producer's answer is read once, by a consumer, the
//! list between them need not exist. One walk over what the producer walks
//! does both steps, handing the consumer each element as the producer makes
//! it, and stops where the consumer would have stopped.
//!
//! The consumer may itself be a producer, as `trail` is, and then so is the
//! walk the two become. A chain of them therefore fuses a link at a time,
//! within one pass over each body.
//!
//! Nothing is recognized by name. A producer and a consumer are shapes of
//! equation, and a list is a type of sequence shape. Only definitions that
//! reach no bodyless call take part: fusing interleaves the two walks'
//! work, and skips what the producer would have made past where the
//! consumer stops, which only work nothing can observe may have done to it.

use std::collections::HashMap;

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::walk;
use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, SequenceOperation, TypeId};

/// Fuse every producer read once by a consumer, in every body.
pub(crate) fn fuse(program: &mut Program) {
    let recognised = program.recognised().clone();
    let mut fusion = Fusion {
        pure: pure(program),
        recognised,
        producers: HashMap::new(),
        consumers: HashMap::new(),
        fused: HashMap::new(),
        prepends: HashMap::new(),
        program,
    };
    let mut bodies = Vec::new();
    let count = fusion.program.functions().len();
    for at in 0..count {
        let id = FnId::at(at);
        if fusion.recognised.answered(id) {
            continue;
        }
        let Some(body) = fusion.program.function(id).body() else {
            continue;
        };
        if !fusion.calls_a_producer(body) {
            continue;
        }
        let params = fusion.program.params(id).len();
        let locals = (0..params).map(|at| Atom(Local::at(at))).collect();
        let rewritten = fusion.rewrite_body(body, locals, params);
        bodies.push((id, rewritten));
    }
    fusion.program.replace_bodies(bodies);
}

/// A walk building a list, as [`Fusion::producer`] reads it.
#[derive(Clone, Copy)]
struct Producer {
    /// The parameter it walks, and the one it pushes onto.
    list: usize,
    acc: usize,
}

/// A walk taking a list apart, as [`Fusion::consumer`] reads it.
#[derive(Clone, Copy)]
struct Consumer {
    list: usize,
}

/// A fused walk, and where its producer's and consumer's parameters are.
struct Pair {
    id: FnId,
    /// The list the producer walks, which the fused walk walks.
    list: usize,
    /// The producer's accumulator and the consumer's list, which the fused
    /// walk has no parameter for.
    acc: usize,
    taken: usize,
    consumer: FnId,
    /// The fused walk's parameter each of theirs is, by position.
    p_locals: Vec<Atom>,
    c_locals: Vec<Atom>,
    arity: usize,
}

/// A producer's call, held back until its one reader is written.
#[derive(Clone)]
struct Deferred {
    callee: FnId,
    /// Its arguments as the source wrote them, and as rewritten.
    written: Vec<Atom>,
    args: Vec<Atom>,
}

struct Fusion<'a> {
    program: &'a mut Program,
    recognised: Recognised,
    /// Whether each function reaches no bodyless call.
    pure: Vec<bool>,
    producers: HashMap<FnId, Option<Producer>>,
    consumers: HashMap<FnId, Option<Consumer>>,
    fused: HashMap<(FnId, FnId), FnId>,
    /// The definition putting one sequence of each type before another in
    /// order, found or written the first time it is wanted.
    prepends: HashMap<TypeId, FnId>,
}

/// A local no fused body may read: what a parameter or field the fused walk
/// has no use for stands for, so that reading one fails validation rather
/// than reading something else.
const UNREAD: Atom = Atom(Local(u32::MAX));

impl Fusion<'_> {
    /// Whether anything in a body calls a producer, which is all that makes
    /// rewriting it worth a copy.
    fn calls_a_producer(&mut self, body: Body) -> bool {
        #[expect(
            clippy::needless_collect,
            reason = "asking whether a callee is a producer caches the answer, which the walk's borrow forbids"
        )]
        let callees: Vec<FnId> = walk::within(self.program, body)
            .filter_map(|id| match self.program.expr(id) {
                Expr::Call(callee, _) => Some(callee),
                _ => None,
            })
            .collect();
        callees
            .into_iter()
            .any(|callee| self.producer(callee).is_some() || self.reversal(callee))
    }

    /// Whether `id` is a producer:
    ///
    /// ```text
    /// p(.. list .. acc ..) = match list
    ///   empty => ...; reverse(acc, <empty>)
    ///   push(x, rest) => ...; next = push(e, acc); p(.. next ..)
    /// ```
    ///
    /// where `acc` is read nowhere else, and `reverse` is a reversal; or the
    /// same building front to back, as [`super::forward`] writes a walk,
    /// `append(acc, e)` for the push and `prepend(acc, <empty>)`, or `acc`
    /// itself, at the end. What it goes on walking is its own: the rest, or
    /// whatever its step worked out. Its call may stand inside matches of
    /// one arm ending the step.
    fn producer(&mut self, id: FnId) -> Option<Producer> {
        if let Some(&known) = self.producers.get(&id) {
            return known;
        }
        let found = self.find_producer(id);
        self.producers.insert(id, found);
        found
    }

    #[expect(
        clippy::too_many_lines,
        reason = "each condition of the producer shape is one early return, read in order"
    )]
    fn find_producer(&self, id: FnId) -> Option<Producer> {
        if !self.takes_part(id) {
            return None;
        }
        let body = self.program.function(id).body()?;
        let (list, arms) = walk::top_match(self.program, body)?;
        let params = self.program.params(id);
        let (empty, push, _) = super::sequence::sequence(self.program, params[list])?;
        let arity = params.len();
        let [nil_arm, push_arm] = walk::split_arms(self.program, arms, empty, push)?;
        // The empty arm answers the accumulator reversed or prepended onto
        // nothing -- or, built front to back, the accumulator itself, which
        // is what prepending it onto nothing answers.
        let (acc, ended) = match self.program.expr(nil_arm.body.tail) {
            Expr::Atom(Atom(acc)) => (acc.index(), None),
            Expr::Call(reverse, args) => {
                let &[Atom(acc), Atom(onto)] = self.program.atoms(args) else {
                    return None;
                };
                (acc.index(), Some((reverse, onto)))
            }
            _ => return None,
        };
        if acc >= arity || acc == list {
            return None;
        }
        // What it builds is a list too, but not necessarily of what it walks.
        let (built_empty, built_push, built_recursive) =
            super::sequence::sequence(self.program, params[acc])?;
        if let Some((reverse, onto)) = ended {
            let ends = super::sequence::reverses(self.program, reverse)
                || self.recognised.sequences.get(reverse.index())
                    == Some(&Some(SequenceOperation::Prepend));
            let onto = walk::bound(self.program, nil_arm.body, arity, onto.index())?;
            if !ends || !self.empty_constant(onto, built_empty) {
                return None;
            }
        }
        // The push arm pushes one element onto it, and goes on, maybe
        // inside matches of one arm taking apart what it goes on with. What
        // it goes on walking is its own affair: the consumer is handed
        // what it pushed, wherever that came from.
        let push_body = push_arm.body;
        let (inner, base) = innermost(self.program, push_body, arity + 2);
        let Expr::Call(again, args) = self.program.expr(inner.tail) else {
            return None;
        };
        if again != id {
            return None;
        }
        let args = self.program.atoms(args);
        if args.len() != arity {
            return None;
        }
        let pushed = walk::bound(self.program, inner, base, args[acc].0.index())?;
        self.pushed_element(pushed, acc, (built_push, built_recursive))?;
        // Answered as it stands, it must have been built in order.
        if ended.is_none() && !self.appends(pushed) {
            return None;
        }
        // Nothing else reads the accumulator, or the list it pushed onto.
        let next = args[acc].0.index();
        let reads = self.reads(push_body, acc) + self.reads(nil_arm.body, acc);
        (reads == 2 && self.reads_after(inner, base, next) == 1).then_some(Producer { list, acc })
    }

    /// The element `expr` puts onto the accumulator at level `acc`: a push
    /// in front of it, or an append after it.
    fn pushed_element(
        &self,
        expr: ExprId,
        acc: usize,
        (push, recursive): (super::CtorId, usize),
    ) -> Option<Atom> {
        match self.program.expr(expr) {
            Expr::Con(ctor, fields) => {
                let fields = self.program.atoms(fields);
                (ctor == push && fields[recursive].0.index() == acc).then(|| fields[1 - recursive])
            }
            Expr::Call(callee, args) => {
                let &[onto, element] = self.program.atoms(args) else {
                    return None;
                };
                let appends = self.recognised.sequences.get(callee.index())
                    == Some(&Some(SequenceOperation::Append));
                (appends && onto.0.index() == acc).then_some(element)
            }
            Expr::Atom(_) | Expr::Static(_) | Expr::Match(..) => None,
        }
    }

    /// Whether `expr` appends to what it builds, rather than pushing in
    /// front of it.
    fn appends(&self, expr: ExprId) -> bool {
        matches!(
            self.program.expr(expr),
            Expr::Call(callee, _) if self.recognised.sequences.get(callee.index())
                == Some(&Some(SequenceOperation::Append))
        )
    }

    /// Whether a definition may be fused at all: it reaches no bodyless
    /// call, and is not answered as an operation it was recognized as.
    /// A definition this pass made was neither.
    fn takes_part(&self, id: FnId) -> bool {
        self.pure[id.index()]
            && (id.index() >= self.recognised.operations.len() || !self.recognised.answered(id))
    }

    /// Whether `id` is a consumer:
    ///
    /// ```text
    /// c(.. list ..) = match list
    ///   empty => ...
    ///   push(x, rest) => ... c(.. rest ..) ... c(.. rest ..) ...
    /// ```
    ///
    /// where `rest` is read only as that argument of calls in tail position,
    /// and `list` is read only by the match.
    fn consumer(&mut self, id: FnId) -> Option<Consumer> {
        if let Some(&known) = self.consumers.get(&id) {
            return known;
        }
        let found = self.find_consumer(id);
        self.consumers.insert(id, found);
        found
    }

    fn find_consumer(&self, id: FnId) -> Option<Consumer> {
        if !self.takes_part(id) {
            return None;
        }
        let body = self.program.function(id).body()?;
        let (list, arms) = walk::top_match(self.program, body)?;
        let params = self.program.params(id);
        let (empty, push, recursive) = super::sequence::sequence(self.program, params[list])?;
        let arity = params.len();
        let [nil_arm, push_arm] = walk::split_arms(self.program, arms, empty, push)?;
        if self.reads(nil_arm.body, list) + self.reads(push_arm.body, list) != 0 {
            return None;
        }
        let rest = arity + recursive;
        let tails = self.tail_reads(push_arm.body, id, list, rest)?;
        (tails == self.reads(push_arm.body, rest)).then_some(Consumer { list })
    }

    /// How many calls of `id` in tail position of `body` read `rest` as
    /// their `list` argument; nothing where `rest` is read in tail position
    /// any other way.
    fn tail_reads(&self, body: Body, id: FnId, list: usize, rest: usize) -> Option<usize> {
        match self.program.expr(body.tail) {
            Expr::Call(callee, args) => {
                let args = self.program.atoms(args);
                let here = args.iter().filter(|atom| atom.0.index() == rest).count();
                if callee == id && args[list].0.index() == rest && here == 1 {
                    Some(1)
                } else {
                    Some(0)
                }
            }
            Expr::Match(_, arms) => self
                .program
                .arms(arms)
                .iter()
                .map(|arm| self.tail_reads(arm.body, id, list, rest))
                .sum(),
            Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => Some(0),
        }
    }

    /// Whether an expression is the empty list: `empty` applied, or a known
    /// value built by it, which is what folding makes of the first.
    fn empty_constant(&self, expr: ExprId, empty: super::CtorId) -> bool {
        match self.program.expr(expr) {
            Expr::Con(ctor, _) => ctor == empty,
            Expr::Static(value) => self.program.constant(value).constructor() == empty,
            Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => false,
        }
    }

    /// How many times `body` reads local `level`, which is bound before any
    /// of it: in its bindings, its tail, and every arm in them. Arms bind
    /// only levels past it, so a read of `level` anywhere is this one.
    fn reads(&self, body: Body, level: usize) -> usize {
        walk::reads(self.program, walk::within(self.program, body), level)
    }

    /// How many times the bindings of `body` after its binding at `level`,
    /// and its tail, read that binding. Its first binding takes `base`. An
    /// arm of an earlier binding may bind the same level for itself.
    fn reads_after(&self, body: Body, base: usize, level: usize) -> usize {
        let later = &self.program.bindings(body.bindings)[level + 1 - base..];
        let exprs = walk::nested(self.program, later.iter().copied().chain([body.tail]));
        walk::reads(self.program, exprs, level)
    }

    /// The function walking what `producer` walks and doing what `consumer`
    /// does with each element it would have pushed, made the first time it
    /// is asked for.
    ///
    /// Its parameters are the producer's but its accumulator, then the
    /// consumer's but its list.
    fn fused(&mut self, producer: FnId, consumer: FnId) -> FnId {
        if let Some(&id) = self.fused.get(&(producer, consumer)) {
            return id;
        }
        let made = self.fuse_pair(producer, consumer);
        self.fused.insert((producer, consumer), made);
        made
    }

    fn fuse_pair(&mut self, producer: FnId, consumer: FnId) -> FnId {
        let pair = self.declared(producer, consumer);
        let p_body = self.program.function(producer).body().expect("a producer");
        let c_body = self.program.function(consumer).body().expect("a consumer");
        let list = pair.list;
        let (_, p_arms) = walk::top_match(self.program, p_body).expect("a producer's match");
        let (_, c_arms) = walk::top_match(self.program, c_body).expect("a consumer's match");
        let walked = self.program.params(producer)[list];
        let (empty, push, recursive) =
            super::sequence::sequence(self.program, walked).expect("a list");
        let taken = self.program.params(consumer)[pair.taken];
        let (c_empty, c_push, _) = super::sequence::sequence(self.program, taken).expect("a list");
        let [_, p_step] = walk::split_arms(self.program, p_arms, empty, push).expect("two arms");
        let [c_nil, c_step] =
            walk::split_arms(self.program, c_arms, c_empty, c_push).expect("two arms");
        let mut arms = Vec::new();
        for arm in self.program.arms(p_arms).to_vec() {
            let body = if arm.ctor == empty {
                // No more elements: the consumer is handed an empty list.
                let locals = pair.c_locals.clone();
                copy::body(self.program, c_nil.body, locals, pair.arity, None)
            } else {
                self.step(&pair, (p_step, recursive), c_step)
            };
            arms.push(Arm {
                ctor: arm.ctor,
                body,
            });
        }
        let arms = self.program.terms.hold_arms(&arms);
        let tail = self
            .program
            .terms
            .push(Expr::Match(pair.p_locals[list], arms));
        let body = self.program.terms.hold_body(&[], tail);
        self.program.replace_bodies(vec![(pair.id, body)]);
        self.pure.push(true);
        pair.id
    }

    /// Declare the walk fusing `producer` into `consumer`, and say where each
    /// of their parameters is in it.
    fn declared(&mut self, producer: FnId, consumer: FnId) -> Pair {
        let Producer { list, acc } = self.producers[&producer].expect("a producer");
        let Consumer { list: taken } = self.consumers[&consumer].expect("a consumer");
        let but = |params: &[TypeId], skip: usize| -> Vec<TypeId> {
            params
                .iter()
                .enumerate()
                .filter(|&(at, _)| at != skip)
                .map(|(_, &ty)| ty)
                .collect()
        };
        let mut params = but(self.program.params(producer), acc);
        let before = params.len();
        params.extend(but(self.program.params(consumer), taken));
        let name = format!(
            "{}+{}",
            self.program.name(self.program.function(producer).name),
            self.program.name(self.program.function(consumer).name)
        );
        let result = self.program.function(consumer).result;
        let id = self.program.declare(&name, &params, result);
        // Each is the next of the fused walk's, but the one it has no use for.
        let placed = |count: usize, skip: usize, from: usize| -> Vec<Atom> {
            (0..count)
                .map(|at| match at.cmp(&skip) {
                    std::cmp::Ordering::Less => Atom(Local::at(from + at)),
                    std::cmp::Ordering::Equal => UNREAD,
                    std::cmp::Ordering::Greater => Atom(Local::at(from + at - 1)),
                })
                .collect()
        };
        Pair {
            id,
            list,
            acc,
            taken,
            consumer,
            p_locals: placed(self.program.params(producer).len(), acc, 0),
            c_locals: placed(self.program.params(consumer).len(), taken, before),
            arity: params.len(),
        }
    }

    /// The fused walk's step: the producer's step, but for its push and its
    /// call, then the consumer's step on the element it would have pushed,
    /// going on with the fused walk wherever the consumer went on with
    /// itself.
    fn step(&mut self, pair: &Pair, (p_step, walked): (Arm, usize), c_step: Arm) -> Body {
        let arity = pair.arity;
        let mut locals = pair.p_locals.clone();
        locals.extend([Atom(Local::at(arity)), Atom(Local::at(arity + 1))]);
        // The rest of what the producer walks, which is the fused walk's.
        let rest = Atom(Local::at(arity + walked));
        self.step_body(pair, p_step.body, locals, arity + 2, (rest, c_step))
    }

    /// The producer's step `body`, whose locals so far `locals` maps, its
    /// first binding at `level` in the fused walk: down through each match
    /// of one arm it ends with, to where it pushes and goes on, which goes
    /// on as the consumer's step instead.
    fn step_body(
        &mut self,
        pair: &Pair,
        body: Body,
        mut locals: Vec<Atom>,
        level: usize,
        (rest, c_step): (Atom, Arm),
    ) -> Body {
        let mut scope = Scope::at(level);
        let Expr::Match(on, arms) = self.program.expr(body.tail) else {
            return self.pushing(pair, body, locals, scope, (rest, c_step));
        };
        let &[arm] = self.program.arms(arms) else {
            unreachable!("a producer's step ends in matches of one arm, then its call");
        };
        for binding in self.program.bindings(body.bindings).to_vec() {
            let value = copy::expr(self.program, binding, &locals, &mut scope, None);
            locals.push(value);
        }
        let fields = self.program.fields(arm.ctor).len();
        let mut inner = locals.clone();
        inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
        let taken = self.step_body(pair, arm.body, inner, scope.level + fields, (rest, c_step));
        let arms = self.program.terms.hold_arms(&[Arm {
            ctor: arm.ctor,
            body: taken,
        }]);
        let answer = copy::push(
            self.program,
            &mut scope,
            Expr::Match(locals[on.0.index()], arms),
        );
        copy::close(self.program, scope, answer)
    }

    /// The body where the producer pushes and goes on, copied into `scope`
    /// but for its push and its call, then the consumer's step on the
    /// element it would have pushed.
    #[expect(
        clippy::too_many_lines,
        reason = "the producer step, the element, and the consumer step are copied into one scope in order"
    )]
    fn pushing(
        &mut self,
        pair: &Pair,
        body: Body,
        mut locals: Vec<Atom>,
        mut scope: Scope,
        (rest, c_step): (Atom, Arm),
    ) -> Body {
        let (_, _, recursive) =
            super::sequence::sequence(self.program, self.program.params(pair.consumer)[pair.taken])
                .expect("a list");
        let Expr::Call(_, again) = self.program.expr(body.tail) else {
            unreachable!("a producer's step calls itself")
        };
        let again = self.program.atoms(again).to_vec();
        // The producer's own level of this body's first binding.
        let pushed = again[pair.acc].0.index() - locals.len();
        let bindings = self.program.bindings(body.bindings).to_vec();
        for (at, &binding) in bindings.iter().enumerate() {
            let value = if at == pushed {
                UNREAD
            } else {
                copy::expr(self.program, binding, &locals, &mut scope, None)
            };
            locals.push(value);
        }
        // What it pushed in front, or appended after.
        let element = match self.program.expr(bindings[pushed]) {
            Expr::Con(_, fields) => self.program.atoms(fields)[1 - recursive],
            Expr::Call(_, args) => self.program.atoms(args)[1],
            _ => unreachable!("a producer pushes or appends"),
        };
        let element = locals[element.0.index()];
        // What the producer goes on with, but for the list it is building:
        // that is what the consumer is handed instead.
        let going_on: Vec<_> = again
            .iter()
            .enumerate()
            .filter(|&(at, _)| at != pair.acc)
            .map(|(_, atom)| locals[atom.0.index()])
            .collect();
        let mut consumed = pair.c_locals.clone();
        consumed.extend((0..2).map(|at| if at == recursive { rest } else { element }));
        // The consumer going round on the rest of the list goes round as
        // the fused walk, on what the producer goes on with.
        let (going_round, taken, fused) = (pair.consumer, pair.taken, pair.id);
        let mut redirect = |program: &mut Program, _: ExprId, expr: Expr| match expr {
            Expr::Call(callee, args)
                if callee == going_round && program.atoms(args)[taken] == rest =>
            {
                let mut going = going_on.clone();
                going.extend(
                    program
                        .atoms(args)
                        .iter()
                        .enumerate()
                        .filter(|&(at, _)| at != taken)
                        .map(|(_, &atom)| atom),
                );
                Expr::Call(fused, program.terms.hold_atoms(going.into_iter()))
            }
            other => other,
        };
        let answer = copy::into(
            self.program,
            c_step.body,
            consumed,
            &mut scope,
            Some(&mut redirect),
        );
        copy::close(self.program, scope, answer)
    }

    /// A sequence reversed onto nothing, `made`, and reversed again onto
    /// another by `callee`, is put before that other in order.
    fn prepended(
        &mut self,
        callee: FnId,
        made: &Deferred,
        written: &[Atom],
        args: &[Atom],
    ) -> Deferred {
        debug_assert!(
            self.reversal(made.callee),
            "only a reversal is deferred for one"
        );
        let ty = self.program.params(callee)[0];
        Deferred {
            callee: self.prepending(ty, callee),
            written: vec![made.written[0], written[1]],
            args: vec![made.args[0], args[1]],
        }
    }

    /// Whether `id` is recognized as reversing one sequence onto another.
    fn reversal(&self, id: FnId) -> bool {
        self.recognised.sequences.get(id.index()) == Some(&Some(SequenceOperation::ReverseOnto))
    }

    /// Whether a reversal onto nothing is read once, by another reversal
    /// later in the same body, as what it reverses.
    fn reversed_twice(&self, call: &Deferred, body: Body, base: usize, level: usize) -> bool {
        let Some(onto) = walk::bound(self.program, body, base, call.written[1].0.index()) else {
            return false;
        };
        let Some((empty, _, _)) =
            super::sequence::sequence(self.program, self.program.params(call.callee)[1])
        else {
            return false;
        };
        if !self.empty_constant(onto, empty) || self.reads_after(body, base, level) != 1 {
            return false;
        }
        let mut rest = self.program.bindings(body.bindings)[level + 1 - base..].to_vec();
        rest.push(body.tail);
        rest.into_iter().any(|id| {
            let Expr::Call(callee, args) = self.program.expr(id) else {
                return false;
            };
            self.reversal(callee) && self.program.atoms(args)[0].0.index() == level
        })
    }

    /// The definition recognized as putting one sequence of type `ty` before
    /// another in order, or one written here as `reverse` reversed onto
    /// nothing and reversed again, which is recognized as one.
    fn prepending(&mut self, ty: TypeId, reverse: FnId) -> FnId {
        if let Some(&id) = self.prepends.get(&ty) {
            return id;
        }
        let found =
            self.recognised
                .sequence_over(self.program, SequenceOperation::Prepend, &[ty, ty]);
        let id = found.unwrap_or_else(|| {
            let id = super::sequence::write_prepend(self.program, ty, reverse);
            self.pure.push(true);
            id
        });
        self.prepends.insert(ty, id);
        id
    }

    /// Rewrite a body, fusing each producer read once by a consumer.
    fn rewrite_body(&mut self, body: Body, locals: Vec<Atom>, level: usize) -> Body {
        let mut scope = Scope::at(level);
        let answer = self.rewrite_into(body, locals, &mut scope, level);
        copy::close(self.program, scope, answer)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one walk rewrites calls and rebuilds arms, sharing the deferred producers"
    )]
    fn rewrite_into(
        &mut self,
        body: Body,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
        base: usize,
    ) -> Atom {
        let bindings = self.program.bindings(body.bindings).to_vec();
        let mut deferred: HashMap<usize, Deferred> = HashMap::new();
        let count = bindings.len();
        for (at, &binding) in bindings
            .iter()
            .chain(std::iter::once(&body.tail))
            .enumerate()
        {
            let level = base + at;
            let value = match self.program.expr(binding) {
                Expr::Call(callee, args) => {
                    let written = self.program.atoms(args).to_vec();
                    let mapped: Vec<_> = written.iter().map(|a| locals[a.0.index()]).collect();
                    let call = self.fusing(callee, &written, &mapped, &mut deferred);
                    if at < count && self.defers(&call, body, base, level) {
                        deferred.insert(level, call);
                        UNREAD
                    } else {
                        let args = self.program.terms.hold_atoms(call.args.into_iter());
                        copy::push(self.program, scope, Expr::Call(call.callee, args))
                    }
                }
                Expr::Match(on, arms) => {
                    let mut rebuilt = Vec::new();
                    for arm in self.program.arms(arms).to_vec() {
                        let fields = self.program.fields(arm.ctor).len();
                        let mut inner = locals.clone();
                        inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
                        let mut arm_scope = Scope::at(scope.level + fields);
                        let answer =
                            self.rewrite_into(arm.body, inner, &mut arm_scope, level + fields);
                        rebuilt.push(Arm {
                            ctor: arm.ctor,
                            body: copy::close(self.program, arm_scope, answer),
                        });
                    }
                    let arms = self.program.terms.hold_arms(&rebuilt);
                    copy::push(self.program, scope, Expr::Match(locals[on.0.index()], arms))
                }
                _ => copy::expr(self.program, binding, &locals, scope, None),
            };
            locals.push(value);
        }
        locals.pop().expect("a body answers")
    }

    /// A call as written, or fused with the producer it reads.
    fn fusing(
        &mut self,
        callee: FnId,
        written: &[Atom],
        args: &[Atom],
        deferred: &mut HashMap<usize, Deferred>,
    ) -> Deferred {
        let plain = Deferred {
            callee,
            written: written.to_vec(),
            args: args.to_vec(),
        };
        if self.reversal(callee)
            && let Some(made) = deferred.remove(&written[0].0.index())
        {
            return self.prepended(callee, &made, written, args);
        }
        let Some(Consumer { list: taken }) = self.consumer(callee) else {
            return plain;
        };
        let Some(made) = deferred.remove(&written[taken].0.index()) else {
            return plain;
        };
        let Producer { acc, .. } = self.producer(made.callee).expect("deferred producers are");
        let fused = self.fused(made.callee, callee);
        let others = |held: &[Atom], skip: usize| -> Vec<Atom> {
            held.iter()
                .enumerate()
                .filter(|&(at, _)| at != skip)
                .map(|(_, &atom)| atom)
                .collect()
        };
        let mut written_args = others(&made.written, acc);
        written_args.extend(others(written, taken));
        let mut mapped = others(&made.args, acc);
        mapped.extend(others(args, taken));
        // The fused walk may produce in turn, which it does where the
        // consumer did; it is asked again as it stands.
        self.producers.remove(&fused);
        self.consumers.remove(&fused);
        Deferred {
            callee: fused,
            written: written_args,
            args: mapped,
        }
    }

    /// Whether a call is a producer's, building onto nothing, whose answer
    /// is read once and by a consumer's call later in the same body.
    fn defers(&mut self, call: &Deferred, body: Body, base: usize, level: usize) -> bool {
        if self.reversal(call.callee) {
            return self.reversed_twice(call, body, base, level);
        }
        let Some(Producer { acc, .. }) = self.producer(call.callee) else {
            return false;
        };
        let Some(onto) = walk::bound(self.program, body, base, call.written[acc].0.index()) else {
            return false;
        };
        let Some((empty, _, _)) =
            super::sequence::sequence(self.program, self.program.params(call.callee)[acc])
        else {
            return false;
        };
        if !self.empty_constant(onto, empty) || self.reads_after(body, base, level) != 1 {
            return false;
        }
        let mut rest = self.program.bindings(body.bindings)[level + 1 - base..].to_vec();
        rest.push(body.tail);
        rest.into_iter().any(|id| {
            let Expr::Call(callee, args) = self.program.expr(id) else {
                return false;
            };
            let args = self.program.atoms(args).to_vec();
            self.consumer(callee)
                .is_some_and(|Consumer { list }| args[list].0.index() == level)
        })
    }
}

/// The body a step ends in, down through each match of one arm it ends
/// with, and the level of that body's first binding, where `body`'s is at
/// `base`.
fn innermost(program: &Program, mut body: Body, mut base: usize) -> (Body, usize) {
    while let Expr::Match(_, arms) = program.expr(body.tail)
        && let &[arm] = program.arms(arms)
    {
        base += program.bindings(body.bindings).len() + program.fields(arm.ctor).len();
        body = arm.body;
    }
    (body, base)
}

/// Whether each function reaches no bodyless call, by function.
fn pure(program: &Program) -> Vec<bool> {
    let mut pure: Vec<bool> = program
        .functions()
        .iter()
        .map(|function| function.body().is_some())
        .collect();
    let callees = super::calls::graph(program);
    loop {
        let mut changed = false;
        for (at, callees) in callees.iter().enumerate() {
            if pure[at] && callees.iter().any(|callee| !pure[callee.index()]) {
                pure[at] = false;
                changed = true;
            }
        }
        if !changed {
            return pure;
        }
    }
}
