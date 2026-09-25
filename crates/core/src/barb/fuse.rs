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

use super::copy::{self, Redirect, Scope};
use super::facts::Recognised;
use super::{Arm, Atom, Body, Expr, ExprId, FnId, Local, Program, Range, TypeId, TypeShape};

/// Fuse every producer read once by a consumer, in every body.
pub(crate) fn fuse(program: &mut Program) {
    let recognised = program.recognised().clone();
    let mut fusion = Fusion {
        pure: pure(program),
        recognised,
        producers: HashMap::new(),
        consumers: HashMap::new(),
        fused: HashMap::new(),
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
}

/// A local no fused body may read: what a parameter or field the fused walk
/// has no use for stands for, so that reading one fails validation rather
/// than reading something else.
const UNREAD: Atom = Atom(Local(u32::MAX));

impl Fusion<'_> {
    /// Whether anything in a body calls a producer, which is all that makes
    /// rewriting it worth a copy.
    fn calls_a_producer(&mut self, body: Body) -> bool {
        let mut exprs: Vec<_> = self.program.bindings(body.bindings).to_vec();
        exprs.push(body.tail);
        while let Some(id) = exprs.pop() {
            match self.program.expr(id) {
                Expr::Call(callee, _) if self.producer(callee).is_some() => return true,
                Expr::Match(_, arms) => {
                    for arm in self.program.arms(arms).to_vec() {
                        exprs.extend_from_slice(self.program.bindings(arm.body.bindings));
                        exprs.push(arm.body.tail);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// The list type a function's parameter is, and its constructors: the
    /// empty one, the push, and the position of the push's rest.
    fn sequence(&self, ty: TypeId) -> Option<(super::CtorId, super::CtorId, usize)> {
        match super::type_shape(self.program, ty) {
            TypeShape::Sequence {
                empty,
                push,
                recursive,
                ..
            } => Some((empty, push, recursive)),
            _ => None,
        }
    }

    /// Whether `id` is a producer:
    ///
    /// ```text
    /// p(.. list .. acc ..) = match list
    ///   empty => ...; reverse(acc, <empty>)
    ///   push(x, rest) => ...; next = push(e, acc); p(.. rest .. next ..)
    /// ```
    ///
    /// where `acc` is read nowhere else, and `reverse` is a reversal.
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
        let (list, arms) = self.top_match(body)?;
        let params = self.program.params(id);
        let (empty, push, recursive) = self.sequence(params[list])?;
        let arity = params.len();
        let [nil_arm, push_arm] = self.split_arms(arms, empty, push)?;
        // The empty arm answers the accumulator reversed onto nothing.
        let Expr::Call(reverse, args) = self.program.expr(nil_arm.body.tail) else {
            return None;
        };
        let &[Atom(acc), Atom(onto)] = self.program.atoms(args) else {
            return None;
        };
        let acc = acc.index();
        if acc >= arity || acc == list || !self.reverses(reverse) {
            return None;
        }
        // What it builds is a list too, but not necessarily of what it walks.
        let (built_empty, built_push, built_recursive) = self.sequence(params[acc])?;
        let onto = self.bound(nil_arm.body, arity, onto.index())?;
        if !self.empty_constant(onto, built_empty) {
            return None;
        }
        // The push arm pushes one element onto it, and goes on.
        let push_body = push_arm.body;
        let Expr::Call(again, args) = self.program.expr(push_body.tail) else {
            return None;
        };
        if again != id {
            return None;
        }
        let args = self.program.atoms(args);
        let rest = arity + recursive;
        if args.len() != arity || args[list].0.index() != rest {
            return None;
        }
        let pushed = self.bound(push_body, arity + 2, args[acc].0.index())?;
        let Expr::Con(ctor, fields) = self.program.expr(pushed) else {
            return None;
        };
        let fields = self.program.atoms(fields);
        if ctor != built_push || fields[built_recursive].0.index() != acc {
            return None;
        }
        // Nothing else reads the accumulator, or the list it pushed onto.
        let next = args[acc].0.index();
        let reads = self.reads(push_body, acc) + self.reads(nil_arm.body, acc);
        (reads == 2 && self.reads_after(push_body, arity + 2, next) == 1)
            .then_some(Producer { list, acc })
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
        let (list, arms) = self.top_match(body)?;
        let params = self.program.params(id);
        let (empty, push, recursive) = self.sequence(params[list])?;
        let arity = params.len();
        let [nil_arm, push_arm] = self.split_arms(arms, empty, push)?;
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

    /// Whether `id` reverses its first argument onto its second:
    ///
    /// ```text
    /// r(list, onto) = match list
    ///   empty => onto
    ///   push(x, rest) => r(rest, push(x, onto))
    /// ```
    #[expect(
        clippy::too_many_lines,
        reason = "each condition of the reversal shape is one early return, read in order"
    )]
    fn reverses(&self, id: FnId) -> bool {
        let Some(body) = self.program.function(id).body() else {
            return false;
        };
        let Some((0, arms)) = self.top_match(body) else {
            return false;
        };
        let params = self.program.params(id);
        let Some((empty, push, recursive)) = self.sequence(params[0]) else {
            return false;
        };
        if params.len() != 2 || params[1] != params[0] {
            return false;
        }
        let Some([nil_arm, push_arm]) = self.split_arms(arms, empty, push) else {
            return false;
        };
        if !nil_arm.body.bindings.is_empty()
            || self.program.expr(nil_arm.body.tail) != Expr::Atom(Atom(Local::at(1)))
        {
            return false;
        }
        let element = 2 + (1 - recursive);
        let rest = 2 + recursive;
        let Expr::Call(again, args) = self.program.expr(push_arm.body.tail) else {
            return false;
        };
        let &[Atom(first), Atom(second)] = self.program.atoms(args) else {
            return false;
        };
        if again != id || first.index() != rest {
            return false;
        }
        let Some(pushed) = self.bound(push_arm.body, 4, second.index()) else {
            return false;
        };
        let Expr::Con(ctor, fields) = self.program.expr(pushed) else {
            return false;
        };
        let fields = self.program.atoms(fields);
        ctor == push
            && fields[recursive].0.index() == 1
            && fields[1 - recursive].0.index() == element
    }

    /// A body that is nothing but a match on a parameter: which one, and
    /// its arms.
    fn top_match(&self, body: Body) -> Option<(usize, Range)> {
        if !body.bindings.is_empty() {
            return None;
        }
        // With no bindings before it, what it matches is a parameter.
        let Expr::Match(Atom(on), arms) = self.program.expr(body.tail) else {
            return None;
        };
        Some((on.index(), arms))
    }

    /// A sequence's two arms, the empty one first, whichever order its
    /// declaration gave them.
    fn split_arms(
        &self,
        arms: Range,
        empty: super::CtorId,
        push: super::CtorId,
    ) -> Option<[Arm; 2]> {
        let &[first, second] = self.program.arms(arms) else {
            return None;
        };
        match (first.ctor, second.ctor) {
            (a, b) if a == empty && b == push => Some([first, second]),
            (a, b) if a == push && b == empty => Some([second, first]),
            _ => None,
        }
    }

    /// What wrote local `level`, where it is a binding of `body`, whose
    /// first binding takes level `base`.
    fn bound(&self, body: Body, base: usize, level: usize) -> Option<ExprId> {
        let at = level.checked_sub(base)?;
        self.program.bindings(body.bindings).get(at).copied()
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
        self.reads_in(
            self.program.bindings(body.bindings).to_vec(),
            body.tail,
            level,
        )
    }

    /// How many times the bindings of `body` after its binding at `level`,
    /// and its tail, read that binding. Its first binding takes `base`. An
    /// arm of an earlier binding may bind the same level for itself.
    fn reads_after(&self, body: Body, base: usize, level: usize) -> usize {
        let later = self.program.bindings(body.bindings)[level + 1 - base..].to_vec();
        self.reads_in(later, body.tail, level)
    }

    fn reads_in(&self, mut exprs: Vec<ExprId>, tail: ExprId, level: usize) -> usize {
        let mut count = 0;
        exprs.push(tail);
        while let Some(id) = exprs.pop() {
            count += match self.program.expr(id) {
                Expr::Atom(atom) => usize::from(atom.0.index() == level),
                Expr::Static(_) => 0,
                Expr::Con(_, args) | Expr::Call(_, args) => self
                    .program
                    .atoms(args)
                    .iter()
                    .filter(|atom| atom.0.index() == level)
                    .count(),
                Expr::Match(on, arms) => {
                    for arm in self.program.arms(arms) {
                        exprs.extend_from_slice(self.program.bindings(arm.body.bindings));
                        exprs.push(arm.body.tail);
                    }
                    usize::from(on.0.index() == level)
                }
            };
        }
        count
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
        let (_, p_arms) = self.top_match(p_body).expect("a producer's match");
        let (_, c_arms) = self.top_match(c_body).expect("a consumer's match");
        let walked = self.program.params(producer)[list];
        let (empty, push, recursive) = self.sequence(walked).expect("a list");
        let taken = self.program.params(consumer)[pair.taken];
        let (c_empty, c_push, _) = self.sequence(taken).expect("a list");
        let [_, p_step] = self.split_arms(p_arms, empty, push).expect("two arms");
        let [c_nil, c_step] = self.split_arms(c_arms, c_empty, c_push).expect("two arms");
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
    #[expect(
        clippy::too_many_lines,
        reason = "the producer step, the element, and the consumer step are copied into one scope in order"
    )]
    fn step(&mut self, pair: &Pair, (p_step, walked): (Arm, usize), c_step: Arm) -> Body {
        let arity = pair.arity;
        let (_, _, recursive) = self
            .sequence(self.program.params(pair.consumer)[pair.taken])
            .expect("a list");
        let mut scope = Scope::at(arity + 2);
        let mut locals = pair.p_locals.clone();
        locals.extend([Atom(Local::at(arity)), Atom(Local::at(arity + 1))]);
        // The rest of what the producer walks, which is the fused walk's.
        let rest = Atom(Local::at(arity + walked));
        let Expr::Call(_, again) = self.program.expr(p_step.body.tail) else {
            unreachable!("a producer's step calls itself")
        };
        let again = self.program.atoms(again).to_vec();
        let p_arity = pair.p_locals.len();
        let pushed = again[pair.acc].0.index() - (p_arity + 2);
        let bindings = self.program.bindings(p_step.body.bindings).to_vec();
        for (at, &binding) in bindings.iter().enumerate() {
            let value = if at == pushed {
                UNREAD
            } else {
                copy::expr(self.program, binding, &locals, &mut scope, None)
            };
            locals.push(value);
        }
        let Expr::Con(_, fields) = self.program.expr(bindings[pushed]) else {
            unreachable!("a producer pushes")
        };
        let element = locals[self.program.atoms(fields)[1 - recursive].0.index()];
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
        let redirect = Redirect {
            from: pair.consumer,
            at: pair.taken,
            rest,
            to: pair.id,
            leading: going_on,
        };
        let answer = copy::into(
            self.program,
            c_step.body,
            consumed,
            &mut scope,
            Some(&redirect),
        );
        copy::close(self.program, scope, answer)
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
        let Some(Producer { acc, .. }) = self.producer(call.callee) else {
            return false;
        };
        let Some(onto) = self.bound(body, base, call.written[acc].0.index()) else {
            return false;
        };
        let Some((empty, _, _)) = self.sequence(self.program.params(call.callee)[acc]) else {
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

/// Whether each function reaches no bodyless call, by function.
fn pure(program: &Program) -> Vec<bool> {
    let count = program.functions().len();
    let mut pure: Vec<bool> = program
        .functions()
        .iter()
        .map(|function| function.body().is_some())
        .collect();
    let callees: Vec<Vec<FnId>> = program
        .functions()
        .iter()
        .map(|function| {
            function
                .body()
                .map(|body| called(program, body))
                .unwrap_or_default()
        })
        .collect();
    loop {
        let mut changed = false;
        for at in 0..count {
            if pure[at] && callees[at].iter().any(|callee| !pure[callee.index()]) {
                pure[at] = false;
                changed = true;
            }
        }
        if !changed {
            return pure;
        }
    }
}

/// Every function a body calls.
fn called(program: &Program, body: Body) -> Vec<FnId> {
    let mut found = Vec::new();
    let mut exprs: Vec<_> = program.bindings(body.bindings).to_vec();
    exprs.push(body.tail);
    while let Some(id) = exprs.pop() {
        match program.expr(id) {
            Expr::Call(callee, _) => found.push(callee),
            Expr::Match(_, arms) => {
                for arm in program.arms(arms) {
                    exprs.extend_from_slice(program.bindings(arm.body.bindings));
                    exprs.push(arm.body.tail);
                }
            }
            _ => {}
        }
    }
    found
}
