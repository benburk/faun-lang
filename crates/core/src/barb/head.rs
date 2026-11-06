//! A list read only for its first element, built only as far as that.
//!
//! A definition building a list by joining what its own calls answer --
//! every solution of a search, the first branch's before the second's --
//! makes every element even where its caller asks only for the first:
//!
//! ```text
//! s(..) = ...; a = s(..); b = s(..); join(a, b)
//! r = s(..); match r { empty => .., push(x, _) => .. x .. }
//! ```
//!
//! Where a call's answer is read once, by a match whose step never reads
//! the rest, only its first element matters, and the call goes to a copy of
//! the definition answering a list with that same first element and as
//! little else as it can. In the copy, a join tries the first list before
//! anything the second needs is worked out:
//!
//! ```text
//! s.head(..) = ...; a = s.head(..); match a { empty => (b = s.head(..); b), push(_, _) => a }
//! ```
//!
//! so a search asked for its first solution stops at the first it finds.
//! In the copy, a call of the definition itself goes to the copy, and an
//! element pushed onto a rest is pushed onto nothing, the rest unread.
//!
//! Nothing is recognized by name: a join is the sequence operation putting
//! one list before another, and the reading match is a shape. Only a
//! definition reaching no bodyless call is copied, since what the copy
//! skips is work nothing may observe ([`Program::pure`]), and only one
//! whose answer some join makes in tail position, which is where there is
//! work to skip.
//!
//! [`Program::pure`]: super::calls::pure

use std::collections::{HashMap, HashSet};

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::walk;
use super::{Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, SequenceOperation};

/// Give each call read only for its first element a copy of what it calls
/// that builds no more than that.
pub(crate) fn heads(program: &mut Program) {
    let recognised = program.recognised().clone();
    let pure = super::calls::pure(program, &recognised);
    let count = program.functions().len();
    let (sites, producers) = found(program, &recognised, &pure);
    if sites.is_empty() {
        return;
    }
    let mut wanted: Vec<FnId> = sites.values().copied().collect();
    wanted.sort_by_key(|id| id.index());
    wanted.dedup();
    let copies = declared(program, &wanted);
    let rewrite = Rewrite {
        recognised: &recognised,
        sites: &sites,
        copies: &copies,
    };
    let mut bodies: Vec<_> = wanted
        .iter()
        .map(|&producer| {
            let head = Head {
                producer,
                copy: copies[&producer],
                shape: producers[&producer].expect("a producer is wanted only where it is one"),
            };
            (head.copy, rewrite.copy_of(program, &head))
        })
        .collect();
    bodies.extend(redirected(program, &rewrite, count));
    program.replace_bodies(bodies);
}

/// Each of the first `count` definitions holding a site, copied with each
/// site calling its copy.
fn redirected(program: &mut Program, rewrite: &Rewrite<'_>, count: usize) -> Vec<(FnId, Body)> {
    let mut bodies = Vec::new();
    for id in (0..count).map(FnId::at) {
        let Some(body) = program.function(id).body() else {
            continue;
        };
        if walk::within(program, body).any(|expr| rewrite.sites.contains_key(&expr)) {
            let arity = program.params(id).len();
            let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
            let mut redirect = rewrite.redirect();
            let copied = copy::body(program, body, locals, arity, Some(&mut redirect));
            bodies.push((id, copied));
        }
    }
    bodies
}

/// A copy of each of `wanted`, declared, named with `.head` after it.
fn declared(program: &mut Program, wanted: &[FnId]) -> HashMap<FnId, FnId> {
    wanted
        .iter()
        .map(|&producer| {
            let name = format!("{}.head", program.name(program.function(producer).name));
            let params = program.params(producer).to_vec();
            let result = program.function(producer).result;
            (producer, program.declare(&name, &params, result))
        })
        .collect()
}

/// Each call read only for its first element, by the expression it is, and
/// what it calls; and each definition asked about, with its shape where it
/// is a producer.
fn found(
    program: &Program,
    recognised: &Recognised,
    pure: &[bool],
) -> (HashMap<ExprId, FnId>, HashMap<FnId, Option<Shape>>) {
    let mut finder = Finder {
        program,
        recognised,
        pure,
        producers: HashMap::new(),
        sites: HashMap::new(),
    };
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        if recognised.answered(id) {
            continue;
        }
        if let Some(body) = program.function(id).body() {
            finder.find(body, program.params(id).len());
        }
    }
    (finder.sites, finder.producers)
}

/// What a list-building definition builds: its empty list, its step, and
/// which of the step's fields is the rest.
#[derive(Clone, Copy)]
struct Shape {
    empty: CtorId,
    push: CtorId,
    recursive: usize,
}

/// A definition being copied, and the copy it is becoming.
struct Head {
    producer: FnId,
    copy: FnId,
    shape: Shape,
}

/// Finding the calls read only for their first element.
struct Finder<'a> {
    program: &'a Program,
    recognised: &'a Recognised,
    pure: &'a [bool],
    /// Each definition asked about, and its shape where it is a producer.
    producers: HashMap<FnId, Option<Shape>>,
    /// Each call to copy, by the expression it is, and what it calls.
    sites: HashMap<ExprId, FnId>,
}

impl Finder<'_> {
    /// Find the sites in `body`, whose first binding takes `base`, and in
    /// every arm it holds.
    fn find(&mut self, body: Body, base: usize) {
        let mut exprs = self.program.bindings(body.bindings).to_vec();
        exprs.push(body.tail);
        for (at, &id) in exprs.iter().enumerate() {
            let level = base + at;
            match self.program.expr(id) {
                Expr::Call(callee, _) if at + 1 < exprs.len() => {
                    if let Some(shape) = self.producer(callee)
                        && self.read_for_head(&exprs[at + 1..], level, shape)
                    {
                        self.sites.insert(id, callee);
                    }
                }
                Expr::Match(_, arms) => {
                    for arm in self.program.arms(arms) {
                        let fields = self.program.fields(arm.ctor).len();
                        self.find(arm.body, level + fields);
                    }
                }
                _ => {}
            }
        }
    }

    /// Whether `id` builds a list that a join answers somewhere in tail
    /// position, and may be copied: it reaches no bodyless call and is not
    /// answered as an operation it was recognized as.
    fn producer(&mut self, id: FnId) -> Option<Shape> {
        if let Some(&known) = self.producers.get(&id) {
            return known;
        }
        let found = self.find_producer(id);
        self.producers.insert(id, found);
        found
    }

    fn find_producer(&self, id: FnId) -> Option<Shape> {
        let takes_part =
            self.pure.get(id.index()).copied().unwrap_or(false) && !self.recognised.answered(id);
        if !takes_part {
            return None;
        }
        let body = self.program.function(id).body()?;
        let (empty, push, recursive) =
            super::sequence::sequence(self.program, self.program.function(id).result)?;
        self.joins_in_tail(body).then_some(Shape {
            empty,
            push,
            recursive,
        })
    }

    /// Whether a join answers `body`, or an arm of a match answering it.
    fn joins_in_tail(&self, body: Body) -> bool {
        match self.program.expr(body.tail) {
            Expr::Call(callee, _) => joins(self.recognised, callee),
            Expr::Match(_, arms) => self
                .program
                .arms(arms)
                .iter()
                .any(|arm| self.joins_in_tail(arm.body)),
            Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => false,
        }
    }

    /// Whether the local at `level` is read once by `later`, the
    /// expressions of its body after it, and that by a match whose step
    /// never reads the rest.
    fn read_for_head(&self, later: &[ExprId], level: usize, shape: Shape) -> bool {
        let reads = walk::reads(
            self.program,
            walk::nested(self.program, later.iter().copied()),
            level,
        );
        if reads != 1 {
            return false;
        }
        later.iter().enumerate().any(|(at, &id)| {
            let Expr::Match(Atom(on), arms) = self.program.expr(id) else {
                return false;
            };
            let Some([_, step]) = walk::split_arms(self.program, arms, shape.empty, shape.push)
            else {
                return false;
            };
            // The match binds its fields from its own level, the next after
            // `level` that it is the `at`th of.
            let rest = level + 1 + at + shape.recursive;
            on.index() == level
                && walk::reads(self.program, walk::within(self.program, step.body), rest) == 0
        })
    }
}

/// Copying bodies, each site calling its definition's copy.
struct Rewrite<'a> {
    recognised: &'a Recognised,
    sites: &'a HashMap<ExprId, FnId>,
    copies: &'a HashMap<FnId, FnId>,
}

/// What a local a copy has no use for stands for, so that reading one fails
/// validation rather than reading something else.
const UNREAD: Atom = Atom(Local(u32::MAX));

impl Rewrite<'_> {
    /// An edit sending each site to its definition's copy.
    fn redirect(&self) -> impl FnMut(&mut Program, &mut Scope, ExprId, Expr) -> Expr + '_ {
        |_, _, id, expr| match (self.sites.get(&id), expr) {
            (Some(producer), Expr::Call(_, args)) => Expr::Call(self.copies[producer], args),
            (_, other) => other,
        }
    }

    /// The body of the copy `head` is becoming.
    fn copy_of(&self, program: &mut Program, head: &Head) -> Body {
        let body = program
            .function(head.producer)
            .body()
            .expect("a producer has a body");
        let arity = program.params(head.producer).len();
        let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
        let mut scope = Scope::at(arity);
        let answer = self.headed(program, head, body, locals, &mut scope);
        copy::close(program, scope, answer)
    }

    /// `body` copied into `scope` as the copy `head` answers it, every
    /// local it reads from before it read through `locals`.
    fn headed(
        &self,
        program: &mut Program,
        head: &Head,
        body: Body,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
    ) -> Atom {
        let base = locals.len();
        let bindings = program.bindings(body.bindings).to_vec();
        if let Expr::Call(callee, args) = program.expr(body.tail)
            && joins(self.recognised, callee)
            && let &[first, then] = program.atoms(args)
        {
            return self.joined(
                program,
                head,
                (&bindings, body.tail),
                (locals, base),
                scope,
                (first, then),
            );
        }
        for &binding in &bindings {
            let value = self.copied(program, binding, &locals, scope);
            locals.push(value);
        }
        match program.expr(body.tail) {
            Expr::Match(on, arms) => {
                let mut rebuilt = Vec::new();
                for arm in program.arms(arms).to_vec() {
                    let fields = program.fields(arm.ctor).len();
                    let mut inner = locals.clone();
                    inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
                    let mut arm_scope = Scope::at(scope.level + fields);
                    let answer = self.headed(program, head, arm.body, inner, &mut arm_scope);
                    rebuilt.push(Arm {
                        ctor: arm.ctor,
                        body: copy::close(program, arm_scope, answer),
                    });
                }
                let arms = program.terms.hold_arms(&rebuilt);
                copy::push(program, scope, Expr::Match(locals[on.0.index()], arms))
            }
            _ => self.headed_expr(program, head, body.tail, &locals, scope),
        }
    }

    /// A body answering `join(first, then)`: `first` as the copy answers
    /// it, and only where that is empty, every binding `first` does not
    /// need, then `then`.
    fn joined(
        &self,
        program: &mut Program,
        head: &Head,
        (bindings, tail): (&[ExprId], ExprId),
        (mut locals, base): (Vec<Atom>, usize),
        scope: &mut Scope,
        (first, then): (Atom, Atom),
    ) -> Atom {
        // The tail reads nothing but the two lists, so a binding the first
        // does not need is the second's, or read by nothing.
        let firsts = needs(program, bindings, base, first.0.index());
        let first_once = read_once(program, (bindings, tail), base, first.0.index());
        let then_once = read_once(program, (bindings, tail), base, then.0.index());
        for (at, &binding) in bindings.iter().enumerate() {
            let level = base + at;
            let value = if !firsts.contains(&level) {
                UNREAD
            } else if level == first.0.index() && first_once {
                self.headed_expr(program, head, binding, &locals, scope)
            } else {
                self.copied(program, binding, &locals, scope)
            };
            locals.push(value);
        }
        let tried = locals[first.0.index()];
        let moved = |level: usize| !firsts.contains(&level);
        let otherwise = self.otherwise(
            program,
            head,
            (bindings, base, &moved),
            locals,
            (then, then_once),
            scope.level,
        );
        // Where it is not, the first list, which has that first element.
        let fields = program.fields(head.shape.push).len();
        let found = copy::close(program, Scope::at(scope.level + fields), tried);
        let arms = program.terms.hold_arms(&[
            Arm {
                ctor: head.shape.empty,
                body: otherwise,
            },
            Arm {
                ctor: head.shape.push,
                body: found,
            },
        ]);
        copy::push(program, scope, Expr::Match(tried, arms))
    }

    /// The body where the first list is empty: each binding `moved` says
    /// only the second list needs, worked out now, then the second list.
    /// Its first binding takes `level`.
    fn otherwise(
        &self,
        program: &mut Program,
        head: &Head,
        (bindings, base, moved): (&[ExprId], usize, &dyn Fn(usize) -> bool),
        mut locals: Vec<Atom>,
        (then, then_once): (Atom, bool),
        level: usize,
    ) -> Body {
        let mut scope = Scope::at(level);
        for (at, &binding) in bindings.iter().enumerate() {
            let level = base + at;
            if !moved(level) {
                continue;
            }
            // Only what is bound before it: an arm it holds binds its
            // fields after the locals it is handed.
            let before = &locals[..level];
            locals[level] = if level == then.0.index() && then_once {
                self.headed_expr(program, head, binding, before, &mut scope)
            } else {
                self.copied(program, binding, before, &mut scope)
            };
        }
        copy::close(program, scope, locals[then.0.index()])
    }

    /// An expression whose answer is read only for its first element, as
    /// the copy answers it: a call of the definition as a call of the copy,
    /// and an element pushed onto a rest as pushed onto nothing.
    fn headed_expr(
        &self,
        program: &mut Program,
        head: &Head,
        id: ExprId,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Atom {
        match program.expr(id) {
            Expr::Call(callee, args) if callee == head.producer => {
                #[expect(
                    clippy::needless_collect,
                    reason = "the atoms are read from the program the new ones are held in"
                )]
                let args: Vec<Atom> = program
                    .atoms(args)
                    .iter()
                    .map(|atom| locals[atom.0.index()])
                    .collect();
                let args = program.terms.hold_atoms(args.into_iter());
                copy::push(program, scope, Expr::Call(head.copy, args))
            }
            Expr::Con(ctor, fields) if ctor == head.shape.push => {
                let none = program.terms.hold_atoms(std::iter::empty());
                let nothing = copy::push(program, scope, Expr::Con(head.shape.empty, none));
                #[expect(
                    clippy::needless_collect,
                    reason = "the atoms are read from the program the new ones are held in"
                )]
                let fields: Vec<Atom> = program
                    .atoms(fields)
                    .iter()
                    .enumerate()
                    .map(|(at, atom)| {
                        if at == head.shape.recursive {
                            nothing
                        } else {
                            locals[atom.0.index()]
                        }
                    })
                    .collect();
                let fields = program.terms.hold_atoms(fields.into_iter());
                copy::push(program, scope, Expr::Con(ctor, fields))
            }
            _ => self.copied(program, id, locals, scope),
        }
    }

    /// An expression copied as it is, but for the sites in it.
    fn copied(
        &self,
        program: &mut Program,
        id: ExprId,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Atom {
        let mut redirect = self.redirect();
        copy::expr(program, id, locals, scope, Some(&mut redirect))
    }
}

/// Whether the local at `level` is one of `bindings`, the first of which
/// takes `base`, read once by those after it and by `tail`.
fn read_once(
    program: &Program,
    (bindings, tail): (&[ExprId], ExprId),
    base: usize,
    level: usize,
) -> bool {
    let Some(at) = level.checked_sub(base).filter(|&at| at < bindings.len()) else {
        return false;
    };
    let mut after = bindings[at + 1..].to_vec();
    after.push(tail);
    walk::reads(program, walk::nested(program, after), level) == 1
}

/// Whether `id` is recognized as putting one list before another.
fn joins(recognised: &Recognised, id: FnId) -> bool {
    recognised.sequences.get(id.index()) == Some(&Some(SequenceOperation::Prepend))
}

/// The levels of `bindings` that working out `level` needs: itself where it
/// is one of them, and whatever it reads of them, however indirectly. The
/// first of `bindings` takes `base`; a binding reads only those before it,
/// so a level its arms bind for themselves is never one of them.
fn needs(program: &Program, bindings: &[ExprId], base: usize, level: usize) -> HashSet<usize> {
    let mut needed = HashSet::new();
    let mut waiting = vec![level];
    while let Some(level) = waiting.pop() {
        let Some(&binding) = level.checked_sub(base).and_then(|at| bindings.get(at)) else {
            continue;
        };
        if !needed.insert(level) {
            continue;
        }
        for id in walk::nested(program, [binding]) {
            waiting.extend(
                walk::operands(program, id)
                    .map(|atom| atom.0.index())
                    .filter(|&read| read >= base && read < level),
            );
        }
    }
    needed
}
