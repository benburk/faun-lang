//! Building a list front to back.
//!
//! A walk answering `[f(x), *walk(rest)]` builds on the way out: each call
//! waits for the rest before putting its element in front, so it goes as
//! deep as its list is long. Written with an accumulator it would be a loop,
//! but one building backwards that must turn round at the end. A sequence is
//! a buffer, and a buffer grows at its end where nothing else holds it, so
//! the walk is written again carrying what it has built so far, each element
//! put after it:
//!
//! ```text
//! walk([], ..) = base                   walk'([], .., built) = built ++ base
//! walk([x, *rest], ..) =                walk'([x, *rest], .., built) =
//!   [f(x), *walk(rest, ..)]               walk'(rest, .., built ++ [f(x)])
//! ```
//!
//! and `walk` calls `walk'` with nothing built. Every call `walk'` makes of
//! itself is then in tail position, which is a loop.
//!
//! The list may be a field of what the walk answers, the rest of a pair it
//! took apart and put back together around one more element: `map_accum`
//! answers its state beside its list. A call answering the walk's answer
//! outright is a call of `walk'` handing on what was built, as a filter
//! skipping an element does; a clause calling nothing answers what was
//! built followed by what it answers. Any other call of itself leaves the
//! walk as it was.
//!
//! Nothing is recognized by name: the clauses' shapes are what is read, and
//! the definitions putting one element or one list after another are
//! written here, as recognized sequence operations, where none is found.

use std::collections::HashMap;

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::{Arm, Atom, Body, CtorId, Expr, FnId, Local, Program, SequenceOperation, TypeId};
use super::{TypeShape, type_shape};

/// Rewrite every walk building a list on the way out to build it front to
/// back.
pub(crate) fn forward(program: &mut Program) {
    let recognised = program.recognised().clone();
    let count = program.functions().len();
    let mut writer = Writer {
        recognised,
        helpers: HashMap::new(),
        program,
    };
    let mut bodies = Vec::new();
    for at in 0..count {
        let id = FnId::at(at);
        if writer.recognised.answered(id) {
            continue;
        }
        let Some(walk) = walk(writer.program, id) else {
            continue;
        };
        bodies.push((id, writer.rewrite(id, &walk)));
    }
    writer.program.replace_bodies(bodies);
}

/// Where the list a walk builds is in what it answers.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Place {
    /// It is the answer.
    Whole,
    /// It is this field of the answer's one constructor.
    Field { ctor: CtorId, field: usize },
}

/// A walk this rewrites: the sequence it builds, its constructors, and
/// where it is in the answer.
struct Walk {
    list: TypeId,
    empty: CtorId,
    push: CtorId,
    recursive: usize,
    place: Place,
}

/// What one way through a body answers.
enum Tail {
    /// A match, each arm read on its own.
    Branch,
    /// Its own answer for other arguments: a call of itself in tail position.
    Pass,
    /// Its own answer for other arguments with one more element in front,
    /// `element`, where the list is.
    Step { element: Atom, place: Place },
    /// Something calling nothing of itself.
    Base,
}

/// Whether `id` is a walk this rewrites, and if so what it builds.
fn walk(program: &Program, id: FnId) -> Option<Walk> {
    let body = program.function(id).body()?;
    let result = program.function(id).result;
    let base = program.params(id).len();
    let mut place = None;
    let mut steps = 0_usize;
    if !read(program, id, body, base, &mut place, &mut steps) || steps == 0 {
        return None;
    }
    let place = place?;
    if let Place::Field { ctor, .. } = place
        && (program.ctor(ctor).owner != result || program.ctors(result).len() != 1)
    {
        return None;
    }
    let list = match place {
        Place::Whole => result,
        Place::Field { ctor, field } => program.types_of(program.ctor(ctor).fields)[field],
    };
    let TypeShape::Sequence {
        empty,
        push,
        recursive,
        ..
    } = type_shape(program, list)
    else {
        return None;
    };
    (program.fields(push).len() == 2).then_some(Walk {
        list,
        empty,
        push,
        recursive,
        place,
    })
}

/// Whether every way through `body`, whose first binding takes `base`, is
/// one this rewrites, all building the list at one place; how many step.
fn read(
    program: &Program,
    id: FnId,
    body: Body,
    base: usize,
    place: &mut Option<Place>,
    steps: &mut usize,
) -> bool {
    let Some(tail) = tail(program, id, body, base) else {
        return false;
    };
    match tail {
        Tail::Branch => {
            let Expr::Match(_, arms) = program.expr(body.tail) else {
                unreachable!("a branch is a match");
            };
            let level = base + program.bindings(body.bindings).len();
            program.arms(arms).iter().all(|arm| {
                let fields = program.fields(arm.ctor).len();
                read(program, id, arm.body, level + fields, place, steps)
            })
        }
        Tail::Pass | Tail::Base => true,
        Tail::Step { place: found, .. } => {
            *steps += 1;
            place.get_or_insert(found) == &found
        }
    }
}

/// What way through it `body` is, where it is one this rewrites.
fn tail(program: &Program, id: FnId, body: Body, base: usize) -> Option<Tail> {
    let bindings = program.bindings(body.bindings);
    let before = bindings.split_last();
    let calls_before = |upto: &[super::ExprId]| {
        upto.iter()
            .any(|&binding| calls_itself(program, id, binding))
    };
    if !calls_itself(program, id, body.tail) && !calls_before(bindings) {
        return Some(Tail::Base);
    }
    if let Some((&last, earlier)) = before
        && matches!(program.expr(last), Expr::Call(callee, _) if callee == id)
        && !calls_before(earlier)
        && let Some((element, place)) = stepped(program, body, base)
    {
        return Some(Tail::Step { element, place });
    }
    if calls_before(bindings) {
        return None;
    }
    match program.expr(body.tail) {
        Expr::Call(callee, _) if callee == id => Some(Tail::Pass),
        Expr::Match(..) => Some(Tail::Branch),
        _ => None,
    }
}

/// The element a body whose last binding calls itself puts in front of
/// what that call answers, as its tail, and where the list is: the call's
/// answer the rest of a push, or a field of it taken apart and put back
/// together as one.
fn stepped(program: &Program, body: Body, base: usize) -> Option<(Atom, Place)> {
    let count = program.bindings(body.bindings).len();
    let call = base + count - 1;
    let (element, place) = match program.expr(body.tail) {
        // `[x, *walk(rest)]`
        Expr::Con(ctor, fields) => {
            let element = pushed(program, ctor, program.atoms(fields), call)?;
            (element, Place::Whole)
        }
        // `(a, list) = walk(rest); (a, [x, *list])`
        Expr::Match(on, arms) if on.0.index() == call => {
            let &[arm] = program.arms(arms) else {
                return None;
            };
            let (element, field) = rebuilt(program, arm, base + count)?;
            let place = Place::Field {
                ctor: arm.ctor,
                field,
            };
            (element, place)
        }
        _ => return None,
    };
    // The element is made before the call, never out of what it answers.
    (element.0.index() < call).then_some((element, place))
}

/// Where an arm taking apart what a call answered, its fields from level
/// `first`, puts it back together with one field pushed onto: the element
/// pushed, and which field.
fn rebuilt(program: &Program, arm: Arm, first: usize) -> Option<(Atom, usize)> {
    let taken = program.fields(arm.ctor).len();
    let &[pushing] = program.bindings(arm.body.bindings) else {
        return None;
    };
    let Expr::Con(push, pushed_fields) = program.expr(pushing) else {
        return None;
    };
    let Expr::Con(again, fields) = program.expr(arm.body.tail) else {
        return None;
    };
    let fields = program.atoms(fields);
    if again != arm.ctor || fields.len() != taken {
        return None;
    }
    // Every field is the one taken out there, but one: the push, once.
    let pushed_at = first + taken;
    let mut field = None;
    for (at, atom) in fields.iter().enumerate() {
        if atom.0.index() == pushed_at && field.is_none() {
            field = Some(at);
        } else if atom.0.index() != first + at {
            return None;
        }
    }
    let field = field?;
    let element = pushed(program, push, program.atoms(pushed_fields), first + field)?;
    Some((element, field))
}

/// The element of a push whose rest is local `rest`, where `ctor` is a
/// sequence's push and the element is not `rest` too.
fn pushed(program: &Program, ctor: CtorId, fields: &[Atom], rest: usize) -> Option<Atom> {
    let TypeShape::Sequence {
        push, recursive, ..
    } = type_shape(program, program.ctor(ctor).owner)
    else {
        return None;
    };
    let &[a, b] = fields else {
        return None;
    };
    let (element, tail) = if recursive == 0 { (b, a) } else { (a, b) };
    (ctor == push && tail.0.index() == rest && element.0.index() != rest).then_some(element)
}

/// Whether `expr` calls `id`, anywhere in it.
fn calls_itself(program: &Program, id: FnId, expr: super::ExprId) -> bool {
    match program.expr(expr) {
        Expr::Call(callee, _) => callee == id,
        Expr::Match(_, arms) => program.arms(arms).iter().any(|arm| {
            program
                .bindings(arm.body.bindings)
                .iter()
                .chain([&arm.body.tail])
                .any(|&inner| calls_itself(program, id, inner))
        }),
        Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => false,
    }
}

/// The sequence operations a rewritten walk calls, for one sequence type.
#[derive(Clone, Copy)]
struct Helpers {
    append: FnId,
    prepend: FnId,
}

struct Writer<'a> {
    program: &'a mut Program,
    recognised: Recognised,
    helpers: HashMap<TypeId, Helpers>,
}

/// One walk being written again: itself, what it now calls, and where the
/// list built so far is.
struct Rewriting<'w> {
    walk: &'w Walk,
    id: FnId,
    forward: FnId,
    helpers: Helpers,
    built: Atom,
}

impl Writer<'_> {
    /// Write `walk'` and answer `walk`'s body calling it with nothing built.
    fn rewrite(&mut self, id: FnId, walk: &Walk) -> Body {
        let helpers = self.helpers(walk);
        let params = self.program.params(id).to_vec();
        let result = self.program.function(id).result;
        let name = format!(
            "{}.forward",
            self.program.name(self.program.function(id).name)
        );
        let mut taking = params.clone();
        taking.push(walk.list);
        let forward = self.program.declare(&name, &taking, result);
        let arity = params.len();
        let rewriting = Rewriting {
            walk,
            id,
            forward,
            helpers,
            built: Atom(Local::at(arity)),
        };
        let body = self.program.function(id).body().expect("a walk has a body");
        let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
        let mut scope = Scope::at(arity + 1);
        let answer = self.write(&rewriting, body, locals, &mut scope, arity);
        let written = copy::close(self.program, scope, answer);
        self.program.replace_bodies(vec![(forward, written)]);

        let mut scope = Scope::at(arity);
        let none = self.program.terms.hold_atoms(std::iter::empty());
        let nothing = copy::push(self.program, &mut scope, Expr::Con(walk.empty, none));
        let args = (0..arity)
            .map(|at| Atom(Local::at(at)))
            .chain([nothing])
            .collect();
        let answer = self.call(&mut scope, forward, args);
        copy::close(self.program, scope, answer)
    }

    /// Write one way through `body`, whose first binding took `base`, into
    /// `scope`, each local read through `locals`: what it answers.
    fn write(
        &mut self,
        rewriting: &Rewriting<'_>,
        body: Body,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
        base: usize,
    ) -> Atom {
        let tail = tail(self.program, rewriting.id, body, base).expect("a walk's ways were read");
        let bindings = self.program.bindings(body.bindings).to_vec();
        let kept = match tail {
            Tail::Step { .. } => &bindings[..bindings.len() - 1],
            Tail::Branch | Tail::Pass | Tail::Base => &bindings[..],
        };
        for &binding in kept {
            let value = copy::expr(self.program, binding, &locals, scope, None);
            locals.push(value);
        }
        match tail {
            Tail::Branch => {
                let level = base + bindings.len();
                self.branch(rewriting, body.tail, (locals, level), scope)
            }
            // `walk(..)` is `walk'(.., built)`.
            Tail::Pass => self.again(rewriting, body.tail, &locals, rewriting.built, scope),
            // `[x, *walk(..)]` is `walk'(.., built ++ [x])`.
            Tail::Step { element, .. } => {
                let &call = bindings.last().expect("a step calls itself last");
                let element = locals[element.0.index()];
                let append = rewriting.helpers.append;
                let built = self.call(scope, append, vec![rewriting.built, element]);
                self.again(rewriting, call, &locals, built, scope)
            }
            Tail::Base => {
                let answer = copy::expr(self.program, body.tail, &locals, scope, None);
                self.finish(rewriting, answer, scope)
            }
        }
    }

    /// A match, each arm written as a way through of its own. Its arms'
    /// fields take the next levels after `level` in the source.
    fn branch(
        &mut self,
        rewriting: &Rewriting<'_>,
        expr: super::ExprId,
        (locals, level): (Vec<Atom>, usize),
        scope: &mut Scope,
    ) -> Atom {
        let Expr::Match(on, arms) = self.program.expr(expr) else {
            unreachable!("a branch is a match");
        };
        let mut rebuilt = Vec::new();
        for arm in self.program.arms(arms).to_vec() {
            let fields = self.program.fields(arm.ctor).len();
            let mut inner = locals.clone();
            inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
            let mut arm_scope = Scope::at(scope.level + fields);
            let answer = self.write(rewriting, arm.body, inner, &mut arm_scope, level + fields);
            rebuilt.push(Arm {
                ctor: arm.ctor,
                body: copy::close(self.program, arm_scope, answer),
            });
        }
        let arms = self.program.terms.hold_arms(&rebuilt);
        copy::push(self.program, scope, Expr::Match(locals[on.0.index()], arms))
    }

    /// The call of itself `call` makes, as a call of `walk'` handing on
    /// `built`.
    fn again(
        &mut self,
        rewriting: &Rewriting<'_>,
        call: super::ExprId,
        locals: &[Atom],
        built: Atom,
        scope: &mut Scope,
    ) -> Atom {
        let Expr::Call(_, args) = self.program.expr(call) else {
            unreachable!("a walk goes on by calling itself");
        };
        let args = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| locals[atom.0.index()])
            .chain([built])
            .collect();
        self.call(scope, rewriting.forward, args)
    }

    /// What a clause calling nothing of itself answers, with what was built
    /// before its list.
    fn finish(&mut self, rewriting: &Rewriting<'_>, answer: Atom, scope: &mut Scope) -> Atom {
        let prepend = rewriting.helpers.prepend;
        let built = rewriting.built;
        match rewriting.walk.place {
            Place::Whole => self.call(scope, prepend, vec![built, answer]),
            Place::Field { ctor, field } => {
                let fields = self.program.fields(ctor).len();
                let taken: Vec<Atom> = (0..fields)
                    .map(|at| Atom(Local::at(scope.level + at)))
                    .collect();
                let mut inner = Scope::at(scope.level + fields);
                let joined = self.call(&mut inner, prepend, vec![built, taken[field]]);
                let mut rebuilt = taken;
                rebuilt[field] = joined;
                let rebuilt = self.program.terms.hold_atoms(rebuilt.into_iter());
                let again = copy::push(self.program, &mut inner, Expr::Con(ctor, rebuilt));
                let body = copy::close(self.program, inner, again);
                let arms = self.program.terms.hold_arms(&[Arm { ctor, body }]);
                copy::push(self.program, scope, Expr::Match(answer, arms))
            }
        }
    }

    fn call(&mut self, scope: &mut Scope, callee: FnId, args: Vec<Atom>) -> Atom {
        let args = self.program.terms.hold_atoms(args.into_iter());
        copy::push(self.program, scope, Expr::Call(callee, args))
    }

    /// The definitions putting one element, and one list, after a list of
    /// the walk's type: found among those recognized, or written.
    fn helpers(&mut self, walk: &Walk) -> Helpers {
        if let Some(&helpers) = self.helpers.get(&walk.list) {
            return helpers;
        }
        let list = walk.list;
        let found = |operation, program: &Program, recognised: &Recognised, takes: &[TypeId]| {
            (0..recognised.sequences.len()).map(FnId::at).find(|&id| {
                recognised.sequences[id.index()] == Some(operation) && program.params(id) == takes
            })
        };
        let element = self.program.types_of(self.program.ctor(walk.push).fields)
            [usize::from(walk.recursive == 0)];
        let prepend = found(
            SequenceOperation::Prepend,
            self.program,
            &self.recognised,
            &[list, list],
        )
        .unwrap_or_else(|| self.write_prepend(walk));
        let append = found(
            SequenceOperation::Append,
            self.program,
            &self.recognised,
            &[list, element],
        )
        .unwrap_or_else(|| self.write_append(walk, element, prepend));
        let helpers = Helpers { append, prepend };
        self.helpers.insert(list, helpers);
        helpers
    }

    /// `p(list, onto) = r(r(list, empty), onto)`, and `r` beside it.
    fn write_prepend(&mut self, walk: &Walk) -> FnId {
        let (list, empty, push, recursive) = (walk.list, walk.empty, walk.push, walk.recursive);
        let reverse = self.program.declare("reverse_onto", &[list, list], list);
        self.program.define(reverse, |b, args| {
            let (from, onto) = (args[0], args[1]);
            b.match_(from, list, |b, ctor, fields| {
                if ctor == empty {
                    return onto;
                }
                let (element, rest) = if recursive == 0 {
                    (fields[1], fields[0])
                } else {
                    (fields[0], fields[1])
                };
                let pushed = if recursive == 0 {
                    b.con(push, &[onto, element])
                } else {
                    b.con(push, &[element, onto])
                };
                b.call(reverse, &[rest, pushed])
            })
        });
        let prepend = self.program.declare("prepend", &[list, list], list);
        self.program.define(prepend, |b, args| {
            let nothing = b.con(empty, &[]);
            let reversed = b.call(reverse, &[args[0], nothing]);
            b.call(reverse, &[reversed, args[1]])
        });
        prepend
    }

    /// `a(list, x) = p(list, push(x, empty))`.
    fn write_append(&mut self, walk: &Walk, element: TypeId, prepend: FnId) -> FnId {
        let (list, empty, push, recursive) = (walk.list, walk.empty, walk.push, walk.recursive);
        let append = self.program.declare("append", &[list, element], list);
        self.program.define(append, |b, args| {
            let nothing = b.con(empty, &[]);
            let single = if recursive == 0 {
                b.con(push, &[nothing, args[1]])
            } else {
                b.con(push, &[args[1], nothing])
            };
            b.call(prepend, &[args[0], single])
        });
        append
    }
}
