//! What a number can be, worked out from what a program does with it.
//!
//! A type says a value is a number and nothing about which numbers, so
//! deciding how wide to hold one is deciding what it could be. That is a
//! question about terms, not about storage: `Succ` is one more than what it
//! wraps, a match on `Zero` says which argument is nought in which arm, and
//! a call answers whatever the name it calls does. None of it needs a word
//! size, which is why it is worked out here and read below.
//!
//! What comes out is per term, since that is what the tier deciding
//! representation walks: every term has an answer, so how wide to hold what
//! it answers is a question with one. A term walked more than once -- an
//! arm reached at two widths, a definition gone round again -- holds what
//! it held at any of them.
//!
//! A field is held the same way: every value built into one field of one
//! constructor, anywhere, is what reading that field back can answer. That
//! is what lets a number inside a product be held as narrowly as a number
//! outside one. A value no walk sees built -- handed in at the entry, or
//! answered by something outside -- could hold anything in any field it
//! reaches.
//!
//! Nothing here is exact. A bound too wide costs a wider number and never a
//! wrong one, so where the walk cannot say -- a definition that counts up
//! without a last step, an argument from outside -- it says so and the
//! tiers below hold what they must.

use super::model::{Body, CtorId, Expr, ExprId, FnId, Range, TypeId};
use super::program::Program;
use super::{Shape, shape, single_field};
pub use crate::facts::Facts as Bounds;

/// Whether a value these bounds hold could be built with this constructor.
/// Nought is not a `Succ` of anything and nothing above nought is `Zero`,
/// and a tag is the one number it is.
fn reaches(program: &Program, held: Bounds, spine: Shape, ctor: CtorId) -> bool {
    if single_field(program, program.ctor(ctor).owner).is_some() {
        return true;
    }
    match spine {
        Shape::Spine { nil, .. } if ctor == nil => held.low == 0,
        Shape::Spine { .. } => held.high != Some(0),
        Shape::Tagged => {
            let tag = u64::from(program.tag(ctor));
            held.low <= tag && held.high.is_none_or(|high| tag <= high)
        }
    }
}

/// How many times the walk goes round before it stops trying to be exact.
/// A definition that counts up without a last step grows every round, and
/// past this a growing bound is answered with no bound at all.
const WIDEN: usize = 8;

/// And how many times it goes round at all. Past widening a bound only ever
/// settles, so this is the room that takes rather than a guess.
const ROUNDS: usize = 24;

/// Final conservative ranges consumed by lowering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Ranges {
    /// What each term answers, by the term.
    pub terms: Vec<Bounds>,
    pub matched: Vec<Bounds>,
    /// What each definition is handed, by definition.
    pub takes: Vec<Vec<Bounds>>,
    /// And what each answers.
    pub answers: Vec<Bounds>,
    /// What each constructor field holds, by its place in the field pool.
    pub fields: Vec<Bounds>,
}

pub(super) fn analyze(program: &Program, operations: &[Option<super::Operation>]) -> Ranges {
    let count = program.functions().len();
    let mut held = Propagation::start(program);

    let mut settled = false;
    for round in 0..ROUNDS {
        let mut again = false;
        for at in 0..count {
            again |= once(program, operations, &mut held, (FnId::at(at), round));
        }
        if !again {
            settled = true;
            break;
        }
    }

    // A bound still on its way up is a bound too small, and a bound too
    // small is the one mistake this must not make: it would hold a value in
    // fewer bits than the value has. Widening settles what recursion leaves
    // growing, so reaching here means something grew in a way widening does
    // not reach -- and then nothing here is known.
    if !settled {
        held.forget();
    }

    finish(program, held)
}

/// What a declaration with no body answers: what the tier above said of it,
/// and what the type it answers declares.
fn answered(program: &Program, id: FnId) -> Bounds {
    let function = program.function(id);
    let said = function.bounds().unwrap_or(Bounds::ANY);
    said.and(declared(program, function.result))
}

/// What a value of `ty` is wherever it was built: anything, but for what the
/// wrappers it is held through declare of their one field. A wrapper is its
/// field, so its declaration bounds the value itself.
fn declared(program: &Program, ty: TypeId) -> Bounds {
    let mut held = Bounds::ANY;
    let mut ty = ty;
    for _ in 0..program.types().len() {
        let Some((ctor, field)) = single_field(program, ty) else {
            break;
        };
        if let Some(bounds) = program.field_bounds(ctor, 0) {
            held = held.and(bounds);
        }
        ty = field;
    }
    held
}

/// How many field places the program declares, end to end.
fn field_slots(program: &Program) -> usize {
    (0..program.types().len())
        .flat_map(|ty| program.ctors(TypeId::at(ty)))
        .map(|ctor| ctor.fields.range().end)
        .max()
        .unwrap_or(0)
}

/// The place one field of one constructor has in the field pool.
pub(super) fn slot(program: &Program, ctor: CtorId, at: usize) -> usize {
    program.ctor(ctor).fields.range().start + at
}

/// Say that every field reachable from `roots` could hold anything its
/// declaration allows: values of those types were built where nothing here
/// walks.
fn unknown(program: &Program, roots: &[TypeId], fields: &mut [Option<Bounds>]) {
    let mut seen = vec![false; program.types().len()];
    let mut waiting = roots.to_vec();
    while let Some(ty) = waiting.pop() {
        if std::mem::replace(&mut seen[ty.index()], true) {
            continue;
        }
        for ctor in program.ctors(ty) {
            let declared = program.declared_bounds(ctor);
            for (place, declared) in fields[ctor.fields.range()].iter_mut().zip(declared) {
                *place = Some(declared.unwrap_or(Bounds::ANY));
            }
            waiting.extend_from_slice(program.types_of(ctor.fields));
        }
    }
}

/// What the walk worked out, as the tier below reads it.
fn finish(program: &Program, held: Propagation) -> Ranges {
    // A spine's rest is read as a step of its count, not as what was built
    // there, so nothing is said of that field.
    let mut fields: Vec<_> = held.fields.into_iter().map(anything).collect();
    for ty in 0..program.types().len() {
        if let Shape::Spine {
            cons, recursive, ..
        } = shape(program, TypeId::at(ty))
        {
            fields[slot(program, cons, recursive)] = Bounds::ANY;
        }
        // What a declaration promises holds wherever the value was built.
        for ctor in program.ctors(TypeId::at(ty)) {
            let declared = program.declared_bounds(ctor);
            for (held, declared) in fields[ctor.fields.range()].iter_mut().zip(declared) {
                if let Some(declared) = declared {
                    *held = held.and(declared);
                }
            }
        }
    }
    // A term nothing reached is a term nothing knows, and so is a parameter
    // nothing was ever handed.
    Ranges {
        matched: held
            .matched
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
        terms: held
            .terms
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
        takes: held
            .params
            .into_iter()
            .map(|held| held.into_iter().map(anything).collect())
            .collect(),
        answers: held.results.into_iter().map(anything).collect(),
        fields,
    }
}

/// What nothing known comes out as. The walk starts at nothing so that one
/// name's ignorance does not spread to every name that calls it; what comes
/// out is read by a tier that has to hold something, and nothing known
/// there means anything at all.
const fn anything(held: Option<Bounds>) -> Bounds {
    match held {
        Some(held) if !held.is_nothing() => held,
        _ => Bounds::ANY,
    }
}

/// What the walk has worked out so far, which is what it goes round again
/// to add to.
struct Propagation {
    params: Vec<Vec<Option<Bounds>>>,
    results: Vec<Option<Bounds>>,
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    /// What each field was built with, by its place in the field pool.
    fields: Vec<Option<Bounds>>,
}

impl Propagation {
    /// Where the walk starts: nothing known of anything reached from inside,
    /// and anything at all in the fields of what comes in from outside.
    fn start(program: &Program) -> Self {
        let count = program.functions().len();
        let entry = program.entry();
        // A parameter nothing has handed anything to yet is a parameter nothing
        // is known of, which is not the same as one anything could be handed.
        let mut held = Self {
            params: (0..count)
                .map(|at| {
                    let id = FnId::at(at);
                    if entry == Some(id) {
                        program
                            .parameter_bounds(id)
                            .zip(program.params(id))
                            .map(|(bounds, &ty)| {
                                Some(bounds.unwrap_or(Bounds::ANY).and(declared(program, ty)))
                            })
                            .collect()
                    } else {
                        vec![None; program.params(id).len()]
                    }
                })
                .collect(),
            results: vec![None; count],
            terms: vec![Bounds::NOTHING; program.exprs_count()],
            matched: vec![Bounds::NOTHING; program.exprs_count()],
            fields: vec![None; field_slots(program)],
        };
        // What comes in from outside was built where no walk sees it.
        let mut outside: Vec<TypeId> = Vec::new();
        for (at, function) in program.functions().iter().enumerate() {
            if entry == Some(FnId::at(at)) {
                outside.extend_from_slice(program.params(FnId::at(at)));
            }
            if function.body().is_none() {
                outside.push(function.result);
            }
        }
        unknown(program, &outside, &mut held.fields);
        held
    }

    /// Say nothing is known, which is what a walk that did not settle knows.
    fn forget(&mut self) {
        self.terms.fill(Bounds::ANY);
        self.matched.fill(Bounds::ANY);
        self.params.iter_mut().flatten().for_each(|held| {
            *held = Some(Bounds::ANY);
        });
        self.results.fill(Some(Bounds::ANY));
        self.fields.fill(Some(Bounds::ANY));
    }

    /// Take in what one walk found it built and called, answering whether
    /// any of it was more than was known.
    fn learn(&mut self, program: &Program, found: Found, round: usize) -> bool {
        let mut again = false;
        for (place, bounds) in found.built {
            again |= settle(&mut self.fields[place], bounds, round);
        }
        if !found.outside.is_empty() {
            let before = self.fields.clone();
            unknown(program, &found.outside, &mut self.fields);
            again |= self.fields != before;
        }
        for (called, args) in found.calls {
            for (at, bounds) in args.into_iter().enumerate() {
                again |= settle(&mut self.params[called.index()][at], bounds, round);
            }
        }
        again
    }
}

/// How a matched constructor's fields are bound: all alike, or each as what
/// was built into it, but for a spine's rest, which is its count less one.
#[derive(Clone, Copy)]
enum Binding {
    Whole(Bounds),
    Built(Option<(usize, Bounds)>),
}

/// What one walk hands on: the arguments it called with, what it built into
/// each field, and the types of values it met built out of sight.
struct Found {
    calls: Vec<(FnId, Vec<Bounds>)>,
    built: Vec<(usize, Bounds)>,
    outside: Vec<TypeId>,
}

/// One definition, once. Answers whether anything it worked out was more
/// than what was already known, which is what says to go round again.
fn once(
    program: &Program,
    operations: &[Option<super::Operation>],
    held: &mut Propagation,
    (id, round): (FnId, usize),
) -> bool {
    let at = id.index();
    let params: Option<Vec<Bounds>> = held.params[at].iter().copied().collect();
    let Some(params) = params else { return false };
    let Some(body) = program.function(id).body() else {
        // Something outside answers, and nothing about a declaration can be
        // read, so what comes back from one is what the tier above said.
        return settle(&mut held.results[at], answered(program, id), round);
    };

    // A recognized equation is evaluated as that operation, not walked as
    // unary recursion. Besides being cheaper, this avoids widening a huge
    // countdown one predecessor at a time.
    if let Some(op) = operations[at] {
        return settle(
            &mut held.results[at],
            operation(program, op, params[0], params[1]),
            round,
        );
    }

    // Results change only after this walk; borrowing retains the same
    // per-function snapshot without copying the whole table each round.
    let mut walk = FunctionWalk {
        program,
        operations,
        results: &held.results,
        fields: &held.fields,
        built: Vec::new(),
        outside: Vec::new(),
        predicates: vec![None; params.len()],
        scope: params,
        terms: std::mem::take(&mut held.terms),
        matched: std::mem::take(&mut held.matched),
        calls: Vec::new(),
    };
    let answer = walk.body(body);
    held.terms = walk.terms;
    held.matched = walk.matched;
    let found = Found {
        calls: walk.calls,
        built: walk.built,
        outside: walk.outside,
    };
    let again = settle(&mut held.results[at], answer, round);
    held.learn(program, found, round) || again
}

/// Widen `held` by `found`, answering whether that changed it. Past the
/// rounds worth being exact for, a bound that grows is given no bound in the
/// direction it grew: a definition counting up without a last step, or down
/// from a large constant, would otherwise be walked once for every number
/// it can reach.
fn settle(held: &mut Option<Bounds>, found: Bounds, round: usize) -> bool {
    let Some(before) = *held else {
        *held = Some(found);
        return true;
    };
    if found.within(before) {
        return false;
    }
    let after = before.or(found);
    *held = Some(if round < WIDEN {
        after
    } else {
        // Past the rounds worth being exact for, a bound that moves is given
        // up in the direction it moved: a count going up has no greatest,
        // and one counting down from a large constant has nought as least.
        Bounds {
            low: if after.low < before.low {
                0
            } else {
                before.low
            },
            high: if after.high == before.high {
                before.high
            } else {
                None
            },
        }
    });
    *held != Some(before)
}

/// One walk over one definition, with what it hands to what it calls.
struct FunctionWalk<'a> {
    program: &'a Program,
    operations: &'a [Option<super::Operation>],
    results: &'a [Option<Bounds>],
    /// What each field was built with so far, and what this walk builds.
    fields: &'a [Option<Bounds>],
    built: Vec<(usize, Bounds)>,
    /// Types of values this walk found built where it cannot see inside.
    outside: Vec<TypeId>,
    /// What each level holds here, which arms take back as they end.
    scope: Vec<Bounds>,
    predicates: Vec<Option<(super::Operation, usize, usize)>>,
    /// And what each term answers, joined over every walk of it.
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    calls: Vec<(FnId, Vec<Bounds>)>,
}

impl FunctionWalk<'_> {
    fn body(&mut self, body: Body) -> Bounds {
        for &binding in self.program.bindings(body.bindings) {
            let held = self.expr(binding);
            if let Expr::Call(called, _) = self.program.expr(binding)
                && self
                    .program
                    .ctors(self.program.function(called).result)
                    .is_empty()
            {
                return Bounds::NOTHING;
            }
            let predicate = match self.program.expr(binding) {
                Expr::Call(called, args) => {
                    let op = self.operations[called.index()];
                    match op {
                        Some(
                            op @ (super::Operation::Equals { .. }
                            | super::Operation::LessThan { .. }),
                        ) => {
                            let args = self.program.atoms(args);
                            Some((op, args[0].0.index(), args[1].0.index()))
                        }
                        _ => None,
                    }
                }
                Expr::Atom(a) => self.predicates[a.0.index()],
                _ => None,
            };
            self.scope.push(held);
            self.predicates.push(predicate);
        }
        self.expr(body.tail)
    }

    /// What a term answers, held against the term so that the tier below
    /// has it where it walks.
    fn expr(&mut self, id: ExprId) -> Bounds {
        let held = self.worked(id);
        self.terms[id.index()] = self.terms[id.index()].or(held);
        held
    }

    fn worked(&mut self, id: ExprId) -> Bounds {
        match self.program.expr(id) {
            Expr::Atom(atom) => self.scope[atom.0.index()],
            Expr::Static(value) => {
                let value = self.program.constant(value);
                self.constant_fields(value);
                constant_bounds(self.program, value)
            }
            Expr::Con(ctor, args) => {
                for (at, atom) in self.program.atoms(args).iter().enumerate() {
                    let place = slot(self.program, ctor, at);
                    self.built.push((place, self.scope[atom.0.index()]));
                }
                self.built(ctor, args)
            }
            Expr::Call(called, args) => self.call(called, args),
            Expr::Match(scrutinee, arms) => {
                self.matched[id.index()] =
                    self.matched[id.index()].or(self.scope[scrutinee.0.index()]);
                self.branch(scrutinee.0.index(), arms)
            }
        }
    }

    fn call(&mut self, called: FnId, args: Range) -> Bounds {
        let held: Vec<Bounds> = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| self.scope[atom.0.index()])
            .collect();
        let answer = match self.operations.get(called.index()).copied().flatten() {
            Some(op) => operation(self.program, op, held[0], held[1]),
            None => self.results[called.index()].unwrap_or(Bounds::NOTHING),
        };
        self.calls.push((called, held));
        if self
            .program
            .ctors(self.program.function(called).result)
            .is_empty()
        {
            Bounds::NOTHING
        } else {
            answer
        }
    }

    /// Record what a known value holds in each field, all the way down. A
    /// spine is read as a count, not field by field, so what one holds is
    /// said to be anything.
    fn constant_fields(&mut self, value: super::Constant<'_>) {
        let super::ConstantView::Constructor(ctor) = value.view() else {
            if let super::ConstantView::Spine(spine) = value.view() {
                self.spine_fields(value.owner(), spine);
            }
            return;
        };
        let mut budget = super::Budget::new(super::FoldLimits {
            work: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let fields = ctor
            .fields(&mut budget)
            .expect("validated constants can be revisited");
        for (at, field) in fields.into_iter().enumerate() {
            let place = slot(self.program, ctor.constructor(), at);
            self.built
                .push((place, constant_bounds(self.program, field)));
            self.constant_fields(field);
        }
    }

    /// A run of bytes holds each byte in its element field. A spine of
    /// anything else is not read element by element here, so its fields
    /// could hold anything.
    fn spine_fields(&mut self, owner: TypeId, spine: super::SpineView<'_>) {
        let (
            Shape::Spine {
                cons, recursive, ..
            },
            Some(bytes),
        ) = (shape(self.program, owner), spine.to_bytes())
        else {
            self.outside.push(owner);
            return;
        };
        let (Some(&low), Some(&high)) = (bytes.iter().min(), bytes.iter().max()) else {
            return;
        };
        let element = usize::from(recursive == 0);
        self.built.push((
            slot(self.program, cons, element),
            Bounds {
                low: u64::from(low),
                high: Some(u64::from(high)),
            },
        ));
    }

    /// A number's empty constructor is nought and its other one is one more
    /// than what it wraps. A tag is which constructor it is.
    fn built(&self, ctor: CtorId, args: Range) -> Bounds {
        let owner = self.program.ctor(ctor).owner;
        if single_field(self.program, owner).is_some() {
            let promised = self.program.field_bounds(ctor, 0).unwrap_or(Bounds::ANY);
            return self
                .program
                .atoms(args)
                .first()
                .map_or(Bounds::ANY, |atom| self.scope[atom.0.index()])
                .and(promised);
        }
        let Shape::Spine { nil, cons, .. } = shape(self.program, owner) else {
            return Bounds::at(u64::from(self.program.tag(ctor)));
        };
        if self.program.fields(cons).len() != 1 {
            return Bounds::ANY;
        }
        if ctor == nil {
            return Bounds::at(0);
        }
        self.program
            .atoms(args)
            .first()
            .map_or(Bounds::ANY, |atom| self.scope[atom.0.index()].up())
    }

    /// Each arm in turn, with what the constructor it matched says of the
    /// value it took apart. What the match holds is what any arm holds.
    fn branch(&mut self, scrutinee: usize, arms: Range) -> Bounds {
        let mut answer = None;
        let outer = self.scope.clone();
        let predicates = self.predicates.clone();
        let mut surviving: Option<Vec<Bounds>> = None;
        for arm in self.program.arms(arms) {
            self.scope.clone_from(&outer);
            self.predicates.clone_from(&predicates);
            let level = self.scope.len();
            if !self.enter(scrutinee, arm.ctor) {
                continue;
            }
            let found = self.body(arm.body);
            answer = Some(answer.map_or(found, |held: Bounds| held.or(found)));
            if !found.is_nothing() {
                let inner = &self.scope[..level];
                if let Some(surviving) = &mut surviving {
                    for (held, found) in surviving.iter_mut().zip(inner) {
                        *held = held.or(*found);
                    }
                } else {
                    surviving = Some(inner.to_vec());
                }
            }
        }
        self.scope = surviving.unwrap_or(outer);
        self.predicates = predicates;
        // Where no arm is reached, nothing is: a value nothing knows yet is
        // a value no constructor could have built.
        answer.unwrap_or(Bounds::NOTHING)
    }

    fn enter(&mut self, scrutinee: usize, ctor: CtorId) -> bool {
        let held = self.scope[scrutinee];
        let owner = self.program.ctor(ctor).owner;
        let spine = shape(self.program, owner);
        if !reaches(self.program, held, spine, ctor) {
            return false;
        }
        let binding = if single_field(self.program, owner).is_some() {
            let promised = self.program.field_bounds(ctor, 0).unwrap_or(Bounds::ANY);
            Binding::Whole(held.and(promised))
        } else {
            match spine {
                Shape::Spine { nil, .. } if ctor == nil => {
                    self.scope[scrutinee] = Bounds::at(0);
                    Binding::Whole(Bounds::NOTHING)
                }
                Shape::Spine { recursive, .. } => {
                    self.scope[scrutinee] = Bounds {
                        low: held.low.max(1),
                        high: held.high,
                    };
                    Binding::Built(Some((recursive, self.scope[scrutinee].down())))
                }
                Shape::Tagged => {
                    self.scope[scrutinee] = Bounds::at(u64::from(self.program.tag(ctor)));
                    Binding::Built(None)
                }
            }
        };
        self.bind_fields(ctor, binding);
        if let Some((op, left, right)) = self.predicates[scrutinee] {
            let (a, b) = refine(op, ctor, self.scope[left], self.scope[right]);
            self.scope[left] = a;
            self.scope[right] = b;
            if a.is_nothing() || b.is_nothing() {
                return false;
            }
        }
        self.predicates.resize(self.scope.len(), None);
        true
    }

    /// Bind a constructor's fields. A field holds what was built into it --
    /// nothing yet, where no walk has built one -- and one whose type is a
    /// run of bare tags is one of them besides: the type says that much
    /// alone. The rest of a spine is one step down its count instead.
    fn bind_fields(&mut self, ctor: CtorId, binding: Binding) {
        for (at, &ty) in self.program.fields(ctor).iter().enumerate() {
            let counted = match binding {
                Binding::Whole(held) => Some(held),
                Binding::Built(Some((recursive, rest))) if recursive == at => Some(rest),
                Binding::Built(_) => None,
            };
            if let Some(held) = counted {
                self.scope.push(held);
                continue;
            }
            let built = self.fields[slot(self.program, ctor, at)].unwrap_or(Bounds::NOTHING);
            self.scope
                .push(tag_count(self.program, ty).map_or(built, |count| {
                    built.and(Bounds {
                        low: 0,
                        high: Some(count - 1),
                    })
                }));
        }
    }
}

/// How many tags a type has, where its constructors all carry nothing and
/// there are at least two of them: a value of one is a tag below this.
fn tag_count(program: &Program, ty: TypeId) -> Option<u64> {
    (super::type_shape(program, ty) == super::TypeShape::Enumeration)
        .then(|| u64::try_from(program.ctors(ty).len()).expect("a count of constructors"))
}

fn constant_bounds(program: &Program, value: super::Constant<'_>) -> Bounds {
    let value = super::single_field_constant(program, value);
    match value.view() {
        super::ConstantView::Natural(number) => number.try_u64().map_or(Bounds::ANY, Bounds::at),
        super::ConstantView::Constructor(ctor)
            if program
                .ctors(value.owner())
                .iter()
                .all(|c| program.types_of(c.fields).is_empty()) =>
        {
            Bounds::at(u64::from(program.tag(ctor.constructor())))
        }
        super::ConstantView::Constructor(_) | super::ConstantView::Spine(_) => Bounds::ANY,
    }
}

fn operation(program: &Program, op: super::Operation, a: Bounds, b: Bounds) -> Bounds {
    use super::Operation;
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let (yes, no, decided) = match op {
        Operation::Add => return a.plus(b),
        Operation::Monus => return a.monus(b),
        Operation::Mul => return a.times(b),
        Operation::Div => return a.quotient(b),
        Operation::Mod => return a.remainder(b),
        Operation::Equals { yes, no } => (
            yes,
            no,
            if a.high == Some(a.low) && b.high == Some(b.low) {
                Some(a.low == b.low)
            } else if a.high.is_some_and(|a| a < b.low) || b.high.is_some_and(|b| b < a.low) {
                Some(false)
            } else {
                None
            },
        ),
        Operation::LessThan { yes, no } => (
            yes,
            no,
            if a.high.is_some_and(|a| a < b.low) {
                Some(true)
            } else if b.high.is_some_and(|b| a.low >= b) {
                Some(false)
            } else {
                None
            },
        ),
    };
    let yes = Bounds::at(u64::from(program.tag(yes)));
    let no = Bounds::at(u64::from(program.tag(no)));
    decided.map_or_else(|| yes.or(no), |held| if held { yes } else { no })
}

fn exclude(held: Bounds, other: Bounds) -> Bounds {
    if other.high != Some(other.low) {
        return held;
    }
    if held.low == other.low {
        return held.and(Bounds {
            low: held.low.saturating_add(1),
            high: None,
        });
    }
    if held.high == Some(other.low) {
        return held.and(Bounds {
            low: 0,
            high: other.low.checked_sub(1),
        });
    }
    held
}

fn refine(op: super::Operation, ctor: CtorId, a: Bounds, b: Bounds) -> (Bounds, Bounds) {
    use super::Operation;
    match op {
        Operation::Equals { yes, .. } if ctor == yes => (a.and(b), b.and(a)),
        Operation::Equals { .. } => (exclude(a, b), exclude(b, a)),
        Operation::LessThan { yes, .. } if ctor == yes => {
            let a_limit = b.high.map_or(Bounds::ANY, |high| {
                high.checked_sub(1).map_or(Bounds::NOTHING, |high| Bounds {
                    low: 0,
                    high: Some(high),
                })
            });
            (
                a.and(a_limit),
                b.and(Bounds {
                    low: a.low.saturating_add(1),
                    high: None,
                }),
            )
        }
        Operation::LessThan { .. } => (
            a.and(Bounds {
                low: b.low,
                high: None,
            }),
            b.and(Bounds {
                low: 0,
                high: a.high,
            }),
        ),
        _ => (a, b),
    }
}
