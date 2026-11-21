//! A program's numbers, apart from everything else it does.
//!
//! Range analysis asks what each number can be. A Barb definition does
//! much besides counting -- builds records, picks tags, calls the host --
//! and walking all of it every time round a recursion is most of what the
//! analysis costs. So each definition is first read once into a small
//! numeric program ([`extract`]): a run of statements over values, each a
//! constant, a copy, a step, an operation, a call, a read of a field or a
//! match whose arms say what holds on entry. A tag is the number it is, a
//! sequence is its length, a field is a slot shared by every value built
//! into it, and a record or a function value is a value nothing is known
//! of. What the solver works out of it ([`super::solve`]) is mapped back
//! to Barb by the term each statement came from.
//!
//! The numeric program keeps Barb's scoping: each statement binds the next
//! value, an arm binds its fields after the values before its match, and
//! two arms side by side bind the same places to different values. So a
//! value is named by its place in scope, as a Barb local is, and the
//! solver walks a numeric body as it would the Barb body, without asking
//! the program what any of it is.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use super::facts::{Operation, Recognised, SequenceOperation};
use super::model::{Body, CtorId, Expr, ExprId, FnId, TypeId};
use super::program::Program;
use super::{Shape, shape, single_field};
use crate::Bounds;

/// A value of a definition, by its place in scope: the parameters first,
/// then each statement and each arm's fields in turn.
pub(super) type Var = usize;

/// Where a value is made, numbered across a definition: a parameter, a
/// statement or a field an arm binds. What the solver relates is the value
/// made, not the place in scope, which two arms side by side share.
pub(super) type Site = usize;

/// A whole program's numbers.
#[derive(Debug, Default)]
pub(super) struct Numeric {
    pub functions: Vec<Function>,
    /// How many field slots there are.
    pub slots: usize,
    /// What each slot holds before anything is built: what is assumed of a
    /// field of a value built out of sight, by slot.
    pub outside: Vec<(usize, Bounds)>,
    /// Every number a remainder is taken by, less one: where a value kept
    /// below one by a remainder is widened to.
    pub divisors: Vec<u64>,
    /// The most any sequence's length can be, where anything says.
    pub length: Option<Bounds>,
    /// How many terms the Barb program has, which the solver's findings are
    /// indexed by.
    pub terms: usize,
}

/// One definition.
#[derive(Debug)]
pub(super) struct Function {
    /// How many parameters it takes, and whether each is a count, a number
    /// or a length, worth relating to the others.
    pub counts: Vec<bool>,
    /// What its entry is handed from outside, where it is the entry.
    pub handed: Option<Vec<Bounds>>,
    pub answer: Answer,
}

/// How a definition answers.
#[derive(Debug)]
pub(super) enum Answer {
    /// By walking its body.
    Body(Block),
    /// By what is assumed of it: a declaration, or a length.
    Known(Bounds),
    /// As the operation it was recognized as, a comparison answering the
    /// tags given.
    Operation(Operation, (u64, u64)),
}

/// A run of statements and the term they are for.
#[derive(Debug, Default)]
pub(super) struct Block {
    pub statements: Vec<Statement>,
    pub tail: Term,
}

/// A term bound to the next value.
#[derive(Debug)]
pub(super) struct Statement {
    pub site: Site,
    pub term: Term,
}

/// A term, and the Barb term it came from, which what it answers is
/// recorded against.
#[derive(Debug)]
pub(super) struct Term {
    pub expr: usize,
    pub kind: Kind,
}

impl Default for Term {
    fn default() -> Self {
        Self {
            expr: 0,
            kind: Kind::Copy(0),
        }
    }
}

/// What a term computes.
#[derive(Debug)]
pub(super) enum Kind {
    /// The value another names.
    Copy(Var),
    /// A value known outright, `exact` where past what a bound says, and
    /// what it puts in each slot, all the way down.
    Const {
        value: Bounds,
        exact: Option<u128>,
        stores: Vec<(usize, Bounds)>,
        /// Slots of values it holds that are built out of sight, each now
        /// what is assumed of it.
        resets: Vec<(usize, Bounds)>,
    },
    /// A constructor applied: each argument stored in its slot.
    Build {
        args: Vec<Var>,
        slots: usize,
        built: Built,
    },
    /// A call: of a recognized operation, a sequence operation, or a
    /// definition answering what it answers. `float` is the pattern a
    /// machine's float operation may answer, and the wrapper slots it is
    /// built into; `never` says the call does not come back.
    Call {
        callee: usize,
        args: Vec<Var>,
        operation: Option<Operation>,
        /// The tags a comparison answers, true first.
        tags: (u64, u64),
        sequence: Option<SequenceOperation>,
        float: Option<(Bounds, Vec<usize>)>,
        never: bool,
    },
    /// A match on a value, an arm a constructor. `told` says what each tag
    /// the match answers says is worth gathering, since it is matched on
    /// its tag later.
    Match { on: Var, arms: Vec<Arm>, told: bool },
}

/// What a constructor builds.
#[derive(Debug)]
pub(super) enum Built {
    /// A wrapper: its one argument, within what is promised of it.
    Wrap(Bounds),
    /// A number's or a sequence's empty end: nought.
    Empty,
    /// A step of a number or a sequence: one more than the rest at `rest`.
    Step(usize),
    /// A tag: the number it is.
    Tag(u64),
}

/// One arm: which constructor it takes, what that says of the value
/// matched, and what its fields are.
#[derive(Debug)]
pub(super) struct Arm {
    pub test: Test,
    pub fields: Vec<(Site, Field)>,
    pub body: Block,
}

/// What an arm says of the value it matched.
#[derive(Debug, Clone, Copy)]
pub(super) enum Test {
    /// A wrapper's arm: always reached, its field the value, within what
    /// is promised of it.
    Wrapper(Bounds),
    /// The empty end: nought.
    Empty,
    /// A step: at least one, its field at `rest` one less.
    Step(usize),
    /// A tag: the number it is.
    Tag(u64),
}

/// What a field an arm binds holds.
#[derive(Debug, Clone, Copy)]
pub(super) enum Field {
    /// The value matched, as a wrapper's arm binds it, or nothing, as an
    /// empty end's does.
    Whole,
    /// A step's rest: one less than the value matched.
    Rest,
    /// What was built into a slot, below `tags` where its type is a run of
    /// bare tags.
    Slot { slot: usize, tags: Option<u64> },
}

/// Read every definition of `program` into numbers.
#[expect(
    clippy::too_many_lines,
    reason = "every definition read, then what comes in from outside"
)]
pub(super) fn extract(
    program: &Program,
    recognised: &Recognised,
    assumed: &super::Assumed,
) -> Numeric {
    let entry = program.entry();
    let mut divisors = Vec::new();
    let functions = (0..program.functions().len())
        .map(|at| {
            let id = FnId::at(at);
            let params = program.params(id);
            let counts = params.iter().map(|&ty| counts(program, ty)).collect();
            let handed = (entry == id).then(|| {
                params
                    .iter()
                    .enumerate()
                    .map(|(at, &ty)| assumed.parameter(at).and(assumed.value(program, ty)))
                    .collect()
            });
            let answer = match program.function(id).body() {
                None => {
                    let result = program.function(id).result;
                    Answer::Known(assumed.result(id).and(assumed.value(program, result)))
                }
                Some(_) if let Some(operation) = recognised.operations[at] => {
                    Answer::Operation(operation, tags(program, operation))
                }
                Some(_) if recognised.sequences[at] == Some(SequenceOperation::Length) => {
                    Answer::Known(assumed.length.unwrap_or(Bounds::ANY))
                }
                Some(body) => {
                    let mut reading = Reading {
                        program,
                        recognised,
                        assumed,
                        told: told(program, body, params.len()),
                        sites: params.len(),
                        known: vec![None; params.len()],
                        divisors: &mut divisors,
                    };
                    Answer::Body(reading.block(body))
                }
            };
            Function {
                counts,
                handed,
                answer,
            }
        })
        .collect();
    divisors.sort_unstable();
    divisors.dedup();
    // What comes in from outside was built where no walk sees it.
    let mut outside: Vec<TypeId> = Vec::new();
    for (at, function) in program.functions().iter().enumerate() {
        if entry == FnId::at(at) {
            outside.extend_from_slice(program.params(FnId::at(at)));
        }
        if function.body().is_none() {
            outside.push(function.result);
        }
    }
    Numeric {
        functions,
        slots: super::ranges::field_slots(program),
        outside: unknown(program, assumed, &outside),
        divisors,
        length: assumed.length,
        terms: program.exprs_count(),
    }
}

/// The tags a comparison answers, true first; none for anything else.
fn tags(program: &Program, operation: Operation) -> (u64, u64) {
    match operation {
        Operation::Equals { yes, no } | Operation::LessThan { yes, no } => {
            (u64::from(program.tag(yes)), u64::from(program.tag(no)))
        }
        _ => (0, 0),
    }
}

/// What every field reachable from `roots` is assumed to hold, by slot:
/// values of those types were built where nothing here walks.
pub(super) fn unknown(
    program: &Program,
    assumed: &super::Assumed,
    roots: &[TypeId],
) -> Vec<(usize, Bounds)> {
    let mut found = Vec::new();
    let mut seen = vec![false; program.types().len()];
    let mut waiting = roots.to_vec();
    while let Some(ty) = waiting.pop() {
        if std::mem::replace(&mut seen[ty.index()], true) {
            continue;
        }
        for (tag, ctor) in program.ctors(ty).iter().enumerate() {
            let id = program.ctor_at(ty, u32::try_from(tag).expect("a sane constructor count"));
            for (at, place) in ctor.fields.range().enumerate() {
                found.push((place, assumed.field(id, at)));
            }
            waiting.extend_from_slice(program.types_of(ctor.fields));
        }
    }
    found
}

/// Whether a value of `ty` is a count: a number or a sequence, whose
/// bounds are how many steps it takes, or a wrapper of one.
fn counts(program: &Program, ty: TypeId) -> bool {
    let mut ty = ty;
    for _ in 0..program.types().len() {
        match single_field(program, ty) {
            Some((_, field)) => ty = field,
            None => break,
        }
    }
    matches!(shape(program, ty), Shape::Spine { .. })
}

/// How many tags a type has, where its constructors all carry nothing and
/// there are at least two of them: a value of one is a tag below this.
fn tag_count(program: &Program, ty: TypeId) -> Option<u64> {
    (super::type_shape(program, ty) == super::TypeShape::Enumeration)
        .then(|| u64::try_from(program.ctors(ty).len()).expect("a count of constructors"))
}

/// The most elements of a constant sequence read one by one for what its
/// fields hold; past this, its fields could hold anything.
const ELEMENTS_READ: u64 = 4096;

struct Reading<'a> {
    program: &'a Program,
    recognised: &'a Recognised,
    assumed: &'a super::Assumed,
    told: HashSet<ExprId>,
    /// How many sites are numbered so far.
    sites: Site,
    /// The natural each value in scope is outright, where it is one.
    known: Vec<Option<u128>>,
    divisors: &'a mut Vec<u64>,
}

impl Reading<'_> {
    const fn site(&mut self) -> Site {
        self.sites += 1;
        self.sites - 1
    }

    fn block(&mut self, body: Body) -> Block {
        let level = self.known.len();
        let mut statements = Vec::new();
        for &binding in self.program.bindings(body.bindings) {
            let term = self.term(binding);
            let known = match &term.kind {
                Kind::Const { exact, .. } => *exact,
                Kind::Copy(from) => self.known[*from],
                _ => None,
            };
            let site = self.site();
            statements.push(Statement { site, term });
            self.known.push(known);
        }
        let tail = self.term(body.tail);
        self.known.truncate(level);
        Block { statements, tail }
    }

    fn atoms(&self, args: super::Range) -> Vec<Var> {
        self.program
            .atoms(args)
            .iter()
            .map(|atom| atom.0.index())
            .collect()
    }

    fn term(&mut self, id: ExprId) -> Term {
        let kind = match self.program.expr(id) {
            Expr::Atom(atom) => Kind::Copy(atom.0.index()),
            Expr::Static(value) => self.constant(value),
            Expr::Con(ctor, args) => self.build(ctor, args),
            Expr::Call(called, args) => self.call(called, args),
            Expr::Match(scrutinee, arms) => Kind::Match {
                on: scrutinee.0.index(),
                arms: self
                    .program
                    .arms(arms)
                    .iter()
                    .map(|arm| self.arm(arm.ctor, arm.body))
                    .collect(),
                told: self.told.contains(&id),
            },
        };
        Term {
            expr: id.index(),
            kind,
        }
    }

    fn constant(&self, value: super::ConstId) -> Kind {
        let constant = self.program.constant(value);
        let exact = match constant.view() {
            super::ConstantView::Natural(number) => u128::try_from(number.to_biguint()).ok(),
            _ => None,
        };
        let mut found = Constants {
            program: self.program,
            stores: Vec::new(),
            outside: Vec::new(),
        };
        found.fields(constant);
        Kind::Const {
            value: constant_bounds(self.program, constant),
            exact,
            stores: found.stores,
            resets: unknown(self.program, self.assumed, &found.outside),
        }
    }

    fn build(&self, ctor: CtorId, args: super::Range) -> Kind {
        let owner = self.program.ctor(ctor).owner;
        let built = if single_field(self.program, owner).is_some() {
            Built::Wrap(self.assumed.field(ctor, 0))
        } else {
            match shape(self.program, owner) {
                Shape::Spine { nil, .. } if ctor == nil => Built::Empty,
                Shape::Spine { recursive, .. } => Built::Step(recursive),
                Shape::Tagged => Built::Tag(u64::from(self.program.tag(ctor))),
            }
        };
        Kind::Build {
            args: self.atoms(args),
            slots: super::ranges::slot(self.program, ctor, 0),
            built,
        }
    }

    fn call(&mut self, called: FnId, args: super::Range) -> Kind {
        let args = self.atoms(args);
        let operation = self.recognised.operations[called.index()];
        if operation == Some(Operation::Mod)
            && let Some(Some(divisor)) = args.get(1).map(|&at| self.known[at])
            && divisor > 0
            && let Ok(below) = u64::try_from(divisor - 1)
        {
            self.divisors.push(below);
        }
        let function = self.program.function(called);
        let float = function.float.and_then(|float| {
            let (wrappers, _) = super::floats::wrapped(self.program, function.result)?;
            let pattern = Bounds {
                low: 0,
                high: Some(float.format.greatest()),
            };
            let slots = wrappers
                .into_iter()
                .map(|wrapper| super::ranges::slot(self.program, wrapper, 0))
                .collect();
            Some((pattern, slots))
        });
        Kind::Call {
            callee: called.index(),
            args,
            operation,
            tags: operation.map_or((0, 0), |operation| tags(self.program, operation)),
            sequence: self.recognised.sequences[called.index()],
            float,
            never: self.program.ctors(function.result).is_empty(),
        }
    }

    fn arm(&mut self, ctor: CtorId, body: Body) -> Arm {
        let owner = self.program.ctor(ctor).owner;
        let types = self.program.fields(ctor).to_vec();
        let (test, rest) = if single_field(self.program, owner).is_some() {
            (Test::Wrapper(self.assumed.field(ctor, 0)), None)
        } else {
            match shape(self.program, owner) {
                Shape::Spine { nil, .. } if ctor == nil => (Test::Empty, None),
                Shape::Spine { recursive, .. } => (Test::Step(recursive), Some(recursive)),
                Shape::Tagged => (Test::Tag(u64::from(self.program.tag(ctor))), None),
            }
        };
        let fields = types
            .iter()
            .enumerate()
            .map(|(at, &ty)| {
                let field = match test {
                    Test::Wrapper(_) | Test::Empty => Field::Whole,
                    _ if rest == Some(at) => Field::Rest,
                    _ => Field::Slot {
                        slot: super::ranges::slot(self.program, ctor, at),
                        tags: tag_count(self.program, ty),
                    },
                };
                (self.site(), field)
            })
            .collect();
        let level = self.known.len();
        self.known.resize(level + types.len(), None);
        let body = self.block(body);
        self.known.truncate(level);
        Arm { test, fields, body }
    }
}

/// What a known value holds in each field, all the way down, and the types
/// of what it holds that are read as anything.
struct Constants<'a> {
    program: &'a Program,
    stores: Vec<(usize, Bounds)>,
    outside: Vec<TypeId>,
}

impl Constants<'_> {
    /// A spine is read as a count, not field by field, so what one holds is
    /// said element by element where short, and to be anything where long.
    fn fields(&mut self, value: super::Constant<'_>) {
        let super::ConstantView::Constructor(ctor) = value.view() else {
            if let super::ConstantView::Spine(spine) = value.view() {
                self.spine_fields(value.owner(), spine);
            }
            return;
        };
        for (at, field) in ctor.fields().into_iter().enumerate() {
            let place = super::ranges::slot(self.program, ctor.constructor(), at);
            self.stores
                .push((place, constant_bounds(self.program, field)));
            self.fields(field);
        }
    }

    /// A run of bytes holds each byte in its element field. A short spine
    /// of anything else is read element by element, as a constructor's
    /// fields are; a long one is not, so its fields could hold anything.
    fn spine_fields(&mut self, owner: TypeId, spine: super::SpineView<'_>) {
        let Shape::Spine {
            cons, recursive, ..
        } = shape(self.program, owner)
        else {
            self.outside.push(owner);
            return;
        };
        let Some(bytes) = spine.to_bytes() else {
            if spine.length() > ELEMENTS_READ.into() {
                self.outside.push(owner);
            } else {
                self.spine_elements(spine, cons, recursive);
            }
            return;
        };
        let (Some(&low), Some(&high)) = (bytes.iter().min(), bytes.iter().max()) else {
            return;
        };
        let element = usize::from(recursive == 0);
        self.stores.push((
            super::ranges::slot(self.program, cons, element),
            Bounds {
                low: u64::from(low),
                high: Some(u64::from(high)),
            },
        ));
    }

    fn spine_elements(&mut self, spine: super::SpineView<'_>, cons: CtorId, recursive: usize) {
        for fields in spine.elements() {
            for (at, field) in fields.into_iter().enumerate() {
                let at = if at >= recursive { at + 1 } else { at };
                self.stores.push((
                    super::ranges::slot(self.program, cons, at),
                    constant_bounds(self.program, field),
                ));
                self.fields(field);
            }
        }
    }
}

/// What a known value is as a number: a natural itself, a tag its number, a
/// sequence its length; anything for a record.
pub(super) fn constant_bounds(program: &Program, value: super::Constant<'_>) -> Bounds {
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
        super::ConstantView::Spine(spine) => {
            u64::try_from(spine.length()).map_or(Bounds::ANY, Bounds::at)
        }
        super::ConstantView::Constructor(_) => Bounds::ANY,
    }
}

/// The matches of a body whose answer is matched again on its tag, where
/// what each tag says of the values before it is worth gathering: a match
/// whose answer is bound and matched later as a tag, or handed through a
/// binding or as the last term of an arm of one that is.
fn told(program: &Program, body: Body, params: usize) -> HashSet<ExprId> {
    let mut found = Told {
        program,
        scope: vec![None; params],
        aliases: HashMap::default(),
        wanted: Vec::new(),
    };
    found.body(body);
    let mut told = HashSet::default();
    while let Some(expr) = found.wanted.pop() {
        if !told.insert(expr) {
            continue;
        }
        match program.expr(expr) {
            Expr::Atom(_) => found.wanted.extend(found.aliases.get(&expr)),
            Expr::Match(_, arms) => {
                found
                    .wanted
                    .extend(program.arms(arms).iter().map(|arm| arm.body.tail));
            }
            _ => {}
        }
    }
    told
}

struct Told<'a> {
    program: &'a Program,
    /// The binding each level in scope is, where it is one.
    scope: Vec<Option<ExprId>>,
    /// The binding each atom read as a term names, where it names one.
    aliases: HashMap<ExprId, ExprId>,
    wanted: Vec<ExprId>,
}

impl Told<'_> {
    fn body(&mut self, body: Body) {
        let level = self.scope.len();
        for &binding in self.program.bindings(body.bindings) {
            self.expr(binding);
            self.scope.push(Some(binding));
        }
        self.expr(body.tail);
        self.scope.truncate(level);
    }

    fn expr(&mut self, id: ExprId) {
        match self.program.expr(id) {
            Expr::Atom(atom) => {
                if let Some(binding) = self.scope[atom.0.index()] {
                    self.aliases.insert(id, binding);
                }
            }
            Expr::Match(scrutinee, arms) => {
                let arms = self.program.arms(arms);
                if let Some(arm) = arms.first() {
                    let owner = self.program.ctor(arm.ctor).owner;
                    if single_field(self.program, owner).is_none()
                        && matches!(shape(self.program, owner), Shape::Tagged)
                        && let Some(binding) = self.scope[scrutinee.0.index()]
                    {
                        self.wanted.push(binding);
                    }
                }
                for arm in arms {
                    let level = self.scope.len();
                    self.scope
                        .resize(level + self.program.fields(arm.ctor).len(), None);
                    self.body(arm.body);
                    self.scope.truncate(level);
                }
            }
            _ => {}
        }
    }
}
