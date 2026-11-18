//! A value built only to be handed to a definition that takes it apart.
//!
//! `key == [grey]` builds a one-element list and hands it to the list's
//! `equals`, which asks first which constructor it is and then reads its
//! fields. Nothing else reads the list. A copy of `equals` taking the
//! element and the rest in its place, with the list built at its top, has
//! that question decided by simplifying it: the arm it takes reads the
//! fields where the caller made them, and the list is never built.
//!
//! ```text
//! v = push(x, rest); f(a, v)          f.push(a, x, rest) = v = push(x, rest); f-body
//! ```
//!
//! A copy is kept only where simplifying it leaves fewer matches between
//! two or more arms than its original: a way through it decided for that
//! constructor. One that decides nothing would only move the building, and
//! is called by nothing, so the sweep takes it away.
//!
//! The copy's own calls are read the same way, a definition calling itself
//! included: a literal of three elements is taken apart one copy at a time,
//! each deciding one push, and a call handing back what a copy was made
//! for is sent to that copy, which then goes round by itself with nothing
//! built. A known value of a constructor with no fields, as the empty list
//! ending a literal is, is taken as that constructor wherever it is read;
//! other known values are [`super::specialize`]'s, which runs after.
//!
//! Only a construction read once, by the call, is followed, and only into
//! a definition the entry reaches with a body, that is not answered as a
//! recognized operation, and that takes the parameter apart with a match
//! of two or more arms. Copying keeps every call and effect where it was.

use std::collections::HashMap;

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::{Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, TypeId};

/// The most copies made of one definition.
const COPIES: usize = 8;
/// The largest definition copied, in what copying it allocates.
const LARGEST: usize = 4096;

/// Send every call handing a definition a construction it takes apart, and
/// that nothing else reads, to a copy taking the construction's fields.
pub(crate) fn constructions(program: &mut Program) {
    let recognised = program.recognised().clone();
    let entry = program.entry();
    let reached = super::sweep::reached(program, entry).0;
    let mut unbuilt = Unbuilt {
        recognised,
        copies: HashMap::new(),
        made: HashMap::new(),
        program,
    };
    let count = unbuilt.program.functions().len();
    for (at, &reached) in reached.iter().enumerate().take(count) {
        let id = FnId::at(at);
        if reached && !unbuilt.answered(id) {
            unbuilt.rewrite(id);
        }
    }
    // Each copy kept is read in turn, for the constructions it builds.
    let mut read = count;
    while read < unbuilt.program.functions().len() {
        let id = FnId::at(read);
        read += 1;
        if unbuilt.made.contains_key(&id) {
            unbuilt.rewrite(id);
        }
    }
}

/// The most constructors one argument is taken apart into.
const NODES: usize = 8;

/// A construction as a call hands it: its constructor, and each field that
/// is itself a construction nothing else reads, taken apart in turn.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Shape {
    ctor: CtorId,
    fields: Vec<Option<Self>>,
}

/// What each parameter of a definition is handed, where it is handed a
/// construction it takes apart.
type Key = Vec<Option<Shape>>;

/// A call handing a construction, found in a body.
struct Site {
    expr: ExprId,
    callee: FnId,
    /// Each argument as written, its shape where it is a construction read
    /// nowhere else, and what that is made of: the fields at its leaves.
    args: Vec<Atom>,
    shapes: Vec<Option<Shape>>,
    leaves: Vec<Vec<Atom>>,
}

struct Unbuilt<'a> {
    program: &'a mut Program,
    recognised: Recognised,
    /// The copy made for each definition and key, `None` where one was made
    /// and decided nothing.
    copies: HashMap<(FnId, Key), Option<FnId>>,
    /// Every copy kept, with what it was copied from and for.
    made: HashMap<FnId, (FnId, Key)>,
}

impl Unbuilt<'_> {
    fn answered(&self, id: FnId) -> bool {
        id.index() < self.recognised.operations.len() && self.recognised.answered(id)
    }

    /// Send each call in `id`'s body that hands a construction its callee
    /// takes apart to the copy made for it.
    fn rewrite(&mut self, id: FnId) {
        let Some(body) = self.program.function(id).body() else {
            return;
        };
        let mut sites = Vec::new();
        let mut known = vec![None; self.program.params(id).len()];
        self.sites(body, &mut known, &mut sites);
        for site in sites {
            if site.callee == id && !self.made.contains_key(&id) {
                continue;
            }
            let Some(key) = self.key(&site) else {
                continue;
            };
            // A copy's call handing back what it was made for goes round on
            // the copy itself.
            let copy = match self.made.get(&id) {
                Some((origin, made_for)) if *origin == site.callee && *made_for == key => Some(id),
                _ => self.copy(site.callee, &key),
            };
            let Some(copy) = copy else {
                continue;
            };
            let mut args = Vec::new();
            for (at, leaves) in site.leaves.iter().enumerate() {
                match key[at] {
                    Some(_) => args.extend(leaves.iter().copied()),
                    None => args.push(site.args[at]),
                }
            }
            let args = self.program.terms.hold_atoms(args.into_iter());
            self.program.write(site.expr, Expr::Call(copy, args));
        }
    }

    /// Every call in `body`, whose bindings and arms `known` maps to the
    /// construction each level holds where nothing but one call reads it,
    /// handing such a construction.
    fn sites(
        &self,
        body: Body,
        known: &mut Vec<Option<(CtorId, Vec<Atom>)>>,
        sites: &mut Vec<Site>,
    ) {
        let depth = known.len();
        let bindings = self.program.bindings(body.bindings);
        let reads = self.live_reads(body, depth);
        for (at, &expr) in bindings.iter().chain([&body.tail]).enumerate() {
            let held = match self.program.expr(expr) {
                Expr::Con(ctor, fields) if reads.get(at) == Some(&1) => {
                    Some((ctor, self.program.atoms(fields).to_vec()))
                }
                Expr::Static(value) => self.fieldless(value),
                Expr::Call(callee, args) => {
                    let args = self.program.atoms(args).to_vec();
                    sites.extend(site(known, expr, callee, args));
                    None
                }
                Expr::Match(_, arms) => {
                    for arm in self.program.arms(arms) {
                        let fields = self.program.fields(arm.ctor).len();
                        known.extend(std::iter::repeat_n(None, fields));
                        self.sites(arm.body, known, sites);
                        known.truncate(known.len() - fields);
                    }
                    None
                }
                Expr::Con(..) | Expr::Atom(_) => None,
            };
            known.push(held);
        }
        known.truncate(depth);
    }

    /// The constructor a known value is, where it has no fields: such as
    /// the empty list ending a literal, which is that constructor however
    /// often it is read. A number is left to [`super::specialize`].
    fn fieldless(&self, value: super::ConstId) -> Option<(CtorId, Vec<Atom>)> {
        let ctor = self.program.constant(value).constructor();
        let owner = self.program.ctor(ctor).owner;
        let natural = matches!(
            super::type_shape(self.program, owner),
            super::TypeShape::Natural { .. }
        );
        (self.program.fields(ctor).is_empty() && !natural).then(|| (ctor, Vec::new()))
    }

    /// How many times each binding of `body`, the first at level `base`, is
    /// read after it, where an arm of an earlier binding cannot bind its
    /// level again; a construction read by nothing is not counted as reading
    /// what it holds, as simplifying a copy leaves the one it took apart.
    fn live_reads(&self, body: Body, base: usize) -> Vec<usize> {
        let bindings = self.program.bindings(body.bindings);
        let mut reads = vec![0; bindings.len()];
        for at in (0..bindings.len()).rev() {
            let later = bindings[at + 1..]
                .iter()
                .enumerate()
                .filter(|&(after, &expr)| {
                    reads[at + 1 + after] > 0 || !matches!(self.program.expr(expr), Expr::Con(..))
                })
                .map(|(_, &expr)| expr)
                .chain([body.tail]);
            let later = super::walk::nested(self.program, later);
            reads[at] = super::walk::reads(self.program, later, base + at);
        }
        reads
    }

    /// Which constructions a call hands that its callee takes apart, where
    /// it hands any.
    fn key(&self, site: &Site) -> Option<Key> {
        let callee = site.callee;
        let body = self.program.function(callee).body()?;
        if self.answered(callee) || super::inline::cost(self.program, body) > LARGEST {
            return None;
        }
        let key: Key = site
            .shapes
            .iter()
            .enumerate()
            .map(|(param, shape)| shape.clone().filter(|_| self.taken_apart(body, param)))
            .collect();
        key.iter().any(Option::is_some).then_some(key)
    }

    /// Whether a body takes its parameter `param` apart with a match of two
    /// or more arms. No arm binds a parameter's level, so any match on it
    /// is on the parameter.
    fn taken_apart(&self, body: Body, param: usize) -> bool {
        super::walk::within(self.program, body).any(|expr| {
            matches!(self.program.expr(expr),
                Expr::Match(on, arms) if on.0.index() == param && arms.len() > 1)
        })
    }

    /// The copy of `id` taking each construction `key` names as its
    /// fields, made the first time it is asked for, where it decides
    /// something.
    fn copy(&mut self, id: FnId, key: &Key) -> Option<FnId> {
        if let Some(&known) = self.copies.get(&(id, key.clone())) {
            return known;
        }
        let made = self
            .copies
            .keys()
            .filter(|(origin, _)| *origin == id)
            .count();
        let copy = (made < COPIES).then(|| self.copied(id, key)).flatten();
        self.copies.insert((id, key.clone()), copy);
        if let Some(copy) = copy {
            self.made.insert(copy, (id, key.clone()));
        }
        copy
    }

    fn copied(&mut self, id: FnId, key: &Key) -> Option<FnId> {
        let body = self.program.function(id).body()?;
        let result = self.program.function(id).result;
        let before = branches(self.program, body);
        let originals = self.program.params(id).to_vec();
        let mut params: Vec<TypeId> = Vec::new();
        for (at, &ty) in originals.iter().enumerate() {
            match &key[at] {
                Some(shape) => leaf_types(self.program, shape, &mut params),
                None => params.push(ty),
            }
        }
        let name = format!(
            "{}.{}",
            self.program.name(self.program.function(id).name),
            self.program.functions().len()
        );
        let copy = self.program.declare(&name, &params, result);
        // Each construction built first, of the leaves it now takes.
        let mut scope = Scope::at(params.len());
        let mut taken = 0;
        let mut locals = Vec::new();
        for shape in key {
            let local = if let Some(shape) = shape {
                built(self.program, shape, &mut taken, &mut scope)
            } else {
                taken += 1;
                Atom(Local::at(taken - 1))
            };
            locals.push(local);
        }
        let answer = copy::into(self.program, body, locals, &mut scope, None);
        let written = copy::close(self.program, scope, answer);
        self.program.replace_bodies(vec![(copy, written)]);
        super::normalize::resimplify(self.program, &[copy]);
        let simplified = self
            .program
            .function(copy)
            .body()
            .expect("a copy has a body");
        (branches(self.program, simplified) < before).then_some(copy)
    }
}

/// A call of `callee` with `args`, where it hands a construction `known`
/// says nothing else reads.
fn site(
    known: &[Option<(CtorId, Vec<Atom>)>],
    expr: ExprId,
    callee: FnId,
    args: Vec<Atom>,
) -> Option<Site> {
    let (mut shapes, mut leaves) = (Vec::new(), Vec::new());
    for &atom in &args {
        let mut nodes = NODES;
        let mut made_of = Vec::new();
        shapes.push(taken(known, atom, &mut nodes, &mut made_of));
        leaves.push(made_of);
    }
    shapes.iter().any(Option::is_some).then_some(Site {
        expr,
        callee,
        args,
        shapes,
        leaves,
    })
}

/// The shape of what `atom` holds, where `known` says it is a construction
/// read only where it is handed on, taken apart while `nodes` lasts; the
/// atoms at its leaves, or `atom` itself, pushed onto `leaves`.
fn taken(
    known: &[Option<(CtorId, Vec<Atom>)>],
    atom: Atom,
    nodes: &mut usize,
    leaves: &mut Vec<Atom>,
) -> Option<Shape> {
    let Some((ctor, fields)) = known[atom.0.index()].as_ref().filter(|_| *nodes > 0) else {
        leaves.push(atom);
        return None;
    };
    *nodes -= 1;
    let fields = fields
        .iter()
        .map(|&field| taken(known, field, nodes, leaves))
        .collect();
    Some(Shape {
        ctor: *ctor,
        fields,
    })
}

/// The types of the leaves of `shape`, in order.
fn leaf_types(program: &Program, shape: &Shape, types: &mut Vec<TypeId>) {
    for (at, field) in shape.fields.iter().enumerate() {
        match field {
            Some(inner) => leaf_types(program, inner, types),
            None => types.push(program.fields(shape.ctor)[at]),
        }
    }
}

/// `shape` built in `scope` of its leaves, the parameters from `next` on.
fn built(program: &mut Program, shape: &Shape, next: &mut usize, scope: &mut Scope) -> Atom {
    let fields: Vec<Atom> = shape
        .fields
        .iter()
        .map(|field| {
            if let Some(inner) = field {
                built(program, inner, next, scope)
            } else {
                *next += 1;
                Atom(Local::at(*next - 1))
            }
        })
        .collect();
    let fields = program.terms.hold_atoms(fields.into_iter());
    copy::push(program, scope, Expr::Con(shape.ctor, fields))
}

/// How many matches between two or more arms `body` holds.
fn branches(program: &Program, body: Body) -> usize {
    super::walk::within(program, body)
        .filter(|&expr| matches!(program.expr(expr), Expr::Match(_, arms) if arms.len() > 1))
        .count()
}
