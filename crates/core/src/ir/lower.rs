//! Lowering barb into the machine tier.
//!
//! This is where a value stops being a term and becomes storage, which is
//! this tier's job rather than barb's or a target's. The rules so far:
//!
//! - a spine-shaped type whose elements carry nothing is an unbounded
//!   natural. Proven bounds can select a fixed width; unknown bounds cannot.
//!   `Zero` is nought, `Succ(n)` is `n + 1`, and a match tests for nought.
//! - a type with no constructors has no values, so a term answering one
//!   does not answer: what it does is laid out, and nothing after it is.
//! - a type with one value says nothing by being itself, so it is not held:
//!   nothing is passed, nothing is tested, and its one arm runs.
//! - a one-constructor, one-field product has the representation of its field;
//!   construction and projection add no machine operation. This is asked
//!   before anything asks whether a value is held as a cell, since a wrapper
//!   around a product is held as that product.
//! - a product -- one constructor, several fields -- is held flat: as the
//!   values its fields are held as, end to end, with no object of its own.
//!   Constructing one allocates nothing and taking it apart reads nothing.
//!   Whether it fits a target's registers is the target's question, answered
//!   by [`super::fit`]. A product on a cycle made only of products has no
//!   values, and one with more than [`FLAT_LEAVES`] leaves is a cell: a
//!   value that large is cheaper shared than copied.
//! - a sequence -- a two-constructor sum whose step holds one element and
//!   the rest of itself -- is a buffer and a length, held flat like a
//!   product of two leaves. The sequence is the buffer's last `len`
//!   elements, so its rest is the same buffer one shorter: taking a sequence
//!   apart builds nothing, and adding to one writes in place where nothing
//!   else holds the buffer. A definition recognized as its length is never
//!   emitted; a call to one reads the length leaf.
//! - everything else with fields is a managed cell.
//! - a cell's fields are held at the class the cell says, which is the class
//!   a projection reads them back at. A field held flat is its leaves, laid
//!   inline among the cell's own fields.
//!
//! Nothing here recognises a routine by name. What a call to something
//! outside hands over is read off that routine's contract, so a byte string
//! becoming an address and a length is one entry in [`crate::platform::Takes`]
//! rather than a rule about one routine.
//!
//! Targets without arbitrary-precision support reject that class explicitly.

use std::rc::Rc;

use crate::barb;
use crate::index::append_range;

use super::model::{Binary, Class, FunctionId, Relation, ValueId};
use super::program::Program;
use super::validate::validate;
use crate::platform::{Built, Returns, Routine, Routines, Takes, reads, takes as takes_sentence};

#[cfg(test)]
mod tests;

/// Lower a whole program, or say what it holds that this tier cannot yet
/// represent.
///
/// Ranges are worked out here, from what the program says and what the
/// target says of values from outside it: what its routines answer and what
/// it hands the entry. Barb knows no target, so how wide anything is held is
/// decided here, and the program's own facts are left as they were.
///
/// # Errors
///
/// Names a program with no entry, which has nothing to run, and the first
/// type whose representation is not decided.
pub fn lower(program: &mut barb::Program, routines: &Routines) -> Result<Program, String> {
    lower_with(program, routines, Arguments::Made)
}

/// The same, where the program is known to read only how many arguments it
/// was handed: the list is never made, and nothing of it is left to hold.
///
/// # Errors
/// As [`lower`].
pub fn lower_counting_arguments(
    program: &mut barb::Program,
    routines: &Routines,
) -> Result<Program, String> {
    lower_with(program, routines, Arguments::Counted)
}

/// The name of the routine making the arguments a list, which a caller may
/// look for to learn whether anything still reads the list.
pub const MAKE_ARGUMENTS: &str = "host.arguments";

/// What the entry does with the arguments it is handed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Arguments {
    /// Makes them the list of strings the program holds.
    Made,
    /// Counts them, and holds an empty list the program never reads.
    Counted,
}

fn lower_with(
    program: &mut barb::Program,
    routines: &Routines,
    wanted: Arguments,
) -> Result<Program, String> {
    barb::validate(program)?;
    let assumed = assumed(program, routines);
    let facts = &program.assuming(&assumed);
    let program = &*program;
    let entry = program
        .entry()
        .ok_or("a program with no entry has nothing to run")?;
    // Only values actually lowered need a representation. Merely declaring
    // a library type (or retaining an old expression in the arena) does not.
    let demand = Demand::discover(program, facts, routines, entry)?;
    let (entry_params, arguments) = entry_parameters(&demand, entry, routines, wanted)?;
    let borrowed: Vec<_> = entry_params
        .iter()
        .map(|(name, class)| (name.as_str(), *class))
        .collect();
    let (mut machine, main) =
        Program::new_with_params(program.name(program.function(entry).name), &borrowed);
    let callees = declare(&demand, routines, &mut machine, (entry, main))?;

    let lowering = Lowering {
        barb: program,
        facts,
        carries: demand.carries,
        leaves: demand.leaves,
        takes: demand.takes,
        callees,
        refused: std::cell::RefCell::default(),
        looping: std::cell::RefCell::default(),
        arguments: arguments.map(|at| {
            let made =
                (wanted == Arguments::Made).then(|| making_arguments(&mut machine, routines));
            (at, made)
        }),
    };
    for (at, callee) in lowering.callees.iter().enumerate() {
        let id = barb::FnId::at(at);
        if matches!(callee, Callee::Function(_)) && program.function(id).body().is_some() {
            lowering.function(&mut machine, id)?;
        }
    }
    validate(&machine)?;
    Ok(machine)
}

/// Parameters by name and class, in order.
type NamedParams = Vec<(String, Class)>;

/// The entry's parameters as a machine hands them over, and where among them
/// the arguments are, where the entry reads them. The arguments come as C
/// lays them out, a count and where their addresses lie, and are made a list
/// of strings where the entry begins; only a program reading the list is
/// handed where it lies. Each is held as the target's startup table says.
fn entry_parameters(
    demand: &Demand<'_>,
    entry: barb::FnId,
    routines: &Routines,
    wanted: Arguments,
) -> Result<(NamedParams, Option<usize>), String> {
    let mut params = demand.named_params(entry);
    let arguments = params.windows(2).position(|pair| {
        pair == [
            ("args.0".to_owned(), Class::Buffer),
            ("args.1".to_owned(), Class::Word),
        ]
    });
    if let Some(at) = arguments {
        let handed: &[&str] = match wanted {
            Arguments::Made => &["argc", "argv"],
            Arguments::Counted => &["argc"],
        };
        let handed = handed
            .iter()
            .map(|&name| {
                routines
                    .startup(name)
                    .map(|value| (name.to_owned(), value.class))
                    .ok_or_else(|| format!("the target hands the entry no `{name}`"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        params.splice(at..at + 2, handed);
    }
    Ok((params, arguments))
}

/// The routine making the arguments a list of strings, which does nothing
/// else, so a call of it nothing reads goes.
fn making_arguments(machine: &mut Program, routines: &Routines) -> FunctionId {
    let word = u64::from(routines.word().unwrap_or(64) / 8);
    let made = machine.declare(
        MAKE_ARGUMENTS,
        &[Class::Word, Class::Address],
        &SEQUENCE_LEAVES,
    );
    machine.define(made, |b, args| {
        let list = Lowering::arguments(b, (args[0], args[1]), word);
        b.ret(&list);
    });
    machine.mark_inert(made);
    made
}

/// One entry per source function; no fabricated IDs for non-functions.
#[derive(Clone)]
enum Callee<'a> {
    Unreachable,
    Instruction(barb::Operation),
    /// Answered from how the sequence it is handed is held.
    Sequence(barb::SequenceOperation),
    Function(FunctionId),
    External {
        id: FunctionId,
        routine: &'a Routine,
        /// What each argument it is handed becomes, after erasure.
        handed: Vec<Handed>,
    },
    /// A routine built here, on a primitive or on memory alone.
    Built {
        built: &'a Built,
        primitive: Option<FunctionId>,
        io: Io,
    },
}

/// What every built routine shares: where a run of bytes is copied, for a
/// primitive to read or write where it lies, and the last error met.
#[derive(Clone, Copy)]
struct Io {
    scratch: super::DataId,
    failure: super::DataId,
    /// The greatest word, from whose top an error is counted down.
    top: u64,
}

/// How many bytes move in one run. Its room is in every image that moves
/// any, so it is small.
const SCRATCH: usize = 256;

/// The longest known byte string pushed one byte at a time; a longer one is
/// pushed by a loop over its bytes in data.
const UNROLLED: usize = 4;

/// What one argument of a call to something outside becomes.
///
/// A byte string is not one machine value, so what a routine is handed is
/// not always what a program wrote. This is read from the routine's
/// contract, so a second routine taking a string needs nothing added here.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Handed {
    Value(Class),
    Bytes,
}

/// What a call hands over, for saying so beside what a routine reads.
fn handed_sentence(handed: &[Handed]) -> String {
    if handed.is_empty() {
        return "nothing".to_owned();
    }
    handed
        .iter()
        .map(|handed| match handed {
            Handed::Bytes => "a byte string".to_owned(),
            Handed::Value(class) => reads(std::slice::from_ref(class)),
        })
        .collect::<Vec<_>>()
        .join(" and ")
}

#[expect(
    clippy::too_many_lines,
    reason = "one dispatch over demanded declarations and their contracts"
)]
fn declare<'a>(
    demand: &Demand<'_>,
    routines: &'a Routines,
    machine: &mut Program,
    (entry, main): (barb::FnId, FunctionId),
) -> Result<Vec<Callee<'a>>, String> {
    let (program, facts) = (demand.program, demand.facts);
    let mut callees = Vec::with_capacity(program.functions().len());
    let mut io = None;
    for (at, reached) in demand.reached.iter().enumerate() {
        let id = barb::FnId::at(at);
        if id == entry {
            callees.push(Callee::Function(main));
            continue;
        }
        // A definition the tier below has an instruction for is never
        // emitted: its callers write the instruction instead. Neither is one
        // nothing reaches, which has no callers to write anything.
        if !reached {
            callees.push(Callee::Unreachable);
            continue;
        }
        if let Some(operation) = facts.operation(id) {
            callees.push(Callee::Instruction(operation));
            continue;
        }
        if let Some(operation) = facts.sequence_operation(id) {
            callees.push(Callee::Sequence(operation));
            continue;
        }
        let function = program.function(id);
        let name = program.name(function.name);
        let (_, returns) = demand.signature(id);
        let named = demand.named_params(id);
        let named: Vec<_> = named
            .iter()
            .map(|(name, class)| (name.as_str(), *class))
            .collect();
        // External functions carry the provider's machine contract. They
        // share function IDs and calls with bodies, not the narrowing policy.
        callees.push(match function.definition {
            barb::Definition::Body(_) => {
                Callee::Function(if uninhabited(program, function.result) {
                    machine.declare_never_named(name, &named)
                } else {
                    machine.declare_named(name, &named, &returns)
                })
            }
            barb::Definition::External { symbol, .. } => {
                // A provider may answer for several source declarations.
                let outside = program.name(symbol);
                let Some(wanted) = routines.get(outside) else {
                    return Err(format!("nothing answers for `{name}`"));
                };
                let handed = demand.handed(id, wanted)?;
                provided(wanted, &handed, &returns)?;
                if wanted.comes_back() == uninhabited(program, function.result) {
                    return Err(format!(
                        "`{outside}` disagrees with `{name}` about returning"
                    ));
                }
                if let Some(built) = &wanted.built {
                    let primitive = match built {
                        Built::Put(through) | Built::Take(through) => {
                            let Some(primitive) = routines.get(through) else {
                                return Err(format!(
                                    "nothing answers for `{through}`, which `{outside}` is built on"
                                ));
                            };
                            Some(primitive.declare(machine))
                        }
                        Built::Taken | Built::Failure => None,
                    };
                    let io = *io.get_or_insert_with(|| {
                        let bits = routines.word().unwrap_or(64);
                        Io {
                            scratch: machine.global(&[0; SCRATCH]),
                            failure: machine.global(&[0; 8]),
                            top: u64::MAX >> (64 - bits),
                        }
                    });
                    callees.push(Callee::Built {
                        built,
                        primitive,
                        io,
                    });
                    continue;
                }
                let taken = demand.handed_names(id, wanted);
                let borrowed: Vec<_> = taken.iter().map(String::as_str).collect();
                Callee::External {
                    id: wanted.declare_named(machine, &borrowed),
                    routine: wanted,
                    handed,
                }
            }
        });
    }
    Ok(callees)
}

/// The routine answering for a name nothing defines, checked against what
/// that name means.
///
/// What a routine reads is what it is handed, and a value of a type that
/// carries nothing is not handed over at all. So a status that carries
/// nothing is no status, and saying so here beats three targets reading
/// past the end of their arguments.
fn provided(wanted: &Routine, handed: &[Handed], returns: &[Class]) -> Result<(), String> {
    let held = wanted.name.as_str();
    // Unlike internal range-proven narrowing, a host signature is not a
    // proof that its argument fits. In particular runtime Natural support
    // must never turn an implicit effect argument into modulo-word Convert.
    for (actual, &expected) in handed.iter().zip(&wanted.takes) {
        match (actual, expected) {
            (Handed::Bytes, Takes::StaticBytes | Takes::Bytes) => {}
            (Handed::Value(actual), Takes::Scalar(expected)) if actual.fits(expected) => {}
            (Handed::Value(actual), Takes::Scalar(expected)) => {
                return Err(format!(
                    "`{held}` requires {expected:?}, but its argument needs {actual:?}; host arguments must be proven to fit"
                ));
            }
            (actual, expected) => {
                return Err(format!(
                    "`{held}` reads {}, and is handed {}",
                    takes_sentence(std::slice::from_ref(&expected)),
                    handed_sentence(std::slice::from_ref(actual)),
                ));
            }
        }
    }
    let answers: Vec<Class> = match wanted.returns {
        Returns::Bytes => SEQUENCE_LEAVES.to_vec(),
        _ => wanted.answers().into_iter().collect(),
    };
    if returns.len() != answers.len() {
        return Err(format!(
            "`{held}` answers {}, and what is taken back is {}",
            reads(&answers),
            reads(returns),
        ));
    }
    Ok(())
}

/// The most leaves a product is held flat in. Past this a product is a
/// cell: copying it at every call would cost more than sharing it.
const FLAT_LEAVES: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Storage {
    Undemanded,
    Erased,
    Scalar,
    Cell,
    /// A product held as its leaves: a run in the leaf pool, never empty.
    Flat(barb::Range),
    /// A sequence: a buffer and a length, as [`SEQUENCE_LEAVES`] says.
    Seq,
}

/// The leaves every sequence is held as, which open every leaf pool.
const SEQUENCE_LEAVES: [Class; 2] = [Class::Buffer, Class::Word];

/// The run [`SEQUENCE_LEAVES`] occupy.
fn sequence_run() -> barb::Range {
    barb::Range::of(0, SEQUENCE_LEAVES.len())
}

impl Storage {
    fn carried(self) -> bool {
        match self {
            Self::Scalar | Self::Cell | Self::Flat(_) | Self::Seq => true,
            Self::Erased => false,
            Self::Undemanded => panic!("a lowered type must have been demanded"),
        }
    }

    /// What a value is held as, given what the tier above proved about it.
    /// Only a scalar's class reads the bounds.
    fn held(self, bounds: barb::Bounds) -> Option<Carried> {
        match self {
            Self::Scalar => Some(Carried::One(width(bounds))),
            Self::Cell => Some(Carried::One(Class::Cell)),
            Self::Flat(leaves) => Some(Carried::Flat(leaves)),
            Self::Seq => Some(Carried::Flat(sequence_run())),
            Self::Erased => None,
            Self::Undemanded => panic!("a lowered type must have been demanded"),
        }
    }
}

/// What one source value is held in: one machine value at a class, or a
/// flat product's leaves, at the classes its run in the leaf pool says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Carried {
    One(Class),
    Flat(barb::Range),
}

/// The classes a value is held at, one per machine value.
fn classes<'a>(leaves: &'a [Class], carried: &'a Carried) -> &'a [Class] {
    match carried {
        Carried::One(class) => std::slice::from_ref(class),
        Carried::Flat(run) => &leaves[run.range()],
    }
}

/// The machine values holding one source value.
#[derive(Clone, Debug)]
enum Held {
    One(ValueId),
    /// A product's leaves, at the classes of its run in the leaf pool.
    Flat {
        leaves: barb::Range,
        values: Rc<[ValueId]>,
    },
}

impl Held {
    /// What `values` hold, where they are held as `carried` says.
    fn of(carried: Carried, values: &[ValueId]) -> Self {
        match carried {
            Carried::One(_) => Self::One(values[0]),
            Carried::Flat(leaves) => Self::Flat {
                leaves,
                values: values.into(),
            },
        }
    }

    fn values(&self) -> &[ValueId] {
        match self {
            Self::One(value) => std::slice::from_ref(value),
            Self::Flat { values, .. } => values,
        }
    }

    /// The one value a scalar or a cell is held in.
    ///
    /// # Panics
    /// If this is a product held flat, which nothing reads as one value.
    fn one(&self) -> ValueId {
        match self {
            Self::One(value) => *value,
            Self::Flat { .. } => panic!("a scalar or a cell, not a flat product"),
        }
    }

    fn carried(&self, b: &super::Builder) -> Carried {
        match self {
            Self::One(value) => Carried::One(b.class(*value)),
            Self::Flat { leaves, .. } => Carried::Flat(*leaves),
        }
    }
}

/// Function and representation demand follow the same paths as emission:
/// recognized definitions become instructions, impossible arms disappear,
/// and a body stops at its first binding that cannot return.
struct Demand<'a> {
    program: &'a barb::Program,
    facts: &'a barb::Facts,
    reached: Vec<bool>,
    waiting: Vec<barb::FnId>,
    /// Parameters whose values survive into the machine calling convention.
    takes: Vec<Vec<bool>>,
    // Every lowered introduction must demand its type first. Undemanded is
    // distinct from erased, so a missed visit cannot silently discard a value.
    carries: Vec<Storage>,
    /// Every flat product's leaf classes, one run per product type.
    leaves: Vec<Class>,
}

impl<'a> Demand<'a> {
    fn discover(
        program: &'a barb::Program,
        facts: &'a barb::Facts,
        routines: &Routines,
        entry: barb::FnId,
    ) -> Result<Self, String> {
        let mut demand = Self {
            program,
            facts,
            reached: vec![false; program.functions().len()],
            waiting: vec![entry],
            takes: read_before_walking(program, facts, routines),
            carries: vec![Storage::Undemanded; program.types().len()],
            leaves: SEQUENCE_LEAVES.to_vec(),
        };
        while let Some(id) = demand.waiting.pop() {
            if std::mem::replace(&mut demand.reached[id.index()], true) {
                continue;
            }
            let function = program.function(id);
            demand.type_(function.result)?;
            if !facts.answered(id)
                && let Some(body) = function.body()
            {
                demand.body(body)?;
            }
        }
        demand.discover_parameters();
        demand.represent_parameters()?;
        Ok(demand)
    }

    fn represent_parameters(&mut self) -> Result<(), String> {
        for at in 0..self.program.functions().len() {
            if !self.reached[at] {
                continue;
            }
            let id = barb::FnId::at(at);
            let types: Vec<_> = self
                .program
                .params(id)
                .iter()
                .zip(&self.takes[at])
                .filter_map(|(&ty, &used)| used.then_some(ty))
                .collect();
            for ty in types {
                self.type_(ty)?;
            }
        }
        Ok(())
    }

    fn discover_parameters(&mut self) {
        loop {
            let previous = self.takes.clone();
            let mut changed = false;
            for at in 0..self.program.functions().len() {
                let id = barb::FnId::at(at);
                if !self.reached[at] || self.facts.answered(id) {
                    continue;
                }
                let Some(body) = self.program.function(id).body() else {
                    continue;
                };
                let mut found = vec![false; self.program.params(id).len()];
                self.demanded_parameters(body, &previous, &mut found);
                for (held, found) in self.takes[at].iter_mut().zip(found) {
                    if found && !*held {
                        *held = true;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// A flat product parameter is one machine parameter per leaf. Each is
    /// named for the field it is held in where a definition named one, so a
    /// target can supply the entry's by name, and otherwise for the
    /// parameter and its place.
    fn named_params(&self, id: barb::FnId) -> Vec<(String, Class)> {
        let mut named = Vec::new();
        for (((name, ty), held), _) in self
            .program
            .parameter_names(id)
            .zip(self.program.params(id))
            .zip(self.facts.takes(id))
            .zip(&self.takes[id.index()])
            .filter(|(((_, ty), _), used)| **used && self.carries[ty.index()].carried())
        {
            let carried = self.carries[ty.index()]
                .held(*held)
                .expect("a carried parameter has a class");
            let leaves = leaf_names(self, *ty, carried, name);
            named.extend(
                leaves
                    .into_iter()
                    .zip(classes(&self.leaves, &carried).iter().copied()),
            );
        }
        named
    }

    /// What each argument a call to something outside hands over, after
    /// erasure.
    ///
    /// What a byte string becomes is read off the routine's contract rather
    /// than off the type, because the same run of bytes is a managed value
    /// where a program holds one and an address and a length where
    /// something outside reads one.
    /// What one carried argument is, for saying so where a routine reads
    /// something else. A managed value is the only thing a byte string can
    /// be, so it is named as one here.
    fn carried_sentence(&self, carried: &[(&barb::TypeId, &barb::Bounds)]) -> String {
        if carried.is_empty() {
            return "nothing".to_owned();
        }
        carried
            .iter()
            .map(
                |(ty, bounds)| match self.carries[ty.index()].held(**bounds) {
                    Some(Carried::One(Class::Cell)) => handed_sentence(&[Handed::Bytes]),
                    Some(Carried::One(class)) => handed_sentence(&[Handed::Value(class)]),
                    Some(Carried::Flat(_)) if self.carries[ty.index()] == Storage::Seq => {
                        handed_sentence(&[Handed::Bytes])
                    }
                    Some(Carried::Flat(_)) => "a product".to_owned(),
                    None => unreachable!("an argument handed over is carried"),
                },
            )
            .collect::<Vec<_>>()
            .join(" and ")
    }

    /// The parameters of a declaration a routine reads: past the authority
    /// it is asked with, and carrying something.
    fn read_by(
        &self,
        id: barb::FnId,
        wanted: &Routine,
    ) -> Result<Vec<(&barb::TypeId, &barb::Bounds)>, String> {
        let asked = authority(wanted);
        if self.program.params(id).len() < asked {
            return Err(format!(
                "`{}` is asked with authority, and a declaration of it takes none",
                wanted.name
            ));
        }
        Ok(self
            .program
            .params(id)
            .iter()
            .zip(self.facts.takes(id))
            .skip(asked)
            .filter(|(ty, _)| self.carries[ty.index()] != Storage::Erased)
            .collect())
    }

    fn handed(&self, id: barb::FnId, wanted: &Routine) -> Result<Vec<Handed>, String> {
        let held = wanted.name.as_str();
        let carried = self.read_by(id, wanted)?;
        // What is handed over is converted to what the routine reads, so
        // what has to agree is how many of them: a value of a type carrying
        // nothing is not handed over at all, and then there is no value
        // where one is read. An argument is counted once here even where a
        // machine reads it as two, which a byte string is.
        if carried.len() != wanted.takes.len() {
            return Err(format!(
                "`{held}` reads {}, and is handed {}",
                takes_sentence(&wanted.takes),
                self.carried_sentence(&carried),
            ));
        }
        carried
            .into_iter()
            .zip(&wanted.takes)
            .map(|((ty, bounds), takes)| match takes {
                Takes::StaticBytes | Takes::Bytes => {
                    if byte_shaped(self.program, *ty) {
                        Ok(Handed::Bytes)
                    } else {
                        Err(format!(
                            "`{held}` reads a byte string, and `{}` is not one",
                            self.program.name(self.program.type_(*ty).name)
                        ))
                    }
                }
                Takes::Scalar(_) => match self.carries[ty.index()].held(*bounds) {
                    Some(Carried::One(class)) => Ok(Handed::Value(class)),
                    _ => Err(format!(
                        "`{held}` reads {}, and `{}` is a product",
                        takes_sentence(std::slice::from_ref(takes)),
                        self.program.name(self.program.type_(*ty).name)
                    )),
                },
            })
            .collect()
    }

    /// One diagnostic name per handed argument, in the same order.
    fn handed_names(&self, id: barb::FnId, wanted: &Routine) -> Vec<String> {
        self.program
            .parameter_names(id)
            .zip(self.program.params(id))
            .skip(authority(wanted))
            .filter(|(_, ty)| self.carries[ty.index()] != Storage::Erased)
            .map(|(name, _)| name.to_owned())
            .collect()
    }

    /// Erased and unused parameters take no machine slot; a flat product
    /// takes one per leaf.
    fn signature(&self, id: barb::FnId) -> (Vec<Class>, Vec<Class>) {
        let mut params = Vec::new();
        for ((ty, held), _) in self
            .program
            .params(id)
            .iter()
            .zip(self.facts.takes(id))
            .zip(&self.takes[id.index()])
            .filter(|((ty, _), used)| **used && self.carries[ty.index()].carried())
        {
            let carried = self.carries[ty.index()]
                .held(*held)
                .expect("a carried parameter has a class");
            params.extend_from_slice(classes(&self.leaves, &carried));
        }
        let result = self.program.function(id).result;
        let returns = self.carries[result.index()]
            .held(self.facts.answers(id))
            .map_or_else(Vec::new, |carried| classes(&self.leaves, &carried).to_vec());
        (params, returns)
    }

    fn type_(&mut self, ty: barb::TypeId) -> Result<(), String> {
        if self.carries[ty.index()] != Storage::Undemanded {
            return Ok(());
        }
        let storage = represent(self.program, ty)?;
        // Held as a cell until it is known to be held flat, which is also
        // what a cycle back to it through a sum reads meanwhile. A sum's
        // fields are read when it is lowered, not here, so that reading is
        // never kept.
        self.carries[ty.index()] = storage;
        if storage == Storage::Cell
            && let Some(product) = flattened(self.program, ty)
            && let Some(flat) = self.flatten(ty, product)?
        {
            self.carries[ty.index()] = flat;
            return Ok(());
        }
        if matches!(storage, Storage::Cell | Storage::Seq) {
            return self.type_fields(ty);
        }
        Ok(())
    }

    /// How a product is held once its fields are demanded: flat where its
    /// leaves fit, erased where there are none, and `None` to keep it a
    /// cell. A wrapper around a product is held as that product, with the
    /// same run of leaves, so the two are never told apart.
    fn flatten(
        &mut self,
        ty: barb::TypeId,
        product: barb::TypeId,
    ) -> Result<Option<Storage>, String> {
        if product != ty {
            self.type_(product)?;
            let inner = self.carries[product.index()];
            return Ok(matches!(inner, Storage::Flat(_) | Storage::Erased).then_some(inner));
        }
        let barb::TypeShape::Product { constructor } = barb::type_shape(self.program, ty) else {
            unreachable!("a flattened type is a product");
        };
        let fields = self.program.fields(constructor).to_vec();
        for &field in &fields {
            self.type_(field)?;
        }
        let mut leaves = Vec::new();
        for at in 0..fields.len() {
            let carried = field_carried(self.program, self.facts, &self.carries, constructor, at);
            if let Some(carried) = carried {
                leaves.extend_from_slice(classes(&self.leaves, &carried));
            }
        }
        Ok((leaves.len() <= FLAT_LEAVES).then(|| {
            if leaves.is_empty() {
                Storage::Erased
            } else {
                Storage::Flat(append_range(&mut self.leaves, &leaves))
            }
        }))
    }

    /// Demand every field of every constructor, as a cell's.
    fn type_fields(&mut self, ty: barb::TypeId) -> Result<(), String> {
        let fields: Vec<_> = self
            .program
            .ctors(ty)
            .iter()
            .flat_map(|ctor| self.program.types_of(ctor.fields))
            .copied()
            .collect();
        for field in fields {
            self.type_(field)?;
        }
        Ok(())
    }

    /// Mark parameters read on paths that can actually execute.
    fn demanded_parameters(
        &self,
        body: barb::Body,
        takes: &[Vec<bool>],
        found: &mut [bool],
    ) -> bool {
        for &expr in self
            .program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
        {
            match self.program.expr(expr) {
                barb::Expr::Atom(atom) => mark_parameter(atom, found),
                barb::Expr::Static(_) => {}
                barb::Expr::Con(_, args) => {
                    for &atom in self.program.atoms(args) {
                        mark_parameter(atom, found);
                    }
                }
                barb::Expr::Call(called, args) => {
                    for (&atom, &needed) in
                        self.program.atoms(args).iter().zip(&takes[called.index()])
                    {
                        if needed {
                            mark_parameter(atom, found);
                        }
                    }
                    if uninhabited(self.program, self.program.function(called).result) {
                        return false;
                    }
                }
                barb::Expr::Match(scrutinee, arms) => {
                    mark_parameter(scrutinee, found);
                    let mut returns = false;
                    for arm in reachable(self.program, arms, self.facts.matched(expr)) {
                        returns |= self.demanded_parameters(arm.body, takes, found);
                    }
                    if !returns {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether this body can return, matching `Lowering::body`.
    fn body(&mut self, body: barb::Body) -> Result<bool, String> {
        for &expr in self
            .program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
        {
            if !self.expr(expr)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn expr(&mut self, expr: barb::ExprId) -> Result<bool, String> {
        match self.program.expr(expr) {
            barb::Expr::Atom(_) => {}
            barb::Expr::Static(value) => self.type_(self.program.constant(value).owner())?,
            barb::Expr::Con(ctor, _) => self.type_(self.program.ctor(ctor).owner)?,
            barb::Expr::Call(id, _) => {
                self.waiting.push(id);
                return Ok(!uninhabited(self.program, self.program.function(id).result));
            }
            barb::Expr::Match(_, arms) => {
                let mut returns = false;
                for arm in reachable(self.program, arms, self.facts.matched(expr)) {
                    for &ty in self.program.fields(arm.ctor) {
                        self.type_(ty)?;
                    }
                    // Visit every reachable arm, even after one can return.
                    returns |= self.body(arm.body)?;
                }
                return Ok(returns);
            }
        }
        Ok(true)
    }
}

fn mark_parameter(atom: barb::Atom, found: &mut [bool]) {
    if let Some(used) = found.get_mut(atom.0.index()) {
        *used = true;
    }
}

/// Shared by demand discovery, answer analysis, and emission: types in an
/// impossible arm do not need storage any more than its calls need code.
fn reachable(
    program: &barb::Program,
    arms: barb::Range,
    bounds: barb::Bounds,
) -> impl Iterator<Item = barb::Arm> + '_ {
    program.arms(arms).iter().copied().filter(move |arm| {
        match barb::type_shape(program, program.ctor(arm.ctor).owner) {
            barb::TypeShape::Natural { empty, .. } if arm.ctor == empty => bounds.low == 0,
            barb::TypeShape::Natural { .. } => bounds.high != Some(0),
            // What the tier above found a value's constructor can be, the
            // same for a sum whose constructors carry something as for one
            // whose do not: an arm for one it cannot be is never taken, and
            // what that arm would work out, nothing there knows.
            barb::TypeShape::Enumeration | barb::TypeShape::Sum => {
                let tag = u64::from(program.tag(arm.ctor));
                tag >= bounds.low && bounds.high.is_none_or(|high| tag <= high)
            }
            barb::TypeShape::Uninhabited
            | barb::TypeShape::Unit { .. }
            | barb::TypeShape::Wrapper { .. }
            | barb::TypeShape::Product { .. }
            | barb::TypeShape::Sequence { .. }
            | barb::TypeShape::Spine { .. } => true,
        }
    })
}

/// The class a type's values take. Numbers and tags are decided so far.
fn represent(program: &barb::Program, id: barb::TypeId) -> Result<Storage, String> {
    let name = program.name(program.type_(id).name);
    let mut represented = id;
    for _ in 0..program.types().len() {
        match barb::type_shape(program, represented) {
            barb::TypeShape::Uninhabited | barb::TypeShape::Unit { .. } => {
                return Ok(Storage::Erased);
            }
            barb::TypeShape::Enumeration => return Ok(Storage::Scalar),
            barb::TypeShape::Wrapper { field, .. } => represented = field,
            barb::TypeShape::Natural { .. } => {
                // A number takes a place. How wide is not a question about the
                // type -- every natural has the same type and they are not all
                // the same size -- so it is asked of each value.
                return Ok(Storage::Scalar);
            }
            // A sequence is a buffer and how many of its elements it holds.
            barb::TypeShape::Sequence { .. } => return Ok(Storage::Seq),
            barb::TypeShape::Spine { .. }
            | barb::TypeShape::Product { .. }
            | barb::TypeShape::Sum => {
                return Ok(Storage::Cell);
            }
        }
    }
    Err(format!("`{name}` has a cyclic transparent representation"))
}

/// The product a type is held flat as, if it is one: read through wrappers,
/// and refused where the product reaches itself through products alone,
/// which no value does in a total program and no finite run could hold.
fn flattened(program: &barb::Program, id: barb::TypeId) -> Option<barb::TypeId> {
    let product = peeled(program, id)?;
    let barb::TypeShape::Product { constructor } = barb::type_shape(program, product) else {
        return None;
    };
    let mut seen = vec![false; program.types().len()];
    let mut waiting = program.fields(constructor).to_vec();
    while let Some(field) = waiting.pop() {
        let field = peeled(program, field)?;
        if field == product {
            return None;
        }
        if std::mem::replace(&mut seen[field.index()], true) {
            continue;
        }
        if let barb::TypeShape::Product { constructor } = barb::type_shape(program, field) {
            waiting.extend_from_slice(program.fields(constructor));
        }
    }
    Some(product)
}

/// What field `at` of `ctor` is held as, where it carries anything.
///
/// A number is as wide as every value built into that field, which is all a
/// reader of it can know. A tag nothing bounds is a word.
fn field_carried(
    program: &barb::Program,
    facts: &barb::Facts,
    carries: &[Storage],
    ctor: barb::CtorId,
    at: usize,
) -> Option<Carried> {
    let ty = program.fields(ctor)[at];
    let held = facts.field(program, ctor, at);
    match carries[ty.index()] {
        Storage::Cell => Some(Carried::One(Class::Cell)),
        Storage::Scalar if held.width().is_none() && tagged(program, ty) => {
            Some(Carried::One(Class::Word))
        }
        Storage::Scalar => Some(Carried::One(width(held))),
        Storage::Flat(run) => Some(Carried::Flat(run)),
        Storage::Seq => Some(Carried::Flat(sequence_run())),
        Storage::Erased => None,
        Storage::Undemanded => panic!("a bound field type must have been demanded"),
    }
}

/// Which parameters are read before any body is walked: every one of a
/// declaration something outside answers or an equation recognized as an
/// operation, but for the authority a routine is asked with, which is handed
/// over and not read.
fn read_before_walking(
    program: &barb::Program,
    facts: &barb::Facts,
    routines: &Routines,
) -> Vec<Vec<bool>> {
    program
        .functions()
        .iter()
        .enumerate()
        .map(|(at, function)| {
            let id = barb::FnId::at(at);
            let mut takes =
                vec![function.body().is_none() || facts.answered(id); program.params(id).len()];
            if let Some(first) = takes.first_mut()
                && asks_with_authority(program, routines, function)
            {
                *first = false;
            }
            takes
        })
        .collect()
}

/// How many of a declaration's first parameters a routine takes as the
/// authority it is asked with, rather than reads: one or none.
const fn authority(routine: &Routine) -> usize {
    if routine.authority { 1 } else { 0 }
}

/// Whether a declaration with no body is answered by a routine asked with
/// authority.
fn asks_with_authority(
    program: &barb::Program,
    routines: &Routines,
    function: &barb::Function,
) -> bool {
    function
        .provider()
        .and_then(|provider| routines.get(program.name(provider)))
        .is_some_and(|routine| routine.authority)
}

/// What the target says of values from outside the program: what each
/// routine it answers for answers, and what it hands the entry.
fn assumed(program: &barb::Program, routines: &Routines) -> barb::Assumed {
    let mut assumed = barb::Assumed::default();
    for (at, function) in program.functions().iter().enumerate() {
        if let Some(provider) = function.provider()
            && let Some(bounds) = routines
                .get(program.name(provider))
                .and_then(Routine::bounds)
        {
            assumed.results.push((barb::FnId::at(at), bounds));
        }
        if let Some(provider) = function.provider()
            && routines
                .get(program.name(provider))
                .is_some_and(|routine| routine.returns == Returns::Bytes)
            && let Some(places) = byte_places(program, function.result)
        {
            // Every byte a routine answers is one, and a byte type's values
            // are bytes wherever they were built.
            let byte = barb::Bounds {
                low: 0,
                high: Some(255),
            };
            for (constructor, at) in places {
                assumed.fields.push((constructor, at, byte));
            }
        }
    }
    if let Some(entry) = program.entry() {
        handed(program, routines, entry, &mut assumed);
    }
    assumed.length = Some(routines.length());
    assumed
}

/// A startup value is named, as a parameter of the entry or a field of a
/// type the entry is handed, through wrappers and products, and holds what
/// the target's startup table says.
fn handed(
    program: &barb::Program,
    routines: &Routines,
    entry: barb::FnId,
    assumed: &mut barb::Assumed,
) {
    let startup = |name: &str, ty| startup(program, routines, name, ty);
    let mut waiting = Vec::new();
    for (at, (name, &ty)) in program
        .parameter_names(entry)
        .zip(program.params(entry))
        .enumerate()
    {
        if let Some(bounds) = startup(name, ty) {
            assumed.parameters.push((at, bounds));
        }
        waiting.push(ty);
    }
    let mut seen = vec![false; program.types().len()];
    while let Some(ty) = waiting.pop() {
        if std::mem::replace(&mut seen[ty.index()], true) {
            continue;
        }
        let (barb::TypeShape::Wrapper { constructor, .. }
        | barb::TypeShape::Product { constructor }) = barb::type_shape(program, ty)
        else {
            continue;
        };
        for (at, &field) in program.fields(constructor).iter().enumerate() {
            if let Some(bounds) = program
                .field_name(constructor, at)
                .and_then(|name| startup(name, field))
            {
                assumed.fields.push((constructor, at, bounds));
            }
            if program.field_name(constructor, at) == Some("args") {
                assume_argument_bytes(program, field, assumed);
            }
            waiting.push(field);
        }
    }
}

/// The arguments are strings of bytes the target handed over, so their
/// bytes are bytes.
fn assume_argument_bytes(
    program: &barb::Program,
    field: barb::TypeId,
    assumed: &mut barb::Assumed,
) {
    if let barb::TypeShape::Sequence { element, .. } = barb::type_shape(program, field)
        && let Some(places) = byte_places(program, element)
    {
        let byte = barb::Bounds {
            low: 0,
            high: Some(255),
        };
        for (constructor, at) in places {
            assumed.fields.push((constructor, at, byte));
        }
    }
}

/// What the startup value named `name` holds, where the target produces one
/// and `ty` is a number.
fn startup(
    program: &barb::Program,
    routines: &Routines,
    name: &str,
    ty: barb::TypeId,
) -> Option<barb::Bounds> {
    let natural = matches!(
        barb::type_shape(program, ty),
        barb::TypeShape::Natural { .. }
    );
    routines
        .startup(name)
        .filter(|_| natural)
        .map(crate::platform::Startup::bounds)
}

/// Each leaf's name, for a value of `ty` held as `carried`: the name of the
/// field it is held in, reading through wrappers and flat products, where a
/// definition named one, and `fallback` with its place where none did.
/// What a run of wrappers around `ty` holds, and the name the innermost
/// named field gives it, or `fallback` where none is named.
fn unwrapped(
    program: &barb::Program,
    mut ty: barb::TypeId,
    fallback: &str,
) -> (barb::TypeId, String) {
    let mut held_as = fallback.to_owned();
    for _ in 0..=program.types().len() {
        let barb::TypeShape::Wrapper { constructor, field } = barb::type_shape(program, ty) else {
            break;
        };
        if let Some(name) = program.field_name(constructor, 0) {
            name.clone_into(&mut held_as);
        }
        ty = field;
    }
    (ty, held_as)
}

fn leaf_names(
    demand: &Demand<'_>,
    ty: barb::TypeId,
    carried: Carried,
    fallback: &str,
) -> Vec<String> {
    let program = demand.program;
    let count = classes(&demand.leaves, &carried).len();
    let placed = |base: &str| (0..count).map(|at| format!("{base}.{at}")).collect();
    let (ty, held_as) = unwrapped(program, ty, fallback);
    let (Carried::Flat(_), barb::TypeShape::Product { constructor }) =
        (carried, barb::type_shape(program, ty))
    else {
        return if count == 1 {
            vec![held_as]
        } else {
            placed(&held_as)
        };
    };
    let mut found = Vec::with_capacity(count);
    for at in 0..program.fields(constructor).len() {
        let Some(inner) = field_carried(program, demand.facts, &demand.carries, constructor, at)
        else {
            continue;
        };
        let field = program
            .field_name(constructor, at)
            .map_or_else(|| format!("{held_as}.{at}"), str::to_owned);
        found.extend(leaf_names(
            demand,
            program.fields(constructor)[at],
            inner,
            &field,
        ));
    }
    if found.len() == count {
        found
    } else {
        placed(fallback)
    }
}

/// Whether a type's values are a run of bytes: a sequence whose element is
/// a number no wider than one. Wrappers are read through, since one adds
/// nothing to what a value is.
fn byte_shaped(program: &barb::Program, id: barb::TypeId) -> bool {
    let Some(id) = peeled(program, id) else {
        return false;
    };
    let barb::TypeShape::Sequence { element, .. } = barb::type_shape(program, id) else {
        return false;
    };
    peeled(program, element).is_some_and(|element| {
        matches!(
            barb::type_shape(program, element),
            barb::TypeShape::Natural { .. }
        )
    })
}

/// Where a byte string's bytes are held, where its element is a type of its
/// own around a number: that type's field, and the sequence's element field.
/// A value of a byte type is a byte wherever it was built, so saying so of
/// every one is saying nothing false.
fn byte_places(program: &barb::Program, id: barb::TypeId) -> Option<[(barb::CtorId, usize); 2]> {
    let barb::TypeShape::Sequence {
        element,
        push,
        recursive,
        ..
    } = barb::type_shape(program, peeled(program, id)?)
    else {
        return None;
    };
    let barb::TypeShape::Wrapper { constructor, field } = barb::type_shape(program, element) else {
        return None;
    };
    matches!(
        barb::type_shape(program, peeled(program, field)?),
        barb::TypeShape::Natural { .. }
    )
    .then_some([(constructor, 0), (push, usize::from(recursive == 0))])
}

/// Read through one-field products. Bounded by the declared types, so a
/// cycle ends the walk rather than running forever.
fn peeled(program: &barb::Program, mut id: barb::TypeId) -> Option<barb::TypeId> {
    for _ in 0..=program.types().len() {
        match barb::type_shape(program, id) {
            barb::TypeShape::Wrapper { field, .. } => id = field,
            _ => return Some(id),
        }
    }
    None
}

/// The narrowest class holding every value a term answers. A width is what
/// a value needs and not what it wraps at, so this narrows nothing: what a
/// target holds it in is whatever it has that is at least this wide.
///
/// Where nothing bounds the values, only an arbitrary-precision natural
/// preserves the semantics. A target may reject it, but may not wrap it.
fn width(held: barb::Bounds) -> Class {
    // Everything worked out above is carried, not just how wide it makes
    // the value: what a value can be is what says whether reading it at
    // another width takes anything off it. The singleton zero needs no
    // value bits and is still a scalar; physical storage and
    // calling-convention slots are target decisions.
    if held.width().is_some() {
        Class::Held(held)
    } else {
        Class::Natural
    }
}

/// A type with no constructors has no values, so nothing holds one and
/// nothing is passed. What is said to answer one does not answer.
fn uninhabited(program: &barb::Program, id: barb::TypeId) -> bool {
    barb::type_shape(program, id) == barb::TypeShape::Uninhabited
}

/// A type whose constructors all carry nothing says which one it is and
/// says nothing else, so a value of one is which: the tag, in a word.
/// `Bool` is such a type, and so is an ordering, and so is anything a
/// program writes as a run of bare names.
///
/// A single nullary constructor is erased rather than tagged: a value that
/// could not have been anything else says nothing by being itself.
fn tagged(program: &barb::Program, id: barb::TypeId) -> bool {
    barb::type_shape(program, id) == barb::TypeShape::Enumeration
}

/// What a term answers: a value, nothing because its type carries nothing,
/// or nothing ever because the term does not come back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Answer<T> {
    Value(T),
    Nothing,
    Never,
}

impl<T> From<Option<T>> for Answer<T> {
    /// What something that may hold a value answers. A type carrying nothing
    /// holds none, and that is `Nothing`: it is the term that says `Never`,
    /// not the storage.
    fn from(held: Option<T>) -> Self {
        held.map_or(Self::Nothing, Self::Value)
    }
}

impl<T> Answer<T> {
    /// The value, where there is one. `Nothing` and `Never` both hold none:
    /// what tells them apart is what a region does after them, not what it
    /// carries out.
    fn held(self) -> Option<T> {
        match self {
            Self::Value(value) => Some(value),
            Self::Nothing | Self::Never => None,
        }
    }

    /// Where two paths join. A path that does not come back says nothing
    /// about what the join carries, so the other one says it.
    fn or(self, other: Self) -> Self {
        match self {
            Self::Never => other,
            held => held,
        }
    }

    fn map<U>(self, held: impl FnOnce(T) -> U) -> Answer<U> {
        match self {
            Self::Value(value) => Answer::Value(held(value)),
            Self::Nothing => Answer::Nothing,
            Self::Never => Answer::Never,
        }
    }
}

/// A value at the width that reads it, where what reads it was worked
/// out from the same bounds the value was.
///
/// A class is what a term could need rather than what it does: a field
/// stepped down from a scrutinee is held at the scrutinee's width, while the
/// tier above may have proved it smaller. So narrowing here takes nothing
/// off, and what it narrows to is a width that tier chose.
///
/// Nothing like that holds where a width came from outside. A routine reads
/// what it reads whatever a program worked out, so a value not fitting one
/// is a program refused rather than a value quietly made to fit -- which is
/// what [`super::model::Op::Convert`] is for, a program asking.
fn met(b: &mut super::Builder, arg: ValueId, wanted: Class) -> ValueId {
    if b.class(arg).fits(wanted) {
        arg
    } else {
        b.convert(wanted, arg)
    }
}

/// Where two arms meet: what they leave with is one place, so it is as wide
/// as either of them needs. A flat product's leaves are held at the classes
/// its type says, so two arms answering one already agree.
fn widest(held: Answer<Carried>, other: Answer<Carried>) -> Answer<Carried> {
    match (held.held(), other.held()) {
        (Some(Carried::One(held)), Some(Carried::One(other))) => {
            Answer::Value(Carried::One(super::arithmetic::widest(held, other)))
        }
        (Some(flat @ Carried::Flat(_)), Some(Carried::Flat(_))) => Answer::Value(flat),
        (Some(_), Some(_)) => unreachable!("the arms of one match answer one type"),
        _ => held.or(other),
    }
}

/// A tagged arm and the join of this arm with all following arms.
struct TagArm {
    arm: barb::Arm,
    suffix: Answer<Carried>,
}

// Analyze each body once, then accumulate joins backward. Returning arms of a
// well-typed match agree on whether they carry a value, so widest is associative
// here. Keep the narrower suffix joins, not just the width of the whole match.
fn tag_plan(
    arms: impl Iterator<Item = barb::Arm>,
    mut answer: impl FnMut(barb::Body) -> Answer<Carried>,
) -> Vec<TagArm> {
    let mut planned: Vec<_> = arms
        .map(|arm| TagArm {
            suffix: answer(arm.body),
            arm,
        })
        .collect();
    let mut suffix = Answer::Never;
    for arm in planned.iter_mut().rev() {
        suffix = widest(arm.suffix, suffix);
        arm.suffix = suffix;
    }
    planned
}

/// Leave an arm with what its body answered. An arm that does not come back
/// never reaches the join, so it carries nothing there.
fn yielded(b: &mut super::Builder, answer: Answer<Held>, classes: &[Class]) {
    match answer {
        Answer::Value(held) => {
            let values: Vec<_> = held
                .values()
                .iter()
                .zip(classes)
                .map(|(&value, &class)| met(b, value, class))
                .collect();
            b.yield_(&values);
        }
        Answer::Nothing => b.yield_(&[]),
        Answer::Never => (),
    }
}

#[derive(Clone)]
enum ReturnTo {
    Entry,
    /// The classes a function answers at, one per machine value.
    Function(Vec<Class>),
}

/// The entry's implicit status is a host word, not a request for modulo.
fn returned(
    b: &mut super::Builder,
    answer: Answer<Held>,
    destination: &ReturnTo,
) -> Result<(), String> {
    match (answer, destination) {
        (Answer::Value(held), ReturnTo::Entry) => {
            let &[answer] = held.values() else {
                return Err(
                    "the entry's result is a product, but its exit status is one word".to_owned(),
                );
            };
            if b.class(answer) == Class::Natural {
                return Err(
                    "the entry's result is unbounded, but its exit status must fit a word"
                        .to_owned(),
                );
            }
            let answer = met(b, answer, Class::Word);
            b.ret(&[answer]);
        }
        (Answer::Value(held), ReturnTo::Function(classes)) => {
            let values: Vec<_> = held
                .values()
                .iter()
                .zip(classes)
                .map(|(&value, &class)| met(b, value, class))
                .collect();
            b.ret(&values);
        }
        (Answer::Nothing, ReturnTo::Entry) => {
            let status = b.constant(Class::Word, 0);
            b.ret(&[status]);
        }
        (Answer::Nothing, ReturnTo::Function(_)) => b.ret(&[]),
        (Answer::Never, _) => (),
    }
    Ok(())
}

struct Lowering<'a> {
    barb: &'a barb::Program,
    facts: &'a barb::Facts,
    /// Whether a value of each barb type takes a place, by type.
    carries: Vec<Storage>,
    /// Every flat product's leaf classes, one run per product type.
    leaves: Vec<Class>,
    /// Which source parameters survive into each machine signature.
    takes: Vec<Vec<bool>>,
    callees: Vec<Callee<'a>>,
    /// The first thing emission found it cannot lay out, read back once a
    /// body is built. Region callbacks answer values rather than results,
    /// so a refusal is kept here instead of returned from each of them.
    refused: std::cell::RefCell<Option<String>>,
    /// The function being lowered as a loop, and the calls of itself in
    /// tail position, each of which goes round again rather than calling.
    looping: std::cell::RefCell<Option<(barb::FnId, Vec<barb::ExprId>)>>,
    /// Where among the entry's parameters the arguments' count and array
    /// are, and the routine making the list of strings from them, where the
    /// program reads the list.
    arguments: Option<(usize, Option<FunctionId>)>,
}

/// Local values, one entry per source local: `None` where it carries nothing.
type Locals = [Option<Held>];

impl Lowering<'_> {
    /// What a term answers as. Two scalar values of one type may be held
    /// at different widths, while an aggregate keeps the representation
    /// selected for its source type.
    fn carried(&self, ty: barb::TypeId, bounds: barb::Bounds) -> Carried {
        self.carries[ty.index()]
            .held(bounds)
            .expect("a carried type has a class")
    }

    fn classes<'a>(&'a self, carried: &'a Carried) -> &'a [Class] {
        classes(&self.leaves, carried)
    }

    /// What a join carries out, one class per machine value.
    fn join(&self, answer: Answer<Carried>) -> Vec<Class> {
        answer
            .held()
            .map_or_else(Vec::new, |carried| self.classes(&carried).to_vec())
    }

    fn field_carried(&self, ctor: barb::CtorId, at: usize) -> Option<Carried> {
        field_carried(self.barb, self.facts, &self.carries, ctor, at)
    }

    /// What each field of `ctor` is held as, in order.
    fn fields_carried(&self, ctor: barb::CtorId) -> impl Iterator<Item = Option<Carried>> + '_ {
        (0..self.barb.fields(ctor).len()).map(move |at| self.field_carried(ctor, at))
    }

    fn width(&self, id: barb::ExprId) -> Class {
        width(self.facts.held(id))
    }

    fn function(&self, machine: &mut Program, id: barb::FnId) -> Result<(), String> {
        let body = self
            .barb
            .function(id)
            .body()
            .expect("a function with a body");
        let Callee::Function(into) = self.callees[id.index()] else {
            unreachable!("only machine functions have bodies to lower");
        };
        let entry = self.barb.entry() == Some(id);
        // What it leaves with: a word from the entry, whatever the program
        // worked in, and otherwise the width it was declared at.
        let destination = if entry {
            ReturnTo::Entry
        } else {
            let result = self.barb.function(id).result;
            ReturnTo::Function(
                self.carries[result.index()]
                    .held(self.facts.answers(id))
                    .map_or_else(Vec::new, |carried| self.classes(&carried).to_vec()),
            )
        };
        let tails = if entry {
            Vec::new()
        } else {
            self.tail_calls(id, body)
        };
        if tails.is_empty() {
            machine.try_define(into, |b, params| {
                let params = if entry {
                    self.arguments_made(b, params)
                } else {
                    params.to_vec()
                };
                let mut locals = self.parameters(id, &params);
                let mut statics = vec![None; locals.len()];
                let answer = self.body(b, body, &mut locals, &mut statics);
                returned(b, answer, &destination)
            })?;
        } else {
            self.looped(machine, (id, into), (body, tails), &destination)?;
        }
        // A body is built before this can be read: emission answers values,
        // and what it could not lay out is said once, here, where lowering
        // can still refuse the program.
        self.refused.borrow_mut().take().map_or(Ok(()), Err)
    }

    /// The entry's parameters, with the arguments' count and array made the
    /// list of strings the program holds.
    fn arguments_made(&self, b: &mut super::Builder, params: &[ValueId]) -> Vec<ValueId> {
        let Some((at, made)) = self.arguments else {
            return params.to_vec();
        };
        // How many there are is the count: a program that asks only that
        // reads no list, and the call making one goes.
        let (list, handed) = match made {
            Some(made) => (b.call(made, &[params[at], params[at + 1]])[0], 2),
            None => (b.buffer_empty(), 1),
        };
        let mut params = params.to_vec();
        params.splice(at..at + handed, [list, params[at]]);
        params
    }

    /// Each of `count` strings whose addresses lie from `array`, a word of
    /// `word` bytes each, as a sequence of byte strings: pushed from the
    /// last, each read up to the nought byte that ends it.
    fn arguments(
        b: &mut super::Builder,
        (count, array): (ValueId, ValueId),
        word: u64,
    ) -> [ValueId; 2] {
        let empty = b.buffer_empty();
        let none = b.constant(Class::Word, 0);
        let built = b.loop_(&[empty, none], &SEQUENCE_LEAVES, |b, state| {
            let (held, len) = (state[0], state[1]);
            let done = b.compare(Relation::Equal, len, count);
            b.if_(done, &[], |b| b.break_(&[held, len]), |b| b.yield_(&[]));
            let one = b.constant(Class::Word, 1);
            let rest = b.binary(Binary::Sub, count, len);
            let index = b.binary(Binary::Sub, rest, one);
            let width = b.constant(Class::Word, word);
            let offset = b.binary(Binary::Mul, index, width);
            let base = b.convert(Class::Word, array);
            let slot = b.binary(Binary::Add, base, offset);
            let slot = b.convert(Class::Address, slot);
            let start = b.load(super::Width::Word, slot, super::Offset::Words(0));
            let start = b.convert(Class::Address, start);
            let length = Self::terminated(b, start);
            let text = Self::pushed_bytes(b, start, length, Class::fixed(8));
            let longer = b.buffer_push(held, len, &text);
            let more = b.binary(Binary::Add, len, one);
            b.continue_(&[longer, more]);
        });
        [built[0], built[1]]
    }

    /// How many bytes lie from `start` before a nought one.
    fn terminated(b: &mut super::Builder, start: ValueId) -> ValueId {
        let none = b.constant(Class::Word, 0);
        b.loop_(&[none], &[Class::Word], |b, state| {
            let len = state[0];
            let base = b.convert(Class::Word, start);
            let place = b.binary(Binary::Add, base, len);
            let place = b.convert(Class::Address, place);
            let byte = b.load(super::Width::Byte, place, super::Offset::Bytes(0));
            let nought = b.constant(Class::Word, 0);
            let ended = b.compare(Relation::Equal, byte, nought);
            b.if_(ended, &[], |b| b.break_(&[len]), |b| b.yield_(&[]));
            let one = b.constant(Class::Word, 1);
            let more = b.binary(Binary::Add, len, one);
            b.continue_(&[more]);
        })[0]
    }

    /// A function calling itself in tail position, which goes round again
    /// instead: the body is a loop over the parameters, and it leaves by
    /// returning. However deep the recursion, the stack is one frame deep.
    fn looped(
        &self,
        machine: &mut Program,
        (id, into): (barb::FnId, FunctionId),
        (body, tails): (barb::Body, Vec<barb::ExprId>),
        destination: &ReturnTo,
    ) -> Result<(), String> {
        *self.looping.borrow_mut() = Some((id, tails));
        let defined = machine.try_define(into, |b, params| {
            let mut lowered = Ok(());
            b.loop_(params, &[], |b, state| {
                let mut locals = self.parameters(id, state);
                let mut statics = vec![None; locals.len()];
                let answer = self.body(b, body, &mut locals, &mut statics);
                lowered = returned(b, answer, destination);
            });
            lowered
        });
        self.looping.borrow_mut().take();
        defined
    }

    /// Whether `expr` is a call of the function being lowered as a loop, to
    /// itself in tail position, which goes round again.
    fn goes_round(&self, expr: barb::ExprId) -> bool {
        self.looping
            .borrow()
            .as_ref()
            .is_some_and(|(_, tails)| tails.contains(&expr))
    }

    /// The calls of `id` to itself in tail position: a body's tail, and
    /// the tails of each arm of a match there.
    fn tail_calls(&self, id: barb::FnId, body: barb::Body) -> Vec<barb::ExprId> {
        let mut found = Vec::new();
        let mut waiting = vec![body];
        while let Some(body) = waiting.pop() {
            match self.barb.expr(body.tail) {
                barb::Expr::Call(callee, _) if callee == id => found.push(body.tail),
                barb::Expr::Match(_, arms) => {
                    waiting.extend(self.barb.arms(arms).iter().map(|arm| arm.body));
                }
                _ => {}
            }
        }
        found
    }

    /// The source parameters, as the machine ones hold them. Erased and
    /// unused parameters take no machine slot and a flat product takes one
    /// per leaf; the rest match in order.
    fn parameters(&self, id: barb::FnId, params: &[ValueId]) -> Vec<Option<Held>> {
        let mut taken = params.iter().copied();
        self.barb
            .params(id)
            .iter()
            .zip(self.facts.takes(id))
            .zip(&self.takes[id.index()])
            .map(|((ty, bounds), used)| {
                (*used && self.carries[ty.index()].carried()).then(|| {
                    let carried = self.carried(*ty, *bounds);
                    let values: Vec<_> = self
                        .classes(&carried)
                        .iter()
                        .map(|_| taken.next().expect("a parameter"))
                        .collect();
                    Held::of(carried, &values)
                })
            })
            .collect()
    }

    /// Each binding takes the next local, then the tail answers.
    fn body(
        &self,
        b: &mut super::Builder,
        body: barb::Body,
        locals: &mut Vec<Option<Held>>,
        statics: &mut Vec<Option<barb::ConstId>>,
    ) -> Answer<Held> {
        for &binding in self.barb.bindings(body.bindings) {
            let static_value = self.propagate_static(binding, statics);
            match self.expr(b, binding, locals, statics) {
                Answer::Value(value) => locals.push(Some(value)),
                Answer::Nothing => locals.push(None),
                // A body leaves where its bindings do: nothing after this
                // one is reached, so nothing after it is lowered.
                Answer::Never => return Answer::Never,
            }
            statics.push(static_value);
        }
        self.expr(b, body.tail, locals, statics)
    }

    fn propagate_static(
        &self,
        expr: barb::ExprId,
        statics: &[Option<barb::ConstId>],
    ) -> Option<barb::ConstId> {
        match self.barb.expr(expr) {
            // Only a run of bytes is worth following: it is the one thing
            // something outside reads where it lies rather than as a value.
            barb::Expr::Static(value)
                if byte_shaped(self.barb, self.barb.constant(value).owner()) =>
            {
                Some(value)
            }
            barb::Expr::Atom(atom) => statics[atom.0.index()],
            _ => None,
        }
    }

    fn expr(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        match self.barb.expr(expr) {
            barb::Expr::Atom(atom) => locals[atom.0.index()].clone().into(),
            // A value the tier above worked out, as the word it lowers to:
            // which constructor for a tag, and what it counts to for a
            // number. One that carries nothing is nothing to carry.
            barb::Expr::Static(value) => {
                let value = self.barb.constant(value);
                let id = value.owner();
                if !self.carries[id.index()].carried() {
                    return Answer::Nothing;
                }
                let carried = self.carried(id, self.facts.held(expr));
                Answer::Value(self.static_held(b, carried, value))
            }
            barb::Expr::Con(ctor, args) => self.construct(b, expr, ctor, args, locals).into(),
            barb::Expr::Call(function, args) => self.call(b, expr, function, args, locals, statics),
            // A value of a type with one inhabitant says nothing by being
            // itself, so it is not held and there is nothing to test: the
            // one arm runs. Asking for a value here would refuse a match
            // that is already decided.
            barb::Expr::Match(scrutinee, arms) => self.branch(
                b,
                locals[scrutinee.0.index()].as_ref(),
                arms,
                locals,
                statics,
                self.facts.matched(expr),
            ),
        }
    }

    /// A known value, held as its type is.
    fn static_held(
        &self,
        b: &mut super::Builder,
        carried: Carried,
        value: barb::Constant<'_>,
    ) -> Held {
        match carried {
            Carried::One(class) => Held::One(self.static_value(b, class, value)),
            Carried::Flat(leaves) => {
                let mut values = Vec::new();
                self.static_leaves(b, value, &mut values);
                Held::Flat {
                    leaves,
                    values: values.into(),
                }
            }
        }
    }

    fn static_value(
        &self,
        b: &mut super::Builder,
        class: Class,
        value: barb::Constant<'_>,
    ) -> ValueId {
        let value = barb::single_field_constant(self.barb, value);
        match value.view() {
            barb::ConstantView::Constructor(ctor) if class == Class::Cell => {
                self.static_cell(b, ctor)
            }
            barb::ConstantView::Constructor(ctor) => {
                b.constant(class, u64::from(self.barb.tag(ctor.constructor())))
            }
            barb::ConstantView::Natural(number) => match number.try_u64() {
                Ok(held) => b.constant(class, held),
                Err(barb::TooWide) => b.natural(&number.to_biguint()),
            },
            // A sequence is held as two values and never reaches here; a
            // spine with wider steps is a cell nothing builds from bytes.
            barb::ConstantView::Spine(_) => {
                self.refuse(format!(
                    "`{}` is a known spine of wide steps, which this tier cannot lay out yet",
                    self.barb.name(self.barb.type_(value.owner()).name)
                ));
                b.constant(Class::Word, 0)
            }
        }
    }

    /// The fields of one known constructor, each as the values it is held
    /// in, end to end.
    fn static_fields(
        &self,
        b: &mut super::Builder,
        ctor: barb::ConstructorView<'_>,
        out: &mut Vec<ValueId>,
    ) {
        let mut budget = barb::Budget::new(barb::FoldLimits {
            work: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let values = ctor
            .fields(&mut budget)
            .expect("validated constants can be revisited");
        for (carried, value) in self.fields_carried(ctor.constructor()).zip(values) {
            match carried {
                Some(Carried::One(class)) => out.push(self.static_value(b, class, value)),
                Some(Carried::Flat(_)) => self.static_leaves(b, value, out),
                None => {}
            }
        }
    }

    /// A known product's leaves, or a known sequence's buffer and length.
    fn static_leaves(
        &self,
        b: &mut super::Builder,
        value: barb::Constant<'_>,
        out: &mut Vec<ValueId>,
    ) {
        if self.carries[value.owner().index()] == Storage::Seq {
            out.extend(self.static_sequence(b, value));
            return;
        }
        let value = barb::single_field_constant(self.barb, value);
        let barb::ConstantView::Constructor(ctor) = value.view() else {
            unreachable!("a product constant is a constructor");
        };
        self.static_fields(b, ctor, out);
    }

    /// Build one known object, its fields at the classes the cell says.
    fn static_cell(&self, b: &mut super::Builder, ctor: barb::ConstructorView<'_>) -> ValueId {
        let mut fields = Vec::new();
        self.static_fields(b, ctor, &mut fields);
        b.cell(self.barb.tag(ctor.constructor()), &fields)
    }

    /// Build a known sequence by pushing its elements, from its end back:
    /// the buffer is nothing else's, so each push writes in place.
    fn static_sequence(&self, b: &mut super::Builder, value: barb::Constant<'_>) -> [ValueId; 2] {
        let owner = peeled(self.barb, value.owner()).expect("a sequence is not cyclic");
        let barb::TypeShape::Sequence {
            push, recursive, ..
        } = barb::type_shape(self.barb, owner)
        else {
            unreachable!("a sequence constant has a sequence type");
        };
        let value = barb::single_field_constant(self.barb, value);
        // An empty sequence lays nothing out, whatever it would hold.
        let bytes = match value.view() {
            barb::ConstantView::Spine(spine) if spine.length() == 0u8.into() => Some(Vec::new()),
            barb::ConstantView::Spine(spine) => spine.to_bytes(),
            _ => None,
        };
        let Some(bytes) = bytes else {
            self.refuse(format!(
                "`{}` holds something per element that is not a byte, which this tier cannot lay out yet",
                self.barb.name(self.barb.type_(owner).name)
            ));
            return Self::unrolled_bytes(b, &[], None);
        };
        if bytes.is_empty() {
            return Self::unrolled_bytes(b, &[], None);
        }
        let element = match self.field_carried(push, usize::from(recursive == 0)) {
            Some(Carried::One(class)) => Some(class),
            Some(Carried::Flat(_)) => unreachable!("a byte is not a product"),
            None => None,
        };
        // A long one is pushed by a loop over its bytes where they lie, so
        // that its size is in data rather than in code and a frame.
        if let Some(class) = element
            && bytes.len() > UNROLLED
        {
            let data = b.data(&bytes);
            let total = b.data_len(data);
            let start = b.address_of(data);
            return Self::pushed_bytes(b, start, total, class);
        }
        Self::unrolled_bytes(b, &bytes, element)
    }

    /// Known bytes pushed one at a time, from the last, each as `element`
    /// where an element carries anything.
    fn unrolled_bytes(
        b: &mut super::Builder,
        bytes: &[u8],
        element: Option<Class>,
    ) -> [ValueId; 2] {
        let len = u64::try_from(bytes.len()).expect("a length fits 64 bits");
        let mut buffer = b.buffer_empty();
        for (len, &byte) in bytes.iter().rev().enumerate() {
            let len = b.constant(
                Class::Word,
                u64::try_from(len).expect("a length fits 64 bits"),
            );
            let fields: Vec<_> = element
                .map(|class| b.constant(class, u64::from(byte)))
                .into_iter()
                .collect();
            buffer = b.buffer_push(buffer, len, &fields);
        }
        [buffer, b.constant(Class::Word, len)]
    }

    /// Record the first thing this tier cannot lay out. Emission has no
    /// error channel of its own -- a region is built by callbacks that
    /// answer values -- so the failure is kept here and read back once the
    /// body is built, which is where lowering can still refuse the program.
    fn refuse(&self, why: String) {
        let mut held = self.refused.borrow_mut();
        if held.is_none() {
            *held = Some(why);
        }
    }

    /// An instruction where the tier below has one, a platform routine where
    /// something outside answers, and a call otherwise. An argument that
    /// carries nothing is not passed.
    #[expect(
        clippy::too_many_lines,
        reason = "one dispatch over every kind of callee"
    )]
    fn call(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        function: barb::FnId,
        arguments: barb::Range,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let (results, answers) = match &self.callees[function.index()] {
            Callee::Instruction(operation) => {
                let args = self.call_arguments(function, arguments, locals);
                if matches!(operation, barb::Operation::Add | barb::Operation::Mul)
                    && let Some(affine) = self.facts.affine(expr)
                {
                    return Answer::Value(Held::One(self.affine(b, expr, affine, locals)));
                }
                return Answer::Value(Held::One(self.operation(
                    b,
                    *operation,
                    self.width(expr),
                    &args,
                )));
            }
            Callee::Sequence(barb::SequenceOperation::Length) => {
                return Answer::Value(Held::One(self.length(b, expr, arguments, locals)));
            }
            Callee::External {
                id,
                routine,
                handed,
            } => {
                let asked = (*routine, handed.as_slice());
                let args = self.outside_arguments(b, function, arguments, locals, statics, asked);
                (b.call(*id, &args), routine.answers())
            }
            Callee::Built {
                built,
                primitive,
                io,
            } => {
                let asked = (function, arguments);
                let results = self.built(b, asked, locals, statics, (built, *primitive, *io));
                (results, None)
            }
            Callee::Function(callee) => {
                let callee = *callee;
                let mut args = self.call_arguments(function, arguments, locals);
                for (at, arg) in args.iter_mut().enumerate() {
                    let wanted = b.takes(callee)[at];
                    *arg = met(b, *arg, wanted);
                }
                if self.goes_round(expr) {
                    b.continue_(&args);
                    return Answer::Never;
                }
                (b.call(callee, &args), None)
            }
            Callee::Unreachable => unreachable!("a lowered call must have been demanded"),
        };
        self.answered(b, expr, function, &results, answers)
    }

    /// How many elements a sequence holds, which is its length leaf.
    fn length(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        arguments: barb::Range,
        locals: &Locals,
    ) -> ValueId {
        let [sequence] = self.barb.atoms(arguments) else {
            unreachable!("a length is of one sequence");
        };
        let len = locals[sequence.0.index()]
            .as_ref()
            .expect("a counted sequence is carried")
            .values()[1];
        // A length is held in a word, which is what the tier above was told
        // a length can be; only a class with no greatest number needs it
        // converted.
        let class = self.width(expr);
        if class == Class::Natural {
            b.convert(class, len)
        } else {
            len
        }
    }

    /// What a call answers: what its result type does, which is nothing
    /// ever where that type has no values -- and at the width the name it
    /// calls was declared at, which the caller may hold wider.
    fn answered(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        function: barb::FnId,
        results: &[ValueId],
        answers: Option<Class>,
    ) -> Answer<Held> {
        let result = self.barb.function(function).result;
        self.answer(result).map(|()| {
            let carried = self.carried(result, self.facts.held(expr));
            let Carried::One(class) = carried else {
                return Held::of(carried, results);
            };
            let held = *results.first().expect("a result where a type carries one");
            Held::One(if answers == Some(Class::Word) {
                held
            } else if answers.is_some_and(|answers| !answers.fits(class)) {
                b.convert(class, held)
            } else {
                held
            })
        })
    }

    /// The machine values a call hands over: each carried argument's, end
    /// to end.
    fn call_arguments(
        &self,
        function: barb::FnId,
        args: barb::Range,
        locals: &Locals,
    ) -> Vec<ValueId> {
        let mut values = Vec::new();
        for ((atom, _), _) in self
            .barb
            .atoms(args)
            .iter()
            .zip(self.barb.params(function))
            .zip(&self.takes[function.index()])
            .filter(|((_, ty), used)| **used && self.carries[ty.index()].carried())
        {
            let held = locals[atom.0.index()]
                .as_ref()
                .expect("a demanded call argument to carry a value");
            values.extend_from_slice(held.values());
        }
        values
    }

    /// The one value a scalar local is held in.
    fn scalar(locals: &Locals, atom: barb::Atom) -> ValueId {
        locals[atom.0.index()]
            .as_ref()
            .expect("a scalar local to carry a value")
            .one()
    }

    /// Materialize a target-independent affine summary as machine arithmetic.
    /// Earlier bindings may still have emitted their source operations; the
    /// machine optimizer removes those when this expression bypasses them.
    fn affine(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        affine: &barb::Affine,
        locals: &Locals,
    ) -> ValueId {
        let class = self.width(expr);
        let mut answer = None;
        for &(atom, coefficient) in &affine.terms {
            let value = Self::scalar(locals, atom);
            let term = match coefficient {
                1 => value,
                // Preserve the primitive operation already present in x+x.
                // Machine simplification can make fixed-width doubling a
                // shift, while runtime naturals retain their cheaper add.
                2 => super::arithmetic::lower(b, barb::Operation::Add, class, value, value),
                _ => {
                    let coefficient = b.constant(width(barb::Bounds::at(coefficient)), coefficient);
                    super::arithmetic::lower(b, barb::Operation::Mul, class, value, coefficient)
                }
            };
            answer = Some(answer.map_or(term, |held| {
                super::arithmetic::lower(b, barb::Operation::Add, class, held, term)
            }));
        }
        if affine.constant != 0 || answer.is_none() {
            let constant = b.constant(width(barb::Bounds::at(affine.constant)), affine.constant);
            answer = Some(answer.map_or(constant, |held| {
                super::arithmetic::lower(b, barb::Operation::Add, class, held, constant)
            }));
        }
        met(
            b,
            answer.expect("an affine form has a term or constant"),
            class,
        )
    }

    /// The machine values a call to something outside hands over.
    ///
    /// A byte string is handed over where it lies: its bytes go in machine
    /// data and the routine reads the address and the length. Nothing about
    /// this is one routine's rule -- it is what the contract said the
    /// routine reads, so a second one taking a string needs nothing here.
    fn outside_arguments(
        &self,
        b: &mut super::Builder,
        function: barb::FnId,
        arguments: barb::Range,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
        (routine, handed): (&Routine, &[Handed]),
    ) -> Vec<ValueId> {
        let mut args = Vec::with_capacity(handed.len());
        let carried = self
            .barb
            .atoms(arguments)
            .iter()
            .zip(self.barb.params(function))
            .skip(authority(routine))
            .filter(|(_, ty)| self.carries[ty.index()] != Storage::Erased);
        for ((atom, _), handed) in carried.zip(handed) {
            match handed {
                Handed::Value(_) => args.push(Self::scalar(locals, *atom)),
                Handed::Bytes => {
                    // Something outside reads bytes where they lie, which
                    // is somewhere only a value known before the program
                    // runs is. One worked out while it runs would have to
                    // be copied somewhere contiguous first, and nothing
                    // below here does that yet.
                    let bytes = statics[atom.0.index()].map_or_else(
                        || {
                            self.refuse(format!(
                                "`{}` reads a byte string where it lies, and this one is worked out while the program runs",
                                self.barb.name(self.barb.function(function).name)
                            ));
                            Vec::new()
                        },
                        |literal| self.bytes(literal),
                    );
                    let data = b.data(&bytes);
                    args.push(b.address_of(data));
                    args.push(b.data_len(data));
                }
            }
        }
        args
    }

    /// A routine built here, called: what it answers.
    fn built(
        &self,
        b: &mut super::Builder,
        asked: (barb::FnId, barb::Range),
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
        (built, primitive, io): (&Built, Option<FunctionId>, Io),
    ) -> Vec<ValueId> {
        let primitive = || primitive.expect("a routine built on a primitive has one");
        match built {
            Built::Put(_) => vec![self.put(b, asked, locals, statics, (primitive(), io))],
            Built::Take(_) => {
                let count = self.handed_scalar(asked, locals);
                vec![Self::take(b, count, (primitive(), io))]
            }
            Built::Taken => {
                let count = self.handed_scalar(asked, locals);
                Self::taken(b, count, io).to_vec()
            }
            Built::Failure => {
                let at = b.address_of(io.failure);
                let failure = b.load(super::Width::Word, at, super::Offset::Words(0));
                let none = b.constant(Class::Word, 0);
                b.store(super::Width::Word, at, super::Offset::Words(0), none);
                vec![failure]
            }
        }
    }

    /// The one argument a routine is called with past its authority, as the
    /// word it is held in.
    fn handed_scalar(
        &self,
        (function, arguments): (barb::FnId, barb::Range),
        locals: &Locals,
    ) -> ValueId {
        let (atom, _) = self
            .barb
            .atoms(arguments)
            .iter()
            .zip(self.barb.params(function))
            .skip(1)
            .find(|(_, ty)| self.carries[ty.index()] != Storage::Erased)
            .expect("a built routine's argument is carried");
        Self::scalar(locals, *atom)
    }

    /// What a primitive answered, as a count: where it is more than it was
    /// asked to move, it failed, and the error is kept and nought answered.
    fn counted(b: &mut super::Builder, answer: ValueId, asked: ValueId, io: Io) -> ValueId {
        let failed = b.compare(Relation::Less, asked, answer);
        b.if_(
            failed,
            &[Class::Word],
            |b| {
                // `-error`, read as a word: the error is that far below the
                // top, and one more.
                let top = b.constant(Class::Word, io.top);
                let below = b.binary(Binary::Sub, top, answer);
                let one = b.constant(Class::Word, 1);
                let error = b.binary(Binary::Add, below, one);
                let at = b.address_of(io.failure);
                b.store(super::Width::Word, at, super::Offset::Words(0), error);
                let none = b.constant(Class::Word, 0);
                b.yield_(&[none]);
            },
            |b| b.yield_(&[answer]),
        )[0]
    }

    /// Hand a byte string to the primitive: where it lies, all of it, if it
    /// is known before the program runs, and otherwise its first run,
    /// copied to the scratch region. How many bytes went.
    fn put(
        &self,
        b: &mut super::Builder,
        (function, arguments): (barb::FnId, barb::Range),
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
        (write, io): (FunctionId, Io),
    ) -> ValueId {
        // Past the authority it is asked with, the one argument carried.
        let (atom, _) = self
            .barb
            .atoms(arguments)
            .iter()
            .zip(self.barb.params(function))
            .skip(1)
            .find(|(_, ty)| self.carries[ty.index()] != Storage::Erased)
            .expect("a string handed out is carried");
        let atom = *atom;
        if let Some(literal) = statics[atom.0.index()] {
            let data = b.data(&self.bytes(literal));
            let at = b.address_of(data);
            let len = b.data_len(data);
            let answer = b.call_one(write, &[at, len]);
            return Self::counted(b, answer, len, io);
        }
        let held = locals[atom.0.index()]
            .as_ref()
            .expect("a string handed out is carried");
        let [buffer, len] = held.values() else {
            unreachable!("a byte string is held as a sequence");
        };
        let run = Self::copied_run(b, (*buffer, *len), io);
        let start = b.address_of(io.scratch);
        let answer = b.call_one(write, &[start, run]);
        Self::counted(b, answer, run, io)
    }

    /// Copy a sequence's first run of bytes to the scratch region: how many.
    fn copied_run(b: &mut super::Builder, (buffer, len): (ValueId, ValueId), io: Io) -> ValueId {
        let room = b.data_len(io.scratch);
        let fits = b.compare(Relation::Less, len, room);
        let run = b.if_(
            fits,
            &[Class::Word],
            |b| b.yield_(&[len]),
            |b| b.yield_(&[room]),
        )[0];
        let none = b.constant(Class::Word, 0);
        b.loop_(&[none], &[], |b, state| {
            let at = state[0];
            let done = b.compare(Relation::Equal, at, run);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let left = b.binary(Binary::Sub, len, at);
            let value = b.buffer_field(Class::fixed(8), buffer, left, 0);
            let start = b.address_of(io.scratch);
            let base = b.convert(Class::Word, start);
            let place = b.binary(Binary::Add, base, at);
            let place = b.convert(Class::Address, place);
            b.store(super::Width::Byte, place, super::Offset::Bytes(0), value);
            let one = b.constant(Class::Word, 1);
            let next = b.binary(Binary::Add, at, one);
            b.continue_(&[next]);
        });
        run
    }

    /// Ask the primitive for up to `count` bytes, no more than a run, into
    /// the scratch region: how many came.
    fn take(b: &mut super::Builder, count: ValueId, (read, io): (FunctionId, Io)) -> ValueId {
        let count = met(b, count, Class::Word);
        let room = b.data_len(io.scratch);
        let fits = b.compare(Relation::Less, count, room);
        let run = b.if_(
            fits,
            &[Class::Word],
            |b| b.yield_(&[count]),
            |b| b.yield_(&[room]),
        )[0];
        let start = b.address_of(io.scratch);
        let answer = b.call_one(read, &[start, run]);
        Self::counted(b, answer, run, io)
    }

    /// The first `count` bytes of the scratch region, no more than a run,
    /// as a sequence: pushed from the last, since a sequence grows at its
    /// front.
    fn taken(b: &mut super::Builder, count: ValueId, io: Io) -> [ValueId; 2] {
        let count = met(b, count, Class::Word);
        let room = b.data_len(io.scratch);
        let fits = b.compare(Relation::Less, count, room);
        let run = b.if_(
            fits,
            &[Class::Word],
            |b| b.yield_(&[count]),
            |b| b.yield_(&[room]),
        )[0];
        let start = b.address_of(io.scratch);
        Self::pushed_bytes(b, start, run, Class::fixed(8))
    }

    /// The first `total` bytes where `data` lies, as a sequence of elements
    /// of `class`: pushed from the last, since a sequence grows at its front.
    fn pushed_bytes(
        b: &mut super::Builder,
        start: ValueId,
        total: ValueId,
        class: Class,
    ) -> [ValueId; 2] {
        let empty = b.buffer_empty();
        let none = b.constant(Class::Word, 0);
        let built = b.loop_(&[empty, none], &SEQUENCE_LEAVES, |b, state| {
            let (held, len) = (state[0], state[1]);
            let done = b.compare(Relation::Equal, len, total);
            b.if_(done, &[], |b| b.break_(&[held, len]), |b| b.yield_(&[]));
            let one = b.constant(Class::Word, 1);
            let rest = b.binary(Binary::Sub, total, len);
            let at = b.binary(Binary::Sub, rest, one);
            let base = b.convert(Class::Word, start);
            let place = b.binary(Binary::Add, base, at);
            let place = b.convert(Class::Address, place);
            let byte = b.load(super::Width::Byte, place, super::Offset::Bytes(0));
            let byte = b.convert(class, byte);
            let longer = b.buffer_push(held, len, &[byte]);
            let more = b.binary(Binary::Add, len, one);
            b.continue_(&[longer, more]);
        });
        [built[0], built[1]]
    }

    /// The bytes a compile-time byte string holds, read off its encoding.
    ///
    /// # Panics
    /// If the constant is not the byte string its declaration said it is.
    fn bytes(&self, literal: barb::ConstId) -> Vec<u8> {
        // A nominal string wraps its bytes; the bytes are what is handed over.
        let value = barb::single_field_constant(self.barb, self.barb.constant(literal));
        let barb::ConstantView::Spine(string) = value.view() else {
            unreachable!("a byte string is spine encoded");
        };
        string
            .to_bytes()
            .expect("a byte string's elements are byte-wide naturals")
    }

    fn operation(
        &self,
        b: &mut super::Builder,
        operation: barb::Operation,
        class: Class,
        args: &[ValueId],
    ) -> ValueId {
        match operation {
            barb::Operation::Equals { yes, no } | barb::Operation::LessThan { yes, no } => {
                let relation = if matches!(operation, barb::Operation::Equals { .. }) {
                    Relation::Equal
                } else {
                    Relation::Less
                };
                let yes = u64::from(self.barb.tag(yes));
                let no = u64::from(self.barb.tag(no));
                let yes_class = width(barb::Bounds::at(yes));
                let no_class = width(barb::Bounds::at(no));
                // Both emitted arms must fit the join, even if range analysis
                // proves only the zero tag reachable. Narrow after the join
                // in that case, rather than truncating the other arm's tag.
                let join = super::arithmetic::widest(
                    class,
                    super::arithmetic::widest(yes_class, no_class),
                );
                let test = super::arithmetic::compare(b, relation, args[0], args[1]);
                let answer = b.if_(
                    test,
                    &[join],
                    |b| {
                        let value = b.constant(yes_class, yes);
                        b.yield_(&[value]);
                    },
                    |b| {
                        let value = b.constant(no_class, no);
                        b.yield_(&[value]);
                    },
                )[0];
                met(b, answer, class)
            }
            operation => super::arithmetic::lower(b, operation, class, args[0], args[1]),
        }
    }

    /// A tag is which constructor it is. A number's empty constructor is
    /// nought and its other one counts up -- which is not the same as its
    /// tag, since a program may write `Succ` before `Zero`. One that
    /// carries nothing builds nothing, and a product held flat is only its
    /// fields' values, so building one writes nothing either.
    fn construct(
        &self,
        b: &mut super::Builder,
        expr: barb::ExprId,
        ctor: barb::CtorId,
        args: barb::Range,
        locals: &Locals,
    ) -> Option<Held> {
        let owner = self.barb.ctor(ctor).owner;
        if !self.carries[owner.index()].carried() {
            return None;
        }
        if barb::single_field(self.barb, owner).is_some() {
            let atom = self.barb.atoms(args)[0];
            return Some(
                locals[atom.0.index()]
                    .clone()
                    .expect("a transparent field to carry a value"),
            );
        }
        if self.carries[owner.index()] == Storage::Seq {
            return Some(self.construct_sequence(b, ctor, args, locals));
        }
        let class = match self.carried(owner, self.facts.held(expr)) {
            Carried::Flat(leaves) => {
                let mut values = Vec::new();
                self.field_values(b, ctor, args, locals, &mut values);
                return Some(Held::Flat {
                    leaves,
                    values: values.into(),
                });
            }
            Carried::One(class) => class,
        };
        if class == Class::Cell {
            let mut fields = Vec::new();
            self.field_values(b, ctor, args, locals, &mut fields);
            return Some(Held::One(b.cell(self.barb.tag(ctor), &fields)));
        }
        if tagged(self.barb, owner) {
            return Some(Held::One(b.constant(class, u64::from(self.barb.tag(ctor)))));
        }
        Some(Held::One(self.count(b, class, args, locals)))
    }

    /// An empty sequence is an empty buffer; a step pushes its element onto
    /// the rest's buffer, taking that buffer's claim, and counts one more.
    fn construct_sequence(
        &self,
        b: &mut super::Builder,
        ctor: barb::CtorId,
        args: barb::Range,
        locals: &Locals,
    ) -> Held {
        let owner = self.barb.ctor(ctor).owner;
        let barb::TypeShape::Sequence {
            empty, recursive, ..
        } = barb::type_shape(self.barb, owner)
        else {
            unreachable!("a sequence's constructor belongs to a sequence");
        };
        let values = if ctor == empty {
            [b.buffer_empty(), b.constant(Class::Word, 0)]
        } else {
            let atoms = self.barb.atoms(args);
            let rest = locals[atoms[recursive].0.index()]
                .as_ref()
                .expect("a sequence's rest is carried");
            let (buffer, len) = (rest.values()[0], rest.values()[1]);
            let element = usize::from(recursive == 0);
            let mut fields = Vec::new();
            if let Some(carried) = self.field_carried(ctor, element) {
                let held = locals[atoms[element].0.index()]
                    .as_ref()
                    .expect("a carried element carries a value");
                for (&value, &class) in held.values().iter().zip(self.classes(&carried)) {
                    fields.push(met(b, value, class));
                }
            }
            let pushed = b.buffer_push(buffer, len, &fields);
            let one = b.constant(Class::Word, 1);
            [pushed, b.binary(Binary::Add, len, one)]
        };
        Held::Flat {
            leaves: sequence_run(),
            values: values.as_slice().into(),
        }
    }

    /// A number built from constructors: nought, or one more than its field.
    fn count(
        &self,
        b: &mut super::Builder,
        class: Class,
        args: barb::Range,
        locals: &Locals,
    ) -> ValueId {
        let Some(&atom) = self.barb.atoms(args).first() else {
            return b.constant(class, 0);
        };
        let one = b.constant(class, 1);
        let held = Self::scalar(locals, atom);
        super::arithmetic::lower(b, barb::Operation::Add, class, held, one)
    }

    /// A constructor's fields, each as the values it is held in, at the
    /// classes its field type says.
    ///
    /// What a value was worked out as says how wide it needs to be, not
    /// where it is kept: storing a number where a projection expects an
    /// arbitrary-precision one and reading it back would read a count as
    /// though it were an address.
    fn field_values(
        &self,
        b: &mut super::Builder,
        ctor: barb::CtorId,
        args: barb::Range,
        locals: &Locals,
        out: &mut Vec<ValueId>,
    ) {
        for (atom, carried) in self.barb.atoms(args).iter().zip(self.fields_carried(ctor)) {
            let Some(carried) = carried else {
                continue;
            };
            let held = locals[atom.0.index()]
                .as_ref()
                .expect("a carried field to carry a value");
            for (&value, &class) in held.values().iter().zip(self.classes(&carried)) {
                out.push(met(b, value, class));
            }
        }
    }

    /// Matching a number asks whether it is nought; the other arm counts the
    /// scrutinee back down to what it wraps.
    #[expect(
        clippy::too_many_lines,
        reason = "shape dispatch keeps natural, scalar-tag, and cell matches visibly distinct"
    )]
    fn branch(
        &self,
        b: &mut super::Builder,
        scrutinee: Option<&Held>,
        arms: barb::Range,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
        bounds: barb::Bounds,
    ) -> Answer<Held> {
        let mut arms = reachable(self.barb, arms, bounds);
        let Some(first) = arms.next() else {
            return Answer::Never;
        };
        let Some(second) = arms.next() else {
            return self.only_arm(b, scrutinee, &first, locals, statics);
        };
        let owner = self.barb.ctor(first.ctor).owner;
        let scrutinee = scrutinee.expect("a tested value is carried");
        if self.carries[owner.index()] == Storage::Seq {
            return self.sequence_branch(b, scrutinee, [first, second], locals, statics);
        }
        // More than one arm means the value says which, so it is held, and
        // held in one value: a product is held flat, and it has one arm.
        let scrutinee = scrutinee.one();
        if self.carries[owner.index()] == Storage::Cell {
            let planned = {
                let mut carried: Vec<_> = locals
                    .iter()
                    .map(|value| value.as_ref().map(|value| value.carried(b)))
                    .collect();
                let base = carried.len();
                let mut planned: Vec<_> = [first, second]
                    .into_iter()
                    .chain(arms)
                    .map(|arm| {
                        carried.extend(self.fields_carried(arm.ctor));
                        let suffix = self.body_answer(arm.body, &mut carried);
                        carried.truncate(base);
                        TagArm { arm, suffix }
                    })
                    .collect();
                let mut suffix = Answer::Never;
                for arm in planned.iter_mut().rev() {
                    suffix = widest(arm.suffix, suffix);
                    arm.suffix = suffix;
                }
                planned
            };
            let tag = b.cell_tag(scrutinee);
            return self.cell_tags(b, scrutinee, tag, &planned, locals, statics);
        }
        // A number is the one thing left that is held as a scalar and still
        // has two arms: which constructor it is, is whether it is nought.
        // This asks the classifier representation selection asks, not the
        // one the constant codec asks, which answers about encodings.
        if let barb::TypeShape::Natural { empty: nil, .. } = barb::type_shape(self.barb, owner) {
            // A number has exactly these two arms, whatever their tags.
            let (empty, counted) = if first.ctor == nil {
                (first, second)
            } else {
                (second, first)
            };
            return self.natural_branch(b, scrutinee, &empty, &counted, locals, statics);
        }
        let arms = {
            let mut carried = locals
                .iter()
                .map(|value| value.as_ref().map(|value| value.carried(b)))
                .collect();
            tag_plan([first, second].into_iter().chain(arms), |body| {
                self.body_answer(body, &mut carried)
            })
        };
        let class = b.class(scrutinee);
        self.tags(b, scrutinee, class, &arms, locals, statics)
    }

    /// Matching a sequence asks whether it is empty, which its length says;
    /// the other arm reads the first element where the buffer holds it.
    fn sequence_branch(
        &self,
        b: &mut super::Builder,
        scrutinee: &Held,
        arms: [barb::Arm; 2],
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let answer = {
            let mut carried: Vec<_> = locals
                .iter()
                .map(|value| value.as_ref().map(|value| value.carried(b)))
                .collect();
            let base = carried.len();
            let mut answer = Answer::Never;
            for arm in arms {
                carried.extend(self.fields_carried(arm.ctor));
                answer = widest(answer, self.body_answer(arm.body, &mut carried));
                carried.truncate(base);
            }
            answer
        };
        let owner = self.barb.ctor(arms[0].ctor).owner;
        let barb::TypeShape::Sequence { empty, .. } = barb::type_shape(self.barb, owner) else {
            unreachable!("a sequence's arms belong to a sequence");
        };
        let (nil, step) = if arms[0].ctor == empty {
            (arms[0], arms[1])
        } else {
            (arms[1], arms[0])
        };
        let join = self.join(answer);
        let len = scrutinee.values()[1];
        let nought = b.constant(Class::Word, 0);
        let is_empty = b.compare(Relation::Equal, len, nought);
        let results = b.if_(
            is_empty,
            &join,
            |b| {
                let answer = self.only_arm(b, Some(scrutinee), &nil, locals, statics);
                yielded(b, answer, &join);
            },
            |b| {
                let answer = self.only_arm(b, Some(scrutinee), &step, locals, statics);
                yielded(b, answer, &join);
            },
        );
        answer.map(|carried| Held::of(carried, &results))
    }

    fn natural_branch(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        empty: &barb::Arm,
        counted: &barb::Arm,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let class = b.class(scrutinee);
        // Both arms answer alike, so whichever of them comes back says what
        // the match holds. An arm that leaves says nothing about it.
        // The counting arm binds what the scrutinee wraps, which holds what
        // the scrutinee holds.
        let answer = {
            let mut carried = locals
                .iter()
                .map(|value| value.as_ref().map(|value| value.carried(b)))
                .collect();
            let answer = self.body_answer(empty.body, &mut carried);
            carried.push(Some(Carried::One(class)));
            widest(answer, self.body_answer(counted.body, &mut carried))
        };
        let join = self.join(answer);
        let nought = b.constant(class, 0);
        let is_nought = b.compare(Relation::Equal, scrutinee, nought);
        let results = b.if_(
            is_nought,
            &join,
            |b| {
                let mut inner = locals.to_vec();
                let mut inner_statics = statics.to_vec();
                let answer = self.body(b, empty.body, &mut inner, &mut inner_statics);
                yielded(b, answer, &join);
            },
            |b| {
                let mut inner = locals.to_vec();
                let mut inner_statics = statics.to_vec();
                let one = b.constant(class, 1);
                inner.push(Some(Held::One(b.binary(Binary::Sub, scrutinee, one))));
                inner_statics.push(None);
                let answer = self.body(b, counted.body, &mut inner, &mut inner_statics);
                yielded(b, answer, &join);
            },
        );
        answer.map(|carried| Held::of(carried, &results))
    }

    fn only_arm(
        &self,
        b: &mut super::Builder,
        scrutinee: Option<&Held>,
        arm: &barb::Arm,
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let mut inner = locals.to_vec();
        let mut inner_statics = statics.to_vec();
        let owner = self.barb.ctor(arm.ctor).owner;
        // Only a step that binds something reads the value it steps into,
        // and a type carrying nothing has no such step.
        if let Some(scrutinee) = scrutinee {
            // Ask transparency first, the way construction does. A wrapper
            // around a product is held as that product, so its storage
            // class is the product's -- and taking one apart here would
            // take the product apart a step early.
            if barb::single_field(self.barb, owner).is_some() {
                inner.push(Some(scrutinee.clone()));
                inner_statics.push(None);
            } else if self.carries[owner.index()] == Storage::Seq {
                self.bind_sequence_fields(b, scrutinee, arm.ctor, &mut inner, &mut inner_statics);
            } else if let Storage::Flat(_) = self.carries[owner.index()] {
                self.bind_flat_fields(scrutinee.values(), arm.ctor, &mut inner, &mut inner_statics);
            } else if self.carries[owner.index()] == Storage::Cell {
                self.bind_cell_fields(b, scrutinee.one(), arm.ctor, &mut inner, &mut inner_statics);
            } else if let barb::TypeShape::Sequence { push, .. }
            | barb::TypeShape::Natural { push, .. }
            | barb::TypeShape::Spine { push, .. } = barb::type_shape(self.barb, owner)
                && arm.ctor == push
            {
                let scrutinee = scrutinee.one();
                let one = b.constant(b.class(scrutinee), 1);
                inner.push(Some(Held::One(b.binary(Binary::Sub, scrutinee, one))));
                inner_statics.push(None);
            }
        } else {
            // The arm still binds what its constructor declares, and a
            // constructor of a type carrying nothing declares nothing that
            // is carried either.
            for carried in self.fields_carried(arm.ctor) {
                inner.push(None);
                inner_statics.push(None);
                debug_assert!(
                    carried.is_none(),
                    "a carried field belongs to a carried type"
                );
            }
        }
        self.body(b, arm.body, &mut inner, &mut inner_statics)
    }

    /// A step of a sequence binds its element, read from the buffer, and its
    /// rest, which is the same buffer one shorter. An empty one binds nothing.
    fn bind_sequence_fields(
        &self,
        b: &mut super::Builder,
        scrutinee: &Held,
        ctor: barb::CtorId,
        locals: &mut Vec<Option<Held>>,
        statics: &mut Vec<Option<barb::ConstId>>,
    ) {
        let owner = self.barb.ctor(ctor).owner;
        let barb::TypeShape::Sequence { recursive, .. } = barb::type_shape(self.barb, owner) else {
            unreachable!("a sequence's constructor belongs to a sequence");
        };
        let (buffer, len) = (scrutinee.values()[0], scrutinee.values()[1]);
        for (at, carried) in self.fields_carried(ctor).enumerate() {
            let field = carried.map(|carried| {
                if at == recursive {
                    let one = b.constant(Class::Word, 1);
                    let shorter = b.binary(Binary::Sub, len, one);
                    return Held::of(carried, &[buffer, shorter]);
                }
                let values: Vec<_> = (0u32..)
                    .zip(self.classes(&carried))
                    .map(|(leaf, &class)| b.buffer_field(class, buffer, len, leaf))
                    .collect();
                Held::of(carried, &values)
            });
            locals.push(field);
            statics.push(None);
        }
    }

    /// Taking a flat product apart reads nothing: each field is the run of
    /// its leaves, where construction laid them.
    fn bind_flat_fields(
        &self,
        values: &[ValueId],
        ctor: barb::CtorId,
        locals: &mut Vec<Option<Held>>,
        statics: &mut Vec<Option<barb::ConstId>>,
    ) {
        let mut rest = values;
        for carried in self.fields_carried(ctor) {
            let field = carried.map(|carried| {
                let (field, after) = rest.split_at(self.classes(&carried).len());
                rest = after;
                Held::of(carried, field)
            });
            locals.push(field);
            statics.push(None);
        }
        debug_assert!(rest.is_empty(), "every leaf belongs to a field");
    }

    fn bind_cell_fields(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        ctor: barb::CtorId,
        locals: &mut Vec<Option<Held>>,
        statics: &mut Vec<Option<barb::ConstId>>,
    ) {
        let mut index = 0;
        for carried in self.fields_carried(ctor) {
            let field = carried.map(|carried| {
                let values: Vec<_> = self
                    .classes(&carried)
                    .iter()
                    .map(|&class| {
                        let field = b.cell_field(class, scrutinee, index);
                        index += 1;
                        field
                    })
                    .collect();
                Held::of(carried, &values)
            });
            locals.push(field);
            statics.push(None);
        }
    }

    /// Matching a tag asks which one it is, arm by arm. The last needs no
    /// asking: nothing else is left for the value to be.
    ///
    /// A run of tests is what a target has instructions for. Anything
    /// cleverer -- a jump table, a search -- wants more constructors than
    /// anything here has, and would be this tier deciding what a target is
    /// better placed to.
    fn tags(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        class: Class,
        arms: &[TagArm],
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let (
            TagArm {
                arm,
                suffix: answer,
            },
            rest,
        ) = arms.split_first().expect("an arm to match");
        if rest.is_empty() {
            let mut inner = locals.to_vec();
            let mut inner_statics = statics.to_vec();
            return self.body(b, arm.body, &mut inner, &mut inner_statics);
        }
        let join = self.join(*answer);
        let tag = b.constant(class, u64::from(self.barb.tag(arm.ctor)));
        let is_this_one = b.compare(Relation::Equal, scrutinee, tag);
        let results = b.if_(
            is_this_one,
            &join,
            |b| {
                let mut inner = locals.to_vec();
                let mut inner_statics = statics.to_vec();
                let answer = self.body(b, arm.body, &mut inner, &mut inner_statics);
                yielded(b, answer, &join);
            },
            |b| {
                let answer = self.tags(b, scrutinee, class, rest, locals, statics);
                yielded(b, answer, &join);
            },
        );
        answer.map(|carried| Held::of(carried, &results))
    }

    fn cell_tags(
        &self,
        b: &mut super::Builder,
        scrutinee: ValueId,
        discriminator: ValueId,
        arms: &[TagArm],
        locals: &Locals,
        statics: &[Option<barb::ConstId>],
    ) -> Answer<Held> {
        let (
            TagArm {
                arm,
                suffix: answer,
            },
            rest,
        ) = arms.split_first().expect("an arm to match");
        let held = Held::One(scrutinee);
        if rest.is_empty() {
            return self.only_arm(b, Some(&held), arm, locals, statics);
        }
        let join = self.join(*answer);
        let tag = b.constant(Class::Word, u64::from(self.barb.tag(arm.ctor)));
        let is_this_one = b.compare(Relation::Equal, discriminator, tag);
        let results = b.if_(
            is_this_one,
            &join,
            |b| {
                let answer = self.only_arm(b, Some(&held), arm, locals, statics);
                yielded(b, answer, &join);
            },
            |b| {
                let answer = self.cell_tags(b, scrutinee, discriminator, rest, locals, statics);
                yielded(b, answer, &join);
            },
        );
        answer.map(|carried| Held::of(carried, &results))
    }

    /// What a body answers, read off its shape: an `if` has to be told what
    /// its arms leave with before either of them is lowered.
    ///
    /// Local presence is occurrence-specific, not an `ExprId` cache. Reuse the
    /// scratch stack across siblings, restoring it even when a binding exits.
    fn body_answer(&self, body: barb::Body, carried: &mut Vec<Option<Carried>>) -> Answer<Carried> {
        let base = carried.len();
        let answer = 'body: {
            for &binding in self.barb.bindings(body.bindings) {
                let answer = self.expr_answer(binding, carried);
                if matches!(answer, Answer::Never) {
                    break 'body answer;
                }
                carried.push(answer.held());
            }
            self.expr_answer(body.tail, carried)
        };
        carried.truncate(base);
        answer
    }

    fn expr_answer(
        &self,
        expr: barb::ExprId,
        carried: &mut Vec<Option<Carried>>,
    ) -> Answer<Carried> {
        match self.barb.expr(expr) {
            barb::Expr::Static(value) => {
                let ty = self.barb.constant(value).owner();
                self.answer(ty)
                    .map(|()| self.carried(ty, self.facts.held(expr)))
            }
            barb::Expr::Con(ctor, _) => {
                let ty = self.barb.ctor(ctor).owner;
                self.answer(ty)
                    .map(|()| self.carried(ty, self.facts.held(expr)))
            }
            // A call of itself in tail position goes round again rather
            // than answering here.
            barb::Expr::Call(..) if self.goes_round(expr) => Answer::Never,
            barb::Expr::Call(function, _) => {
                let ty = self.barb.function(function).result;
                self.answer(ty)
                    .map(|()| self.carried(ty, self.facts.held(expr)))
            }
            barb::Expr::Match(_, arms) => {
                let base = carried.len();
                let mut answer = Answer::Never;
                for arm in reachable(self.barb, arms, self.facts.matched(expr)) {
                    carried.extend(self.fields_carried(arm.ctor));
                    answer = widest(answer, self.body_answer(arm.body, carried));
                    carried.truncate(base);
                }
                answer
            }
            barb::Expr::Atom(atom) => match carried[atom.0.index()] {
                Some(Carried::One(Class::Cell)) => Answer::Value(Carried::One(Class::Cell)),
                Some(Carried::One(_)) => Answer::Value(Carried::One(self.width(expr))),
                Some(flat @ Carried::Flat(_)) => Answer::Value(flat),
                None => Answer::Nothing,
            },
        }
    }

    /// Whether a type answers with a value, nothing where it carries
    /// nothing, and nothing ever where it has no values at all.
    fn answer(&self, id: barb::TypeId) -> Answer<()> {
        if uninhabited(self.barb, id) {
            return Answer::Never;
        }
        self.carries[id.index()].carried().then_some(()).into()
    }
}
