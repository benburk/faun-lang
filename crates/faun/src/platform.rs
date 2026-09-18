//! What a target answers for, said once.
//!
//! A routine is where a program meets the outside: a name it declares and
//! never defines, and a target provides. Two tiers read these and neither
//! owns them. The language above reads what a routine is called, how much a
//! program hands it, and what holding it means; the machine tier below reads
//! what it takes and leaves in a target's own terms. barb, in between, reads
//! none of it -- a routine there is a name with no body, like any other.
//!
//! Saying it once is the point. It was said twice before, in two
//! vocabularies that had to agree and nothing checked, and a third time in
//! each target as a `match` on the name with a signature assumed per arm.
//!
//! What a compiler knows is [`Routines::builtin`], and a set is something a
//! program is read against rather than something the compiler is: a routine
//! a target reaches by name and nothing else -- a symbol in a library, a
//! function another module exports -- is one somebody writes down, and a set
//! that cannot grow is a set nobody can write into.

use crate::ir::Class;

/// A routine, as every tier that reads one reads it.
#[derive(Clone, Debug)]
pub struct Routine {
    /// What a target answers to. Two names in a program may pick out the
    /// same routine, which is how one serves a program at more than one
    /// type: there is no body to copy, so nothing is duplicated by it.
    pub name: String,
    /// What a program calls it, where a program may call it at all. A
    /// routine with no name here is one a target provides and no language
    /// yet offers -- the tier below still reaches it, since a program built
    /// rather than written is a program too.
    pub called: Option<String>,
    /// What it reads and what it leaves, in the machine's terms.
    ///
    /// How many arguments a program hands it is `takes.len()`, which holds
    /// while everything handed over is carried. A token carrying nothing
    /// would take no slot here and still be written at the call, and then
    /// this would have to say both.
    pub takes: Vec<Class>,
    pub answers: Vec<Class>,
    /// Whether control comes back. Nothing after a call to one that does
    /// not is ever reached, and nothing is laid out for it.
    pub comes_back: bool,
}

/// The routines a program is read against.
///
/// Every one of them is observable. A name with no body is something outside
/// answers for, and what it does while answering cannot be seen from here,
/// so a program calling one is a program that may be watched working.
///
/// A program naming anything outside the set it was read with is not a
/// program any target can be handed, and one naming something in it that
/// its own target does not answer for is refused by the target.
#[derive(Clone, Debug, Default)]
pub struct Routines(Vec<Routine>);

impl Routines {
    /// What every compiler knows: the routines a target answers for out of
    /// its own machine, rather than by reaching a name somebody wrote down.
    #[must_use]
    pub fn builtin() -> Self {
        let held = |name: &str, called: Option<&str>, takes: &[Class], answers: &[Class]| Routine {
            name: name.to_owned(),
            called: called.map(str::to_owned),
            takes: takes.to_vec(),
            answers: answers.to_vec(),
            comes_back: true,
        };
        Self(vec![
            held("write", None, &[Class::Address, Class::Word], &[]),
            Routine {
                comes_back: false,
                ..held("exit", Some("exit!"), &[Class::Word], &[])
            },
            // The kernel picks the address, so nothing asking for a page
            // says where.
            held("grow", None, &[Class::Word], &[Class::Address]),
            // How many arguments a program was handed, which is the one
            // thing every machine here can be asked and the only thing a
            // program can be told that it did not work out itself.
            held("argc", Some("argc!"), &[], &[Class::Word]),
        ])
    }

    /// The routine a target answers to by `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Routine> {
        self.0.iter().find(|routine| routine.name == name)
    }

    /// Every routine a program may call by name, and what each is called.
    pub fn offered(&self) -> impl Iterator<Item = (&str, &Routine)> {
        self.0
            .iter()
            .filter_map(|routine| Some((routine.called.as_deref()?, routine)))
    }

    /// Take one more in, which is how a routine somebody wrote down arrives.
    pub fn push(&mut self, routine: Routine) {
        self.0.push(routine);
    }
}

/// A run of classes as a sentence, for saying what a routine wanted and
/// what it was handed instead.
#[must_use]
pub fn reads(classes: &[Class]) -> String {
    if classes.is_empty() {
        return "nothing".to_owned();
    }
    classes
        .iter()
        .map(|class| match *class {
            Class::Word => "a word".to_owned(),
            Class::Address => "an address".to_owned(),
            Class::Fixed { bits } => format!("{bits} bits"),
        })
        .collect::<Vec<_>>()
        .join(" and ")
}
