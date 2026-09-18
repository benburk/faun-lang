//! What a target answers for, said once.
//!
//! A routine is where a program meets the outside: a name it declares and
//! never defines, and a target provides. Two tiers read this table and
//! neither owns it. The language above reads what a routine is called, how
//! much a program hands it, and what holding it means; the machine tier
//! below reads what it takes and leaves in a target's own terms. barb, in
//! between, reads none of it -- a routine there is a name with no body, like
//! any other.
//!
//! Saying it once is the point. It was said twice before, in two
//! vocabularies that had to agree and nothing checked, and a third time in
//! each target as a `match` on the name with a signature assumed per arm.

use crate::ir::Class;

/// A routine, as every tier that reads one reads it.
#[derive(Debug)]
pub struct Routine {
    /// What a target answers to. Two names in a program may pick out the
    /// same routine, which is how one serves a program at more than one
    /// type: there is no body to copy, so nothing is duplicated by it.
    pub name: &'static str,
    /// What a program calls it, where a program may call it at all. A
    /// routine with no name here is one a target provides and no language
    /// yet offers -- the tier below still reaches it, since a program built
    /// rather than written is a program too.
    pub called: Option<&'static str>,
    /// What it reads and what it leaves, in the machine's terms.
    ///
    /// How many arguments a program hands it is `takes.len()`, which holds
    /// while everything handed over is carried. A token carrying nothing
    /// would take no slot here and still be written at the call, and then
    /// this would have to say both.
    pub takes: &'static [Class],
    pub answers: &'static [Class],
    /// Whether control comes back. Nothing after a call to one that does
    /// not is ever reached, and nothing is laid out for it.
    pub comes_back: bool,
    /// Whether a program hands it the authority it holds, which is the
    /// language's way of saying a program may observe this one working.
    /// Nothing below the language reads it.
    pub authority: bool,
    /// Which argument it hands straight back, counted past the authority.
    /// Nothing can be read off a declaration, so what is known of one is
    /// what this says.
    pub hands_back: Option<usize>,
}

/// Every routine there is. A program naming anything else is not a program
/// any target can be handed.
pub const ROUTINES: [Routine; 4] = [
    Routine {
        name: "write",
        called: None,
        takes: &[Class::Address, Class::Word],
        answers: &[],
        comes_back: true,
        authority: true,
        hands_back: None,
    },
    Routine {
        name: "exit",
        called: Some("exit!"),
        takes: &[Class::Word],
        answers: &[],
        comes_back: false,
        authority: true,
        hands_back: None,
    },
    // What a target hands straight back. Nothing happens, and that is the
    // point: a value that went through it is a value no tier worked out, so
    // a program can hold one the compiler will not fold away. It is handed
    // no authority, since nothing about it is observable -- what it is for
    // is being a name with no body.
    Routine {
        name: "opaque",
        called: Some("opaque"),
        takes: &[Class::Word],
        answers: &[Class::Word],
        comes_back: true,
        authority: false,
        hands_back: Some(0),
    },
    // The kernel picks the address, so nothing asking for a page says where.
    Routine {
        name: "grow",
        called: None,
        takes: &[Class::Word],
        answers: &[Class::Address],
        comes_back: true,
        authority: true,
        hands_back: None,
    },
];

/// The routine a target answers to by `name`.
#[must_use]
pub fn routine(name: &str) -> Option<&'static Routine> {
    ROUTINES.iter().find(|routine| routine.name == name)
}

/// Every routine a program may call by name, and what each is called.
pub fn offered() -> impl Iterator<Item = (&'static str, &'static Routine)> {
    ROUTINES
        .iter()
        .filter_map(|routine| Some((routine.called?, routine)))
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
