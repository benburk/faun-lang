//! The routines a target answers for.
//!
//! A program declares one by name, and this is what the name means. Nothing
//! above this tier can say it -- barb has no type of its own for a machine
//! word, since a number there is whatever a program builds out of its own
//! constructors -- and every target below would otherwise say it again, in
//! the shape of a `match` on the name with a signature assumed in each arm.

use super::model::Class;

/// A routine, as the tier declaring it and the tiers answering for it both
/// read it.
#[derive(Debug)]
pub(super) struct Routine {
    pub(super) name: &'static str,
    pub(super) takes: &'static [Class],
    pub(super) answers: &'static [Class],
    /// Whether control comes back. Nothing after a call to one that does
    /// not is ever reached, and nothing is laid out for it.
    pub(super) comes_back: bool,
}

/// Every routine there is. A program naming anything else is not a program
/// any target can be handed.
pub(super) const ROUTINES: [Routine; 4] = [
    Routine {
        name: "write",
        takes: &[Class::Address, Class::Word],
        answers: &[],
        comes_back: true,
    },
    Routine {
        name: "exit",
        takes: &[Class::Word],
        answers: &[],
        comes_back: false,
    },
    // What a target hands straight back. Nothing happens, and that is the
    // point: a value that went through it is a value no tier worked out, so
    // a program can hold one the compiler will not fold away.
    Routine {
        name: "opaque",
        takes: &[Class::Word],
        answers: &[Class::Word],
        comes_back: true,
    },
    // The kernel picks the address, so nothing asking for a page says where.
    Routine {
        name: "grow",
        takes: &[Class::Word],
        answers: &[Class::Address],
        comes_back: true,
    },
];

pub(super) fn routine(name: &str) -> Option<&'static Routine> {
    ROUTINES.iter().find(|routine| routine.name == name)
}

/// A run of classes as a sentence, for saying what a routine wanted and
/// what it was handed instead.
pub(super) fn reads(classes: &[Class]) -> String {
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
