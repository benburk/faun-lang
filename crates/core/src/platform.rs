//! What a target answers for, said once.
//!
//! A routine describes a chosen environment: what a source program may name,
//! and the machine contract a target supplies. Frontend setup and lowering
//! read these contracts; target acceptance checks calls against its own set.
//! Machine programs keep ordinary external function declarations, not this
//! catalog. barb reads none of it -- an external there is a name with no body,
//! like any other.
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

/// What one of a routine's parameters is handed.
///
/// A routine reads machine values, and a source value is not always one of
/// them. A byte string is the case that matters here: a machine reads where
/// it starts and how long it is, which is two values where a program wrote
/// one. Saying that here means lowering reads a contract rather than
/// recognising a name, and a second routine taking a string needs nothing
/// added to the tier below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Takes {
    /// One value, in the machine's terms.
    Scalar(Class),
    /// A run of bytes known before the program runs, handed over as the
    /// address it starts at and the number of bytes it is.
    StaticBytes,
}

impl Takes {
    /// The machine values one source argument becomes, in order. A byte
    /// string becomes two; everything else so far becomes itself.
    #[must_use]
    pub fn classes(self) -> Vec<Class> {
        match self {
            Self::Scalar(class) => vec![class],
            Self::StaticBytes => vec![Class::Address, Class::Word],
        }
    }

    /// How many machine values one source argument becomes.
    #[must_use]
    pub const fn width(self) -> usize {
        match self {
            Self::Scalar(_) => 1,
            Self::StaticBytes => 2,
        }
    }
}

/// A host call's control-flow and result contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Returns {
    Never,
    Unit,
    Value(Class),
}

/// A routine, as every tier that reads one reads it.
#[derive(Clone, Debug)]
pub struct Routine {
    /// The one name it has: what a program writes, and what a target is
    /// asked by. Nothing translates between those, so no two tiers can
    /// disagree about which routine a call meant.
    ///
    /// The `!` in one is this language's, and a target knowing it is the
    /// coupling between a frontend and a target that the host interface
    /// gave up trying to avoid.
    pub name: String,
    /// Whether a program may name it.
    ///
    /// One offered to nothing is a routine a target answers for and no
    /// program may reach: the heap's own hook, or anything a target uses to
    /// build what it offers. The tier below still reaches it, since a
    /// program built rather than written is a program too.
    pub offered: bool,
    /// What it reads and what it leaves.
    ///
    /// One entry per argument a program hands it, which is not always one
    /// machine value: [`Takes::StaticBytes`] is two. A token carrying
    /// nothing takes no slot here and is still written at the call, so what
    /// this counts is what a machine reads rather than what a source wrote.
    pub takes: Vec<Takes>,
    pub returns: Returns,
}

impl Routine {
    /// Copy this environment contract into an ordinary machine declaration.
    /// The machine program retains no catalog; targets check the declaration
    /// against their own contracts before emission.
    pub fn declare(&self, program: &mut crate::ir::Program) -> crate::ir::FunctionId {
        let answers = self.answers();
        let returns = if self.comes_back() {
            crate::ir::Returns::Values(answers.as_slice())
        } else {
            crate::ir::Returns::Never
        };
        program.external(&self.name, &self.reads(), returns)
    }

    /// The machine classes it reads, one argument expanded at a time.
    #[must_use]
    pub fn reads(&self) -> Vec<Class> {
        self.takes
            .iter()
            .copied()
            .flat_map(Takes::classes)
            .collect()
    }

    /// Copy this contract while retaining parameter names from the source
    /// declaration.
    ///
    /// # Panics
    /// If there is not exactly one name for each parameter.
    pub fn declare_named(
        &self,
        program: &mut crate::ir::Program,
        names: &[&str],
    ) -> crate::ir::FunctionId {
        assert_eq!(names.len(), self.takes.len(), "one name per argument");
        // An argument becoming two machine values needs a name for each. The
        // source wrote one, so the second is derived from it rather than
        // asked for: a name is diagnostic here, not part of the contract.
        let mut owned: Vec<(String, Class)> = Vec::with_capacity(self.takes.len());
        for (&name, takes) in names.iter().zip(&self.takes) {
            match takes {
                Takes::Scalar(class) => owned.push((name.to_owned(), *class)),
                Takes::StaticBytes => {
                    owned.push((format!("{name}.at"), Class::Address));
                    owned.push((format!("{name}.len"), Class::Word));
                }
            }
        }
        let params: Vec<(&str, Class)> = owned
            .iter()
            .map(|(name, class)| (name.as_str(), *class))
            .collect();
        let answers = self.answers();
        let returns = if self.comes_back() {
            crate::ir::Returns::Values(answers.as_slice())
        } else {
            crate::ir::Returns::Never
        };
        program.external_named(&self.name, &params, returns)
    }

    #[must_use]
    pub const fn answers(&self) -> Option<Class> {
        match self.returns {
            Returns::Value(class) => Some(class),
            Returns::Unit | Returns::Never => None,
        }
    }

    #[must_use]
    pub const fn comes_back(&self) -> bool {
        !matches!(self.returns, Returns::Never)
    }

    /// What a program may assume about the number it answers with.
    ///
    /// A target answers in a machine's width, so nothing wider than that
    /// width comes back, and the tier above is entitled to know it: a count
    /// a program adds to is a count it has a bound for. One that answers
    /// nothing, or answers something that is not a number, bounds nothing.
    #[must_use]
    pub fn bounds(&self) -> Option<crate::barb::Bounds> {
        self.answers().map(held_bounds)
    }
}

/// A value a target hands the entry when the program starts, by name.
///
/// The target produces it where it starts the program, into the entry's
/// frame, and nothing asks for it again. An entry that never reads one has
/// no parameter for it once lowering drops unused ones, so the target never
/// produces it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Startup {
    pub name: String,
    pub class: Class,
}

impl Startup {
    /// What a program may assume about the number it is handed.
    #[must_use]
    pub fn bounds(&self) -> crate::barb::Bounds {
        held_bounds(self.class)
    }
}

/// The numbers a machine value of `class` can hold.
fn held_bounds(class: Class) -> crate::barb::Bounds {
    let high = match class {
        Class::Word => Some(u64::MAX),
        held @ Class::Held(_) => held.width().map(|bits| {
            if bits < 64 {
                (1u64 << bits) - 1
            } else {
                u64::MAX
            }
        }),
        // A natural, an address, or a width no machine here has: a number
        // with no bound rather than no number.
        _ => None,
    };
    crate::barb::Bounds { low: 0, high }
}

/// The routines a program is read against.
///
/// Every one of them is observable. A name with no body is something outside
/// answers for, and what it does while answering cannot be seen from here,
/// so a program calling one is a program that may be watched working.
///
/// A source program naming anything outside the set it was read with is not a
/// program any target can be handed, and one naming something in it that
/// its own target does not answer for is refused by the target.
#[derive(Clone, Debug, Default)]
pub struct Routines {
    routines: Vec<Routine>,
    startup: Vec<Startup>,
}

impl Routines {
    /// What every compiler knows: the routines a target answers for out of
    /// its own machine, rather than by reaching a name somebody wrote down.
    #[must_use]
    pub fn builtin() -> Self {
        let held = |name: &str, offered, takes: &[Takes], returns| Routine {
            name: name.to_owned(),
            offered,
            takes: takes.to_vec(),
            returns,
        };
        let offered = |name: &str, takes: &[Takes], returns| held(name, true, takes, returns);
        let hidden = |name: &str, takes: &[Takes], returns| held(name, false, takes, returns);
        let word = Takes::Scalar(Class::Word);
        let routines = vec![
            // One argument, two machine values: a program hands over a
            // string and a machine reads where it starts and how long it is.
            offered("write!", &[Takes::StaticBytes], Returns::Unit),
            offered("exit!", &[word], Returns::Never),
            // The kernel picks the address, so nothing asking for a page
            // says where.
            hidden("grow", &[word], Returns::Value(Class::Address)),
            // How many arguments a program was handed.
            offered("argc!", &[], Returns::Value(Class::Word)),
            // One byte from standard input, offset by one so nought can say
            // EOF without losing the byte whose bits are all nought.
            offered("read_byte!", &[], Returns::Value(Class::fixed(9))),
        ];
        let startup = vec![
            // How many arguments a program was handed.
            Startup {
                name: "argc".to_owned(),
                class: Class::Word,
            },
        ];
        Self { routines, startup }
    }

    /// Resolve the finite range of a host word for a particular target.
    /// The range is a host contract, not a bound on the language's Nat type.
    #[must_use]
    pub fn with_word(mut self, bits: u16) -> Self {
        for routine in &mut self.routines {
            if routine.returns == Returns::Value(Class::Word) {
                routine.returns = Returns::Value(Class::fixed(bits));
            }
        }
        for value in &mut self.startup {
            if value.class == Class::Word {
                value.class = Class::fixed(bits);
            }
        }
        self
    }

    /// Every routine a program may call by name.
    pub fn offered(&self) -> impl Iterator<Item = &Routine> {
        self.routines.iter().filter(|routine| routine.offered)
    }

    /// The routine a target answers to by `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Routine> {
        self.routines.iter().find(|routine| routine.name == name)
    }

    /// The startup value a target hands the entry by `name`.
    #[must_use]
    pub fn startup(&self, name: &str) -> Option<&Startup> {
        self.startup.iter().find(|value| value.name == name)
    }

    /// Declare one of this environment's contracts in a machine program.
    ///
    /// # Panics
    /// If the environment has no routine with this name.
    pub fn declare(&self, program: &mut crate::ir::Program, name: &str) -> crate::ir::FunctionId {
        self.get(name)
            .unwrap_or_else(|| panic!("no routine named `{name}`"))
            .declare(program)
    }

    /// The ones named, and no others. What a target answers for is not what
    /// every target answers for, and a program is read against the one it
    /// is being compiled for.
    #[must_use]
    pub fn only(&self, names: &[&str]) -> Self {
        Self {
            routines: self
                .routines
                .iter()
                .filter(|routine| names.contains(&routine.name.as_str()))
                .cloned()
                .collect(),
            startup: self
                .startup
                .iter()
                .filter(|value| names.contains(&value.name.as_str()))
                .cloned()
                .collect(),
        }
    }

    /// Take one more in, which is how a routine somebody wrote down arrives.
    pub fn push(&mut self, routine: Routine) {
        self.routines.push(routine);
    }
}

/// A run of arguments as a sentence, for saying what a routine wanted.
#[must_use]
pub fn takes(takes: &[Takes]) -> String {
    if takes.is_empty() {
        return "nothing".to_owned();
    }
    takes
        .iter()
        .map(|takes| match takes {
            Takes::StaticBytes => "a byte string".to_owned(),
            Takes::Scalar(class) => reads(std::slice::from_ref(class)),
        })
        .collect::<Vec<_>>()
        .join(" and ")
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
            Class::Cell => "an algebraic cell".to_owned(),
            Class::Buffer => "a sequence buffer".to_owned(),
            Class::Natural => "an arbitrary-precision natural".to_owned(),
            Class::Word => "a word".to_owned(),
            Class::Address => "an address".to_owned(),
            Class::Held(_) => class.width().map_or_else(
                || "a number with no greatest".to_owned(),
                |bits| format!("{bits} bits"),
            ),
        })
        .collect::<Vec<_>>()
        .join(" and ")
}
