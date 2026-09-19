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
    /// What a target answers to. Two names in a program may pick out the
    /// same routine, which is how one serves a program at more than one
    /// type: there is no body to copy, so nothing is duplicated by it.
    pub name: String,
    /// What a program calls it, where a program may call it at all.
    ///
    /// A routine with no name here is one a target answers for and no
    /// program may reach: the heap's own hook, or anything a target uses to
    /// build what it offers. The tier below still reaches it, since a
    /// program built rather than written is a program too.
    ///
    /// The `!` in one is this language's, and a target knowing it is the
    /// coupling between a frontend and a target that the host interface
    /// gave up trying to avoid.
    pub called: Option<String>,
    /// What it reads and what it leaves, in the machine's terms.
    ///
    /// How many arguments a program hands it is `takes.len()`, which holds
    /// while everything handed over is carried. A token carrying nothing
    /// would take no slot here and still be written at the call, and then
    /// this would have to say both.
    pub takes: Vec<Class>,
    pub returns: Returns,
}

impl Routine {
    /// Copy this environment contract into an ordinary machine declaration.
    /// The machine program retains no catalog; targets check the declaration
    /// against their own contracts before emission.
    pub fn declare(&self, program: &mut crate::ir::Program, name: &str) -> crate::ir::FunctionId {
        let answers = self.answers();
        let returns = if self.comes_back() {
            crate::ir::Returns::Values(answers.as_slice())
        } else {
            crate::ir::Returns::Never
        };
        program.external(name, &self.name, &self.takes, returns)
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
pub struct Routines(Vec<Routine>);

impl Routines {
    /// What every compiler knows: the routines a target answers for out of
    /// its own machine, rather than by reaching a name somebody wrote down.
    #[must_use]
    pub fn builtin() -> Self {
        let held = |name: &str, called: Option<&str>, takes: &[Class], returns| Routine {
            name: name.to_owned(),
            called: called.map(str::to_owned),
            takes: takes.to_vec(),
            returns,
        };
        Self(vec![
            held("write", None, &[Class::Address, Class::Word], Returns::Unit),
            held("exit", Some("exit!"), &[Class::Word], Returns::Never),
            // The kernel picks the address, so nothing asking for a page
            // says where.
            held("grow", None, &[Class::Word], Returns::Value(Class::Address)),
            // How many arguments a program was handed, which is the one
            // thing every machine here can be asked and the only thing a
            // program can be told that it did not work out itself.
            held("argc", Some("argc!"), &[], Returns::Value(Class::Word)),
        ])
    }

    /// Resolve the finite range of a host word for a particular target.
    /// The range is a host contract, not a bound on the language's Nat type.
    #[must_use]
    pub fn with_word(mut self, bits: u16) -> Self {
        for routine in &mut self.0 {
            if routine.returns == Returns::Value(Class::Word) {
                routine.returns = Returns::Value(Class::Fixed { bits });
            }
        }
        self
    }

    /// Every routine a program may call by name, and what each is called.
    pub fn offered(&self) -> impl Iterator<Item = (&str, &Routine)> {
        self.0
            .iter()
            .filter_map(|routine| Some((routine.called.as_deref()?, routine)))
    }

    /// The routine a target answers to by `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Routine> {
        self.0.iter().find(|routine| routine.name == name)
    }

    /// Declare one of this environment's contracts in a machine program.
    ///
    /// # Panics
    /// If the environment has no routine with this name.
    pub fn declare(&self, program: &mut crate::ir::Program, name: &str) -> crate::ir::FunctionId {
        self.get(name)
            .unwrap_or_else(|| panic!("no routine named `{name}`"))
            .declare(program, name)
    }

    /// The ones named, and no others. What a target answers for is not what
    /// every target answers for, and a program is read against the one it
    /// is being compiled for.
    #[must_use]
    pub fn only(&self, names: &[&str]) -> Self {
        Self(
            self.0
                .iter()
                .filter(|routine| names.contains(&routine.name.as_str()))
                .cloned()
                .collect(),
        )
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
            Class::Natural => "an arbitrary-precision natural".to_owned(),
            Class::Word => "a word".to_owned(),
            Class::Address => "an address".to_owned(),
            Class::Fixed { bits } => format!("{bits} bits"),
        })
        .collect::<Vec<_>>()
        .join(" and ")
}
