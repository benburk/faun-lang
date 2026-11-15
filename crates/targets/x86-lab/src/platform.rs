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
    /// A byte string of any kind, handed over where it lies: in data where
    /// it is known before the program runs, and otherwise in the buffer
    /// holding it, which lives until the primitive answers.
    Bytes,
}

impl Takes {
    /// The machine values one source argument becomes, in order. A byte
    /// string becomes two; everything else so far becomes itself.
    #[must_use]
    pub fn classes(self) -> Vec<Class> {
        match self {
            Self::Scalar(class) => vec![class],
            Self::StaticBytes | Self::Bytes => vec![Class::Address, Class::Word],
        }
    }

    /// How many machine values one source argument becomes.
    #[must_use]
    pub const fn width(self) -> usize {
        match self {
            Self::Scalar(_) => 1,
            Self::StaticBytes | Self::Bytes => 2,
        }
    }
}

/// A host call's control-flow and result contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Returns {
    Never,
    Unit,
    Value(Class),
    /// A byte string the primitive the routine is built on filled, and what
    /// the primitive answered: the program holds both.
    Filled,
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
    /// Whether a program asks it with authority: the first argument a
    /// declaration of it takes is what a program was handed to be allowed
    /// to ask, and nothing of it is read. It orders what a program asks and
    /// says who may; a machine hands nothing for it, and handing it over is
    /// not reading what it carries.
    pub authority: bool,
    /// What it reads and what it leaves.
    ///
    /// One entry per argument a program hands it, which is not always one
    /// machine value: [`Takes::StaticBytes`] is two. A token carrying
    /// nothing takes no slot here and is still written at the call, so what
    /// this counts is what a machine reads rather than what a source wrote.
    pub takes: Vec<Takes>,
    pub returns: Returns,
    /// What lowering builds this from, where it is not a routine a target
    /// answers for itself. A target answers only for primitives, which never
    /// see a program's string.
    pub built: Option<Built>,
    /// Whether it uses up what it is handed first: a resource, such as an
    /// open file, of which nothing may be asked afterwards. A type some
    /// routine uses up is a resource, which a program must use up exactly
    /// once; nothing else says what one is.
    pub consumes: bool,
}

/// A routine lowering builds on a primitive.
///
/// Each answers what its primitive does, as the primitive answers it: how
/// many bytes a stream moved, or the descriptor a name opened as, or the
/// error it met that far short of the top of a word, which is how a kernel
/// answers `-errno`. Telling which is the program's to do, so nothing is
/// kept between one call and the next. Every argument but a byte string or
/// the count is handed on as it is, in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Built {
    /// Hand the primitive a byte string where it lies: where its first byte
    /// is and how many bytes it has, whether it was known before the
    /// program ran or worked out since. What the primitive answers.
    Put(String),
    /// Ask the primitive for up to a count of bytes, the last argument,
    /// into a new byte string's buffer, from its first byte: the string of
    /// as many as came, none where the primitive answered an error, and
    /// what the primitive answered.
    Read(String),
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
                Takes::StaticBytes | Takes::Bytes => {
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
            Returns::Unit | Returns::Never | Returns::Filled => None,
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
    contracts: Vec<Routine>,
    startup: Vec<Startup>,
    /// How many bits a host word is, once a target has said.
    word: Option<u16>,
    /// Whether its machine computes IEEE 754 arithmetic itself: see
    /// [`Self::with_floats`].
    floats: bool,
}

impl Routines {
    /// What every compiler knows: the routines a target answers for out of
    /// its own machine, rather than by reaching a name somebody wrote down.
    #[must_use]
    #[expect(
        clippy::too_many_lines,
        reason = "one contract per line, in the order a reader looks for them"
    )]
    pub fn builtin() -> Self {
        let held = |name: &str, (offered, authority), takes: &[Takes], returns, built| Routine {
            name: name.to_owned(),
            offered,
            authority,
            takes: takes.to_vec(),
            returns,
            built,
            consumes: false,
        };
        // What a program asks, it asks with the authority it was handed.
        let offered =
            |name: &str, takes: &[Takes], returns| held(name, (true, true), takes, returns, None);
        // What a descriptor names, a program asks of by holding the
        // descriptor, which the routine reads.
        let described = |name: &str, takes: &[Takes], returns, built: Built| {
            held(name, (true, false), takes, returns, Some(built))
        };
        // A primitive a program's routines are built on is asked with the
        // same authority, though no program names it.
        let primitive =
            |name: &str, takes: &[Takes], returns| held(name, (false, true), takes, returns, None);
        // What a target uses to build what it offers, nobody asks.
        let hidden =
            |name: &str, takes: &[Takes], returns| held(name, (false, false), takes, returns, None);
        let word = Takes::Scalar(Class::Word);
        let count = Returns::Value(Class::Word);
        let contracts = vec![
            // What a descriptor names, bytes where they lie, and a name
            // opened as one: standard input, output and error are the first
            // three. How many bytes moved, or the descriptor, or an error.
            described(
                "fd_put!",
                &[word, Takes::Bytes],
                count,
                Built::Put("write_fd!".into()),
            ),
            described(
                "fd_read!",
                &[word, word],
                Returns::Filled,
                Built::Read("read_fd!".into()),
            ),
            // A name beneath where the program runs, how it is opened, and
            // who may then read or write what it names, where it is made.
            // A target whose kernel reads names up to a nought byte has its
            // host module end the name with one.
            held(
                "fd_open!",
                (true, true),
                &[Takes::Bytes, word, word],
                count,
                Some(Built::Put("open_at!".into())),
            ),
            Routine {
                consumes: true,
                ..held("fd_close!", (true, false), &[word], count, None)
            },
            offered("exit!", &[word], Returns::Never),
            // Bytes where they lie to or from what a descriptor names, and a
            // name opened: how many, or the descriptor, or an error.
            primitive("write_fd!", &[word, Takes::StaticBytes], count),
            primitive(
                "read_fd!",
                &[word, Takes::Scalar(Class::Address), word],
                count,
            ),
            primitive("open_at!", &[Takes::StaticBytes, word, word], count),
            // One argument, two machine values: a machine reads where a run
            // of bytes starts and how long it is.
            primitive("write!", &[Takes::StaticBytes], Returns::Unit),
            // One byte from standard input, offset by one so nought can say
            // EOF without losing the byte whose bits are all nought.
            primitive("read_byte!", &[], Returns::Value(Class::fixed(9))),
            // The kernel picks the address, so nothing asking for a page
            // says where.
            hidden("grow", &[word], Returns::Value(Class::Address)),
        ];
        let startup = vec![
            // How many arguments a program was handed.
            Startup {
                name: "argc".to_owned(),
                class: Class::Word,
            },
            // Where the arguments' addresses lie, one word each, and each
            // argument where its address says, ended by a nought byte.
            Startup {
                name: "argv".to_owned(),
                class: Class::Address,
            },
        ];
        Self {
            contracts,
            startup,
            word: None,
            floats: false,
        }
    }

    /// Resolve the finite range of a host word for a particular target.
    /// The range is a host contract, not a bound on the language's Nat type.
    #[must_use]
    pub fn with_word(mut self, bits: u16) -> Self {
        for routine in &mut self.contracts {
            if routine.returns == Returns::Value(Class::Word) {
                routine.returns = Returns::Value(Class::fixed(bits));
            }
        }
        for value in &mut self.startup {
            if value.class == Class::Word {
                value.class = Class::fixed(bits);
            }
        }
        self.word = Some(bits);
        self
    }

    /// How many bits a host word is, once a target has said.
    #[must_use]
    pub const fn word(&self) -> Option<u16> {
        self.word
    }

    /// Say that the machine computes each [`crate::float::Float`] with an
    /// instruction of its own, correctly rounded to nearest-even and never
    /// trapping, so that a definition claimed to compute one is answered by
    /// the instruction rather than by its body.
    #[must_use]
    pub const fn with_floats(mut self) -> Self {
        self.floats = true;
        self
    }

    /// Whether its machine computes IEEE 754 arithmetic itself.
    #[must_use]
    pub const fn floats(&self) -> bool {
        self.floats
    }

    /// What a sequence's length can be. A sequence is held in memory, and
    /// how many elements it has is a word, so no more than a word holds;
    /// and its buffer's header takes memory too, so fewer than that: one
    /// more than an index into it still fits a word.
    #[must_use]
    pub fn length(&self) -> crate::barb::Bounds {
        let word = held_bounds(self.word.map_or(Class::Word, Class::fixed));
        crate::barb::Bounds {
            high: word.high.map(|high| high - 1),
            ..word
        }
    }

    /// Every routine a program may call by name.
    pub fn offered(&self) -> impl Iterator<Item = &Routine> {
        self.contracts.iter().filter(|routine| routine.offered)
    }

    /// The routine a target answers to by `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Routine> {
        self.contracts.iter().find(|routine| routine.name == name)
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
            contracts: self
                .contracts
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
            word: self.word,
            floats: self.floats,
        }
    }

    /// Take one more in, which is how a routine somebody wrote down arrives.
    pub fn push(&mut self, routine: Routine) {
        self.contracts.push(routine);
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
            Takes::StaticBytes | Takes::Bytes => "a byte string".to_owned(),
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
