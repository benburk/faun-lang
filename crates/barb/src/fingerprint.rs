//! What a definition is, as a number: its body and everything it reaches,
//! with no name or ID in it.
//!
//! A definition is written out together with every definition it calls and
//! every type it touches, each numbered in the order it is first met, so
//! two programs that hold the same code -- however its declarations were
//! named, numbered or interleaved with others -- write out the same stream.
//! A type is written as its constructors' fields, a constructor as its type
//! and tag, a known value as its type and its encoding, which is itself
//! structural, and a call of something already written as its number, which
//! is how recursion closes. The stream is hashed with 128-bit FNV-1a, which
//! is fixed and needs no dependency.
//!
//! Equal code has equal fingerprints. Distinct code sharing one is a 128-bit
//! accident, and a definition answered by its fingerprint keeps its body,
//! which a target without the instruction walks.

use rustc_hash::FxHashMap as HashMap;

use super::model::TypeDefinition;
use super::{Atom, Body, CtorId, Expr, FnId, Program, TypeId};

/// The most expressions a definition and what it reaches may hold for a
/// fingerprint to be taken: more is not a definition worth naming.
const WORK: usize = 200_000;

/// `id`'s fingerprint, or nothing where it reaches a definition with no
/// body or a type not yet defined, or holds more than 200,000 expressions.
#[must_use]
pub fn fingerprint(program: &Program, id: FnId) -> Option<u128> {
    let mut writer = Writer {
        program,
        hash: Fnv::new(),
        functions: HashMap::default(),
        pending_functions: Vec::new(),
        types: HashMap::default(),
        pending_types: Vec::new(),
        work: WORK,
    };
    writer.function_ref(id);
    let mut next = 0;
    while next < writer.pending_functions.len() {
        let id = writer.pending_functions[next];
        writer.function(id)?;
        next += 1;
    }
    let mut next = 0;
    while next < writer.pending_types.len() {
        let ty = writer.pending_types[next];
        writer.type_(ty)?;
        next += 1;
    }
    Some(writer.hash.0)
}

struct Writer<'a> {
    program: &'a Program,
    hash: Fnv,
    functions: HashMap<FnId, u32>,
    pending_functions: Vec<FnId>,
    types: HashMap<TypeId, u32>,
    pending_types: Vec<TypeId>,
    work: usize,
}

impl Writer<'_> {
    fn function_ref(&mut self, id: FnId) {
        let next = u32::try_from(self.functions.len()).expect("fewer than 2^32 definitions");
        let number = *self.functions.entry(id).or_insert_with(|| {
            self.pending_functions.push(id);
            next
        });
        self.hash.number(u64::from(number));
    }

    fn type_ref(&mut self, ty: TypeId) {
        let next = u32::try_from(self.types.len()).expect("fewer than 2^32 types");
        let number = *self.types.entry(ty).or_insert_with(|| {
            self.pending_types.push(ty);
            next
        });
        self.hash.number(u64::from(number));
    }

    fn ctor_ref(&mut self, ctor: CtorId) {
        self.type_ref(self.program.ctor(ctor).owner);
        self.hash.number(u64::from(self.program.tag(ctor)));
    }

    fn atoms(&mut self, atoms: &[Atom]) {
        self.hash.count(atoms.len());
        for atom in atoms {
            self.hash.count(atom.0.index());
        }
    }

    fn function(&mut self, id: FnId) -> Option<()> {
        let function = self.program.function(id);
        let body = function.body()?;
        let params = self.program.params(id);
        self.hash.count(params.len());
        for &ty in params {
            self.type_ref(ty);
        }
        self.type_ref(function.result);
        self.body(body)
    }

    fn body(&mut self, body: Body) -> Option<()> {
        let bindings = self.program.bindings(body.bindings);
        self.hash.count(bindings.len());
        for &binding in bindings {
            self.expr(self.program.expr(binding))?;
        }
        self.expr(self.program.expr(body.tail))
    }

    fn expr(&mut self, expr: Expr) -> Option<()> {
        self.work = self.work.checked_sub(1)?;
        match expr {
            Expr::Atom(atom) => {
                self.hash.number(0);
                self.hash.count(atom.0.index());
            }
            Expr::Con(ctor, fields) => {
                self.hash.number(1);
                self.ctor_ref(ctor);
                self.atoms(self.program.atoms(fields));
            }
            Expr::Static(value) => {
                self.hash.number(2);
                let constant = self.program.constant(value);
                self.type_ref(constant.owner());
                let encoded = constant.encoded();
                self.hash.count(encoded.len());
                self.hash.bytes(encoded);
            }
            Expr::Call(called, args) => {
                self.hash.number(3);
                self.function_ref(called);
                self.atoms(self.program.atoms(args));
            }
            Expr::Match(scrutinee, arms) => {
                self.hash.number(4);
                self.hash.count(scrutinee.0.index());
                let arms = self.program.arms(arms);
                self.hash.count(arms.len());
                for arm in arms {
                    self.ctor_ref(arm.ctor);
                    self.body(arm.body)?;
                }
            }
        }
        Some(())
    }

    fn type_(&mut self, ty: TypeId) -> Option<()> {
        let TypeDefinition::Defined(ctors) = self.program.type_(ty).definition else {
            return None;
        };
        self.hash.count(ctors.len());
        for at in 0..ctors.len() {
            let ctor = self.program.ctor_at(ty, u32::try_from(at).ok()?);
            let fields = self.program.fields(ctor);
            self.hash.count(fields.len());
            for &field in fields {
                self.type_ref(field);
            }
        }
        Some(())
    }
}

/// 128-bit FNV-1a.
struct Fnv(u128);

impl Fnv {
    const OFFSET: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;

    const fn new() -> Self {
        Self(Self::OFFSET)
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.0 ^= u128::from(byte);
            self.0 = self.0.wrapping_mul(Self::PRIME);
        }
    }

    fn number(&mut self, number: u64) {
        self.bytes(&number.to_le_bytes());
    }

    /// A count or an index, written as the `u64` it is on every host.
    fn count(&mut self, count: usize) {
        self.number(u64::try_from(count).expect("a count fits in 64 bits"));
    }
}
