//! Program storage, queries, and construction entry points.

use super::builder::Builder;
use super::constant::{self, Shape, Value};
use super::model::{
    Arm, Atom, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Symbol, Type, TypeId,
};
use crate::index::{Pool, Range, append_range};

/// A program, and the pools every part of it lives in.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub(super) types: Pool<TypeId, Type>,
    pub(super) ctors: Pool<CtorId, Ctor>,
    pub(super) functions: Pool<FnId, Function>,
    /// The term arena.
    pub(super) exprs: Pool<ExprId, Expr>,
    /// Argument lists, for `Con` and `Call`.
    pub(super) atoms: Vec<Atom>,
    /// The bindings of every body, each run contiguous.
    pub(super) bindings: Vec<ExprId>,
    pub(super) arms: Vec<Arm>,
    /// Field and parameter types.
    pub(super) types_pool: Vec<TypeId>,
    /// Known values, encoded. See [`super::constant`].
    pub(super) consts: Pool<ConstId, Range>,
    pub(super) bytes: Vec<u8>,
    /// Every name the program uses, each once, end to end. A [`Symbol`] is
    /// an index into `symbols`, which says where in here its characters are,
    /// so naming something allocates nothing.
    pub(super) names: Vec<u8>,
    pub(super) symbols: Pool<Symbol, Range>,
    pub(super) entry: Option<FnId>,
}

impl Program {
    /// The name a symbol stands for.
    ///
    /// # Panics
    ///
    /// If the symbol came from another program.
    #[must_use]
    pub fn name(&self, symbol: Symbol) -> &str {
        let at = self.symbols[symbol];
        std::str::from_utf8(&self.names[at.range()]).expect("a name was written as text")
    }

    #[must_use]
    pub fn type_(&self, id: TypeId) -> &Type {
        &self.types[id]
    }

    #[must_use]
    pub fn ctor(&self, id: CtorId) -> &Ctor {
        &self.ctors[id]
    }

    #[must_use]
    pub fn function(&self, id: FnId) -> &Function {
        &self.functions[id]
    }

    #[must_use]
    pub fn expr(&self, id: ExprId) -> Expr {
        self.exprs[id]
    }

    /// How many terms the program holds, which is what anything keeping an
    /// answer per term needs.
    #[must_use]
    pub const fn exprs_count(&self) -> usize {
        self.exprs.len()
    }

    /// Put another term where one is. A term is a slot in the arena rather
    /// than something owned, so replacing one is a store and nothing that
    /// named it has to hear about it.
    pub(super) fn write(&mut self, id: ExprId, expr: Expr) {
        self.exprs[id] = expr;
    }

    #[must_use]
    pub fn ctors(&self, id: TypeId) -> &[Ctor] {
        &self.ctors.as_slice()[self.type_(id).ctors.range()]
    }

    /// Where `ctor` sits among its type's constructors, which is the tag a
    /// known value carries.
    #[must_use]
    pub fn tag(&self, ctor: CtorId) -> u32 {
        ctor.0 - self.type_(self.ctor(ctor).owner).ctors.start()
    }

    #[must_use]
    pub fn ctor_at(&self, owner: TypeId, tag: u32) -> CtorId {
        CtorId(self.type_(owner).ctors.start() + tag)
    }

    /// The types a range of the pool holds.
    #[must_use]
    pub fn types_of(&self, range: Range) -> &[TypeId] {
        &self.types_pool[range.range()]
    }

    #[must_use]
    pub fn fields(&self, ctor: CtorId) -> &[TypeId] {
        &self.types_pool[self.ctor(ctor).fields.range()]
    }

    #[must_use]
    pub fn params(&self, id: FnId) -> &[TypeId] {
        &self.types_pool[self.function(id).params.range()]
    }

    #[must_use]
    pub fn bindings(&self, range: Range) -> &[ExprId] {
        &self.bindings[range.range()]
    }

    #[must_use]
    pub fn atoms(&self, range: Range) -> &[Atom] {
        &self.atoms[range.range()]
    }

    #[must_use]
    pub fn arms(&self, range: Range) -> &[Arm] {
        &self.arms[range.range()]
    }

    #[must_use]
    pub fn known_bytes(&self, id: ConstId) -> &[u8] {
        &self.bytes[self.consts[id].range()]
    }

    #[must_use]
    pub const fn entry(&self) -> Option<FnId> {
        self.entry
    }

    #[must_use]
    pub fn types(&self) -> &[Type] {
        self.types.as_slice()
    }

    #[must_use]
    pub fn functions(&self) -> &[Function] {
        self.functions.as_slice()
    }
}

impl Program {
    /// The symbol for `name`, the same symbol every time.
    ///
    /// A scan rather than a table beside it. This runs once per declaration
    /// and nowhere else: nothing here mints a name, since specialisation
    /// happens above this tier, so the cost is over what a program declares
    /// rather than over its terms. Reading one back is an index and a slice.
    ///
    /// # Panics
    ///
    /// If the program outgrew the names it may have.
    pub fn symbol(&mut self, name: &str) -> Symbol {
        let held = |at: &Range| &self.names[at.range()] == name.as_bytes();
        if let Some(id) = self.symbols.position(held) {
            return id;
        }
        let name = append_range(&mut self.names, name.as_bytes());
        self.symbols.push(name)
    }

    /// Reserve a type. Its constructors follow, so that a field may name the
    /// type being declared.
    pub fn declare_type(&mut self, name: &str) -> TypeId {
        let name = self.symbol(name);
        self.types.push(Type {
            name,
            ctors: Range::default(),
        })
    }

    /// Give a reserved type its constructors, in tag order.
    ///
    /// # Panics
    ///
    /// If the program outgrew the pools it may have.
    pub fn define_type(&mut self, id: TypeId, ctors: &[(&str, &[TypeId])]) {
        let start = self.ctors.len();
        for (name, fields) in ctors {
            let name = self.symbol(name);
            let fields = append_range(&mut self.types_pool, fields);
            self.ctors.push(Ctor {
                name,
                owner: id,
                fields,
            });
        }
        self.types[id].ctors = Range::of(start, ctors.len());
    }

    /// # Panics
    ///
    /// If the program outgrew the pools it may have.
    pub fn declare(&mut self, name: &str, params: &[TypeId], result: TypeId) -> FnId {
        let name = self.symbol(name);
        let params = append_range(&mut self.types_pool, params);
        self.functions.push(Function {
            name,
            params,
            result,
            definition: super::Definition::External {
                symbol: name,
                bounds: None,
            },
        })
    }

    /// Say what answers for a declaration out there, where a program calls
    /// it by another name. Two declarations may name the same one, which is
    /// how a program reaches it at more than one type.
    ///
    /// # Panics
    /// If the function already has a body.
    pub fn answered_by(&mut self, id: FnId, name: &str) {
        let name = self.symbol(name);
        let super::Definition::External { symbol, .. } = &mut self.functions[id].definition else {
            panic!("only an external declaration can name a provider");
        };
        *symbol = name;
    }

    /// Supply a range contract for a declaration implemented outside Barb.
    ///
    /// # Panics
    /// If the function already has a body.
    pub fn bound(&mut self, id: FnId, bounds: super::Bounds) {
        let super::Definition::External {
            bounds: contract, ..
        } = &mut self.functions[id].definition
        else {
            panic!("only an external declaration can carry a range contract");
        };
        *contract = Some(bounds);
    }

    /// The function a target enters.
    pub const fn set_entry(&mut self, id: FnId) {
        self.entry = Some(id);
    }

    /// Encode a known value into the pool.
    ///
    /// # Panics
    ///
    /// If `value` is not of type `id`.
    pub fn intern(&mut self, id: TypeId, value: &Value) -> ConstId {
        self.hold(|program, out| {
            constant::encode(program, id, value, out);
        })
    }

    /// A number, written straight into the pool. The chain of constructors
    /// it stands for is never built, which for a large one is the difference
    /// between a few bytes and its own magnitude.
    ///
    /// # Panics
    ///
    /// If `id` is not a number: a spine whose elements carry nothing.
    pub fn intern_number(&mut self, id: TypeId, value: u64) -> ConstId {
        let name = self.type_(id).name;
        let Shape::Spine { cons, .. } = constant::shape(self, id) else {
            panic!("`{}` is not a number", self.name(name));
        };
        assert_eq!(
            self.fields(cons).len(),
            1,
            "`{}` carries something per element",
            self.name(name)
        );
        self.hold(|_, out| constant::write_number(value, out))
    }

    /// An arbitrary-precision natural, encoded without constructing its spine.
    ///
    /// # Panics
    /// If `id` is not a natural-number shape.
    pub fn intern_natural(&mut self, id: TypeId, value: &num_bigint::BigUint) -> ConstId {
        assert!(
            super::arithmetic::natural(self, id).is_some(),
            "a natural type"
        );
        self.hold(|_, out| constant::write_natural(value, out))
    }

    pub(super) fn intern_encoded(&mut self, bytes: &[u8]) -> ConstId {
        self.hold(|_, out| out.extend_from_slice(bytes))
    }

    /// Write into the pool itself, so that nothing is encoded into a buffer
    /// and then copied in.
    fn hold(&mut self, write: impl FnOnce(&Self, &mut Vec<u8>)) -> ConstId {
        let mut bytes = std::mem::take(&mut self.bytes);
        let start = bytes.len();
        write(self, &mut bytes);
        let len = bytes.len() - start;
        self.bytes = bytes;
        self.consts.push(Range::of(start, len))
    }

    /// Build a declared function's body. Its parameters are the first locals.
    ///
    /// # Panics
    ///
    /// If the function takes more parameters than the tier allows.
    pub fn define(&mut self, id: FnId, build: impl FnOnce(&mut Builder, &[Atom]) -> Atom) {
        let arity = u32::try_from(self.params(id).len()).expect("a sane arity");
        let body = Builder::build(self, arity, build);
        self.functions[id].define(body);
    }
}
