//! Program storage, queries, and construction entry points.

use super::budget::Budget;
use super::builder::Builder;
use super::constant::{
    self, Constant, ConstantPool, ConstructionError, DecodeError, Held, Shape, Value,
};
use super::model::{
    Arm, Atom, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Symbol, Type, TypeDefinition,
    TypeId,
};
use super::types::TypeInfo;
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
    pub(super) constants: ConstantPool,
    /// Every name the program uses, each once, end to end. A [`Symbol`] is
    /// an index into `symbols`, which says where in here its characters are,
    /// so naming something allocates nothing.
    pub(super) names: Vec<u8>,
    pub(super) symbols: Pool<Symbol, Range>,
    pub(super) entry: Option<FnId>,
}

/// How a type's constants are encoded, derived from its declaration.
#[must_use]
pub fn shape(program: &Program, id: TypeId) -> Shape {
    constant::shape(program.type_info(), id)
}

impl Program {
    pub(super) fn type_info(&self) -> TypeInfo<'_> {
        TypeInfo::new(&self.types, &self.ctors, &self.types_pool)
    }

    // Keep the pool paired with this program's declarations while splitting the
    // mutable storage borrow from immutable metadata. No public schema argument.
    fn constant_parts(&mut self) -> (TypeInfo<'_>, &mut ConstantPool) {
        (
            TypeInfo::new(&self.types, &self.ctors, &self.types_pool),
            &mut self.constants,
        )
    }

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
        self.type_info().ctors(id)
    }

    /// Where `ctor` sits among its type's constructors, which is the tag a
    /// known value carries.
    #[must_use]
    pub fn tag(&self, ctor: CtorId) -> u32 {
        self.type_info().tag(ctor)
    }

    #[must_use]
    pub fn ctor_at(&self, owner: TypeId, tag: u32) -> CtorId {
        self.type_info().ctor_at(owner, tag)
    }

    /// The types a range of the pool holds.
    #[must_use]
    pub fn types_of(&self, range: Range) -> &[TypeId] {
        &self.types_pool[range.range()]
    }

    #[must_use]
    pub fn fields(&self, ctor: CtorId) -> &[TypeId] {
        self.type_info().fields(ctor)
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
        self.constants.bytes(id)
    }

    /// A constant carries its own type; callers cannot reinterpret its bytes.
    #[must_use]
    pub fn constant(&self, value: ConstId) -> Constant<'_> {
        self.constants.get(self.type_info(), value)
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
            definition: TypeDefinition::Declared,
        })
    }

    /// Give a reserved type its constructors, once, in tag order.
    ///
    /// # Panics
    /// If the type was already defined, a field is undeclared, or a pool overflows.
    pub fn define_type(&mut self, id: TypeId, ctors: &[(&str, &[TypeId])]) {
        assert_eq!(
            self.types[id].definition,
            TypeDefinition::Declared,
            "type definitions are immutable"
        );
        for (_, fields) in ctors {
            for field in *fields {
                assert!(self.types.get(*field).is_some(), "a declared field type");
            }
        }
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
        self.types[id].definition = TypeDefinition::Defined(Range::of(start, ctors.len()));
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

    /// Validate and encode a constructor tree.
    ///
    /// # Errors
    /// If its constructors, field counts or field types do not match declarations.
    pub fn intern(&mut self, id: TypeId, value: &Value) -> Result<ConstId, ConstructionError> {
        let (types, pool) = self.constant_parts();
        pool.intern(types, id, value)
    }

    /// Import exactly one encoded value without expanding its constructor tree.
    ///
    /// # Errors
    /// If the encoding is malformed, has trailing bytes, or exceeds the budget.
    pub fn decode_constant(
        &mut self,
        owner: TypeId,
        bytes: &[u8],
        budget: &mut Budget,
    ) -> Result<ConstId, DecodeError> {
        let (types, pool) = self.constant_parts();
        pool.decode(types, owner, bytes, budget)
    }

    /// Construct a constant from other constants in this program.
    ///
    /// # Errors
    /// If the fields do not match the constructor, or the budget is exhausted.
    pub fn construct(
        &mut self,
        ctor: CtorId,
        fields: &[ConstId],
        budget: &mut Budget,
    ) -> Result<ConstId, ConstructionError> {
        let (types, pool) = self.constant_parts();
        pool.construct(types, ctor, fields, budget)
    }

    /// Encode a number directly, without building its unary constructor chain.
    ///
    /// # Errors
    /// If the type is undefined or is not a natural-number shape.
    pub fn intern_number(&mut self, id: TypeId, value: u64) -> Result<ConstId, ConstructionError> {
        let (types, pool) = self.constant_parts();
        pool.number(types, id, value)
    }

    /// Encode an arbitrary-precision natural without constructing its spine.
    ///
    /// # Errors
    /// If the type is undefined or is not a natural-number shape.
    pub fn intern_natural(
        &mut self,
        id: TypeId,
        value: &num_bigint::BigUint,
    ) -> Result<ConstId, ConstructionError> {
        let (types, pool) = self.constant_parts();
        pool.natural(types, id, value)
    }

    pub(super) fn intern_held(&mut self, value: &Held) -> ConstId {
        self.constants.intern_held(value)
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
