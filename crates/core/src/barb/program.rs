//! Program storage, queries, and construction entry points.

use super::budget::Budget;
use super::builder::Builder;
use super::constant::{
    self, Constant, ConstantPool, ConstructionError, DecodeError, Held, Shape, Value,
};
use super::model::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Expr, ExprId, FnId, Function, Parameter, Symbol, Type,
    TypeDefinition, TypeId,
};
use super::terms::TermArena;
use super::types::{TypeInfo, TypeShape};
use crate::index::{Pool, Range, append_range};

/// A program, and the pools every part of it lives in.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub(super) types: Pool<TypeId, Type>,
    pub(super) ctors: Pool<CtorId, Ctor>,
    pub(super) functions: Pool<FnId, Function>,
    pub(super) terms: TermArena,
    /// Field and parameter types.
    pub(super) types_pool: Vec<TypeId>,
    /// Function parameter names and incoming range contracts.
    pub(super) parameters: Vec<Parameter>,
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
pub(crate) fn shape(program: &Program, id: TypeId) -> Shape {
    constant::shape(program.type_info(), id)
}

/// Classify a type for representation selection from its declaration alone.
#[must_use]
pub fn type_shape(program: &Program, id: TypeId) -> TypeShape {
    program.type_info().shape(id)
}

/// The sole constructor and field of a one-field product.
#[must_use]
pub(crate) fn single_field(program: &Program, id: TypeId) -> Option<(CtorId, TypeId)> {
    match type_shape(program, id) {
        TypeShape::Wrapper { constructor, field } => Some((constructor, field)),
        _ => None,
    }
}

/// Peel nested one-field products from an already validated constant.
#[must_use]
pub(crate) fn single_field_constant<'a>(
    program: &'a Program,
    mut value: Constant<'a>,
) -> Constant<'a> {
    let mut budget = Budget::new(super::FoldLimits {
        work: u64::MAX,
        max_bytes: usize::MAX,
        max_depth: program.types().len(),
    });
    while single_field(program, value.owner()).is_some() {
        let super::ConstantView::Constructor(product) = value.view() else {
            unreachable!("a one-field product is constructor encoded")
        };
        let fields = product
            .fields(&mut budget)
            .expect("validated constant fields can be revisited");
        value = fields[0];
    }
    value
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
        self.terms.expr(id)
    }

    /// How many terms the program holds, which is what anything keeping an
    /// answer per term needs.
    #[must_use]
    pub const fn exprs_count(&self) -> usize {
        self.terms.exprs_count()
    }

    /// Put another term where one is. A term is a slot in the arena rather
    /// than something owned, so replacing one is a store and nothing that
    /// named it has to hear about it.
    pub(super) fn write(&mut self, id: ExprId, expr: Expr) {
        self.terms.write(id, expr);
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

    /// Parameter names, in signature order.
    pub fn parameter_names(&self, id: FnId) -> impl Iterator<Item = &str> {
        self.parameters[self.function(id).parameters.range()]
            .iter()
            .map(|parameter| self.name(parameter.name))
    }

    pub(super) fn parameter_bounds(
        &self,
        id: FnId,
    ) -> impl Iterator<Item = Option<super::Bounds>> + '_ {
        self.parameters[self.function(id).parameters.range()]
            .iter()
            .map(|parameter| parameter.bounds)
    }

    #[must_use]
    pub fn bindings(&self, range: Range) -> &[ExprId] {
        self.terms.bindings(range)
    }

    #[must_use]
    pub fn atoms(&self, range: Range) -> &[Atom] {
        self.terms.atoms(range)
    }

    #[must_use]
    pub fn arms(&self, range: Range) -> &[Arm] {
        self.terms.arms(range)
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

    /// Reserve a nominal type. Its constructors follow, so that a field may
    /// name the type being declared.
    pub fn declare_type(&mut self, name: &str) -> TypeId {
        self.declare_type_with_display(name, false)
    }

    /// Reserve a structural type whose diagnostic name is its complete inline
    /// spelling. Rendering omits a redundant top-level declaration.
    pub fn declare_inline_type(&mut self, name: &str) -> TypeId {
        self.declare_type_with_display(name, true)
    }

    fn declare_type_with_display(&mut self, name: &str, inline: bool) -> TypeId {
        let name = self.symbol(name);
        self.types.push(Type {
            name,
            inline,
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
        let names: Vec<_> = (0..params.len()).map(|at| format!("v{at}")).collect();
        let params: Vec<_> = names
            .iter()
            .zip(params)
            .map(|(name, &ty)| (name.as_str(), ty))
            .collect();
        self.declare_named(name, &params, result)
    }

    /// Declare a function with source-level parameter names.
    pub fn declare_named(&mut self, name: &str, params: &[(&str, TypeId)], result: TypeId) -> FnId {
        let name = self.symbol(name);
        let types: Vec<_> = params.iter().map(|(_, ty)| *ty).collect();
        let types = append_range(&mut self.types_pool, &types);
        let names: Vec<_> = params
            .iter()
            .map(|(parameter, _)| self.symbol(parameter))
            .collect();
        let start = self.parameters.len();
        self.parameters.extend(
            names
                .into_iter()
                .map(|name| Parameter { name, bounds: None }),
        );
        let parameters = Range::of(start, params.len());
        self.functions.push(Function {
            name,
            params: types,
            parameters,
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

    /// Supply the range promised for one incoming parameter.
    ///
    /// # Panics
    /// If `at` is outside the function signature.
    pub fn bound_parameter(&mut self, id: FnId, at: usize, bounds: super::Bounds) {
        let range = self.functions[id].parameters;
        assert!(at < range.len(), "parameter outside the function signature");
        self.parameters[range.range().start + at].bounds = Some(bounds);
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

    /// Encode bytes as a spine whose one element field is a natural.
    ///
    /// # Errors
    /// If the owner is undefined or does not have that structural shape.
    pub fn intern_byte_spine(
        &mut self,
        owner: TypeId,
        bytes: &[u8],
    ) -> Result<ConstId, ConstructionError> {
        let (types, pool) = self.constant_parts();
        pool.byte_spine(types, owner, bytes)
    }

    pub(super) fn intern_held(&mut self, value: &Held) -> ConstId {
        self.constants.intern_held(value)
    }

    /// Publish roots only after a pass has finished reading the original bodies.
    pub(super) fn replace_bodies(&mut self, bodies: Vec<(FnId, Body)>) {
        for (id, body) in bodies {
            self.functions[id].define(body);
        }
    }

    /// Install a rebuilt arena and its roots without moving declarations or constants.
    /// The rebuilder must supply every defined function's remapped body; old term
    /// IDs, ranges and expression-indexed analyses are invalid after this operation.
    pub(super) fn replace_terms(&mut self, terms: TermArena, bodies: Vec<(FnId, Body)>) {
        self.terms = terms;
        self.replace_bodies(bodies);
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
