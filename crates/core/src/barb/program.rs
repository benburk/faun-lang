//! Program storage, queries, and construction entry points.

use std::borrow::Cow;
use std::collections::HashMap;

use super::budget::Budget;
use super::builder::Builder;
use super::constant::{self, Constant, ConstantPool, ConstructionError, Held, Shape, Value};
use super::facts::{Facts, Recognised};
use super::model::{
    Arm, Atom, Body, ConstId, Ctor, CtorId, Expr, ExprId, Field, FieldDetail, FnId, Function,
    Parameter, Symbol, Type, TypeDefinition, TypeId,
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
    /// Function parameter names.
    pub(super) parameters: Vec<Parameter>,
    /// Constructor field names.
    pub(super) field_details: Vec<FieldDetail>,
    /// Known values, encoded. See [`super::constant`].
    pub(super) constants: ConstantPool,
    /// Every name the program uses, each once, end to end. A [`Symbol`] is
    /// an index into `symbols`, which says where in here its characters are,
    /// so naming something allocates nothing.
    pub(super) names: Vec<u8>,
    pub(super) symbols: Pool<Symbol, Range>,
    /// Each name's symbol, by its characters, so that naming something
    /// again finds it without reading every name before it.
    spelled: Derived<HashMap<Box<str>, Symbol>>,
    pub(super) entry: Option<FnId>,
    /// Which functions are recognised equations, one entry per function once
    /// worked out. Rewriting a body keeps what it means, so this outlives
    /// every optimization; only defining a body or a type forgets it.
    recognised: Derived<Recognised>,
}

/// What was worked out from a program rather than said by it. Two programs
/// saying the same thing are equal whatever either has worked out so far.
#[derive(Clone, Debug, Default)]
struct Derived<T>(T);

impl<T> PartialEq for Derived<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<T> Eq for Derived<T> {}

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
pub fn single_field(program: &Program, id: TypeId) -> Option<(CtorId, TypeId)> {
    match type_shape(program, id) {
        TypeShape::Wrapper { constructor, field } => Some((constructor, field)),
        _ => None,
    }
}

/// Peel nested one-field products from an already validated constant.
///
/// # Panics
/// If the constant does not have the validated encoding for its type.
#[must_use]
pub fn single_field_constant<'a>(program: &'a Program, mut value: Constant<'a>) -> Constant<'a> {
    let mut budget = Budget::new(super::FoldLimits {
        work: u64::MAX,
        work_per_function: u64::MAX,
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

    /// Which functions are recognised equations or questions about a
    /// sequence, by function: worked out the first time anything asks, and
    /// kept while bodies are only rewritten.
    pub(super) fn recognised(&mut self) -> &Recognised {
        if !self.recognition_kept() {
            self.recognised.0 = self.recognise();
        }
        &self.recognised.0
    }

    /// The same, for a reader: what was kept where it still holds, and
    /// otherwise worked out afresh and not kept.
    fn recognition(&self) -> Cow<'_, Recognised> {
        if self.recognition_kept() {
            Cow::Borrowed(&self.recognised.0)
        } else {
            Cow::Owned(self.recognise())
        }
    }

    /// Whether what was recognised was recognised of these functions: no
    /// function has been added or taken away since, and nothing redefined.
    const fn recognition_kept(&self) -> bool {
        self.recognised.0.operations.len() == self.functions.len()
    }

    fn recognise(&self) -> Recognised {
        let operations = super::arithmetic::recognise(self);
        let sequences = super::arithmetic::recognise_sequences(self, &operations);
        let floats = self
            .functions
            .iter()
            .map(|function| function.float)
            .collect();
        Recognised {
            operations,
            sequences,
            floats,
        }
    }

    /// What every term, parameter, result and field can hold, as the
    /// program alone says.
    #[must_use]
    pub fn analyze(&self) -> Facts {
        self.assuming(&super::Assumed::default())
    }

    /// What analysis finds when values from outside the program are what
    /// `assumed` says. The tier that knows a target asks this.
    #[must_use]
    pub fn assuming(&self, assumed: &super::Assumed) -> Facts {
        super::facts::analyze(self, self.recognition().into_owned(), assumed)
    }

    /// Forget what was recognised of this program: a declaration or a body
    /// now says something it did not.
    pub(super) fn redefined(&mut self) {
        self.recognised.0 = Recognised::default();
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
        if let Some(&id) = self.spelled.0.get(name) {
            return id;
        }
        let at = append_range(&mut self.names, name.as_bytes());
        let id = self.symbols.push(at);
        self.spelled.0.insert(name.into(), id);
        id
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
        self.redefined();
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
        let fields: Vec<Vec<Field>> = ctors
            .iter()
            .map(|(_, fields)| fields.iter().copied().map(Field::of).collect())
            .collect();
        let ctors: Vec<_> = ctors
            .iter()
            .zip(&fields)
            .map(|((name, _), fields)| (*name, fields.as_slice()))
            .collect();
        self.define_fields(id, &ctors);
    }

    /// Define a type whose constructors' fields may be named.
    ///
    /// # Panics
    /// If the type is already defined, or a field's type is not declared.
    pub fn define_fields(&mut self, id: TypeId, ctors: &[(&str, &[Field])]) {
        assert_eq!(
            self.types[id].definition,
            TypeDefinition::Declared,
            "type definitions are immutable"
        );
        for (_, fields) in ctors {
            for field in *fields {
                assert!(self.types.get(field.ty).is_some(), "a declared field type");
            }
        }
        self.redefined();
        let start = self.ctors.len();
        for (name, fields) in ctors {
            let name = self.symbol(name);
            let types: Vec<_> = fields.iter().map(|field| field.ty).collect();
            let details: Vec<_> = fields
                .iter()
                .map(|field| FieldDetail {
                    name: field.name.map(|name| self.symbol(name)),
                })
                .collect();
            let fields = append_range(&mut self.types_pool, &types);
            let details = append_range(&mut self.field_details, &details);
            self.ctors.push(Ctor {
                name,
                owner: id,
                fields,
                details,
            });
        }
        self.types[id].definition = TypeDefinition::Defined(Range::of(start, ctors.len()));
    }

    /// Each field's name, in order, where its definition gave one.
    pub(super) fn field_names(&self, ctor: &Ctor) -> impl Iterator<Item = Option<&str>> + '_ {
        self.field_details[ctor.details.range()]
            .iter()
            .map(|detail| detail.name.map(|name| self.name(name)))
    }

    /// What field `at` of `ctor` is called, if its definition named it.
    #[must_use]
    pub fn field_name(&self, ctor: CtorId, at: usize) -> Option<&str> {
        let detail = self.field_details[self.ctor(ctor).details.range()].get(at)?;
        detail.name.map(|name| self.name(name))
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
        self.redefined();
        let name = self.symbol(name);
        let types: Vec<_> = params.iter().map(|(_, ty)| *ty).collect();
        let types = append_range(&mut self.types_pool, &types);
        let names: Vec<_> = params
            .iter()
            .map(|(parameter, _)| self.symbol(parameter))
            .collect();
        let start = self.parameters.len();
        self.parameters
            .extend(names.into_iter().map(|name| Parameter { name }));
        let parameters = Range::of(start, params.len());
        self.functions.push(Function {
            name,
            params: types,
            parameters,
            result,
            definition: super::Definition::External { symbol: name },
            float: None,
        })
    }

    /// Say that `id`'s body computes `float` on the patterns its parameters
    /// hold, as the program building it knows and nothing here can check:
    /// no equation says what an IEEE 754 operation is. The body stays, and
    /// answers wherever nothing faster does -- the evaluator, a target with
    /// no float instructions -- so a claim that is wrong is a program whose
    /// answer depends on its target; validation checks only its shape.
    ///
    /// A claimed definition is treated as a recognized one: passes neither
    /// rewrite nor inline it, folding answers a call of it from its
    /// operands, and cleanup treats its calls as inert.
    pub fn claim(&mut self, id: FnId, float: crate::float::Float) {
        self.redefined();
        self.functions[id].float = Some(float);
    }

    /// Forget every claim, so that each claimed definition answers by its
    /// body wherever it is called: how a body is checked against what was
    /// claimed of it.
    pub fn disclaim(&mut self) {
        self.redefined();
        for function in &mut self.functions {
            function.float = None;
        }
    }

    /// Say what answers for a declaration out there, where a program calls
    /// it by another name. Two declarations may name the same one, which is
    /// how a program reaches it at more than one type.
    ///
    /// # Panics
    /// If the function already has a body.
    pub fn answered_by(&mut self, id: FnId, name: &str) {
        self.redefined();
        let name = self.symbol(name);
        let super::Definition::External { symbol, .. } = &mut self.functions[id].definition else {
            panic!("only an external declaration can name a provider");
        };
        *symbol = name;
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

    /// Encode bytes as a spine whose one element field is a natural, or wraps one.
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
        self.redefined();
        let arity = u32::try_from(self.params(id).len()).expect("a sane arity");
        let body = Builder::build(self, arity, build);
        self.functions[id].define(body);
    }
}
