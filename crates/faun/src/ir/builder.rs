//! Scoped construction of instruction regions.
//!
//! [`Program::define`] and [`Program::try_define`] start construction; this
//! module owns the temporary instructions, results, and transfer state.

use super::model::{
    Binary, Class, DataId, Exit, FunctionId, Offset, Op, Range, Region, RegionId, Relation,
    Terminator, ValueId, Width, wrap,
};
use super::program::Program;

/// Accumulates one region.
///
/// Its instructions are appended to the program only when the region is
/// finished, which is what keeps a region's run of them contiguous while
/// nested regions are being built inside it.
#[derive(Debug)]
pub struct Builder<'a> {
    program: &'a mut Program,
    params: Range,
    ops: Vec<Op>,
    results: Vec<Range>,
    terminator: Option<Terminator>,
}

impl Builder<'_> {
    /// Build a root region using its already-reserved parameter values.
    pub(super) fn build<E>(
        program: &mut Program,
        entry: Range,
        build: impl FnOnce(&mut Builder, &[ValueId]) -> Result<(), E>,
    ) -> Result<Region, E> {
        let params = program.values(entry).to_vec();
        let mut builder = Builder {
            program,
            params: entry,
            ops: Vec::new(),
            results: Vec::new(),
            terminator: None,
        };
        build(&mut builder, &params)?;
        Ok(builder.finish())
    }

    /// What class a value has, for a decision that has to be made before
    /// the values it is about are built -- an `if` is told what its arms
    /// leave with before either arm is lowered.
    #[must_use]
    pub fn class(&self, value: ValueId) -> Class {
        self.program.class(value)
    }

    /// The classes a function's parameters were declared at, which is what
    /// a call to it hands over.
    #[must_use]
    pub fn takes(&self, function: FunctionId) -> &[Class] {
        self.program
            .signature(self.program.functions[function].params)
    }

    pub fn constant(&mut self, class: Class, value: u64) -> ValueId {
        let value = wrap(class, value);
        self.push_one(Op::Constant { class, value }, class)
    }

    /// An arbitrary-precision constant, kept compactly in the data pool.
    pub fn natural(&mut self, value: &num_bigint::BigUint) -> ValueId {
        let data = self.program.intern(&value.to_bytes_le());
        self.push_one(Op::NaturalConstant(data), Class::Natural)
    }

    pub fn address_of(&mut self, data: DataId) -> ValueId {
        self.push_one(Op::AddressOf(data), Class::Address)
    }

    pub fn data_len(&mut self, data: DataId) -> ValueId {
        let len = self.program.datum(data).len;
        self.constant(Class::Word, u64::from(len))
    }

    /// As wide as its left operand, which is what a program building its own
    /// IR means by an operation on two values of one width.
    pub fn binary(&mut self, op: Binary, left: ValueId, right: ValueId) -> ValueId {
        let class = self.program.class(left);
        self.binary_at(class, op, left, right)
    }

    /// And at a width said outright, for a tier that worked out what the
    /// answer can be before working out what reads it: two and two are two
    /// bits each and four is three.
    pub fn binary_at(
        &mut self,
        class: Class,
        op: Binary,
        left: ValueId,
        right: ValueId,
    ) -> ValueId {
        self.push_one(Op::Binary { op, left, right }, class)
    }

    pub fn compare(&mut self, relation: Relation, left: ValueId, right: ValueId) -> ValueId {
        let op = Op::Compare {
            relation,
            left,
            right,
        };
        self.push_one(op, Class::Word)
    }

    pub fn load(&mut self, width: Width, address: ValueId, offset: Offset) -> ValueId {
        let op = Op::Load {
            width,
            address,
            offset,
        };
        self.push_one(op, Class::Word)
    }

    pub fn store(&mut self, width: Width, address: ValueId, offset: Offset, value: ValueId) {
        let op = Op::Store {
            width,
            address,
            offset,
            value,
        };
        self.push(op, &[]);
    }

    pub fn convert(&mut self, class: Class, value: ValueId) -> ValueId {
        self.push_one(Op::Convert { class, value }, class)
    }

    pub fn call(&mut self, function: FunctionId, args: &[ValueId]) -> Vec<ValueId> {
        let returns = self.program.functions[function].returns.classes();
        let args = self.program.hold(args);
        self.push_from(Op::Call { function, args }, returns)
    }

    /// Call a function declared to return exactly one value, without building
    /// a temporary result vector. The result class comes from its signature.
    /// Argument and control-flow validity are still checked by validation.
    ///
    /// # Panics
    /// If the function ID is invalid, the region already has an explicit
    /// transfer, or the signature has zero/multiple results or never returns.
    /// Result-arity rejection happens before appending call operands or values.
    pub fn call_one(&mut self, function: FunctionId, args: &[ValueId]) -> ValueId {
        self.open();
        let returns = self.program.function(function).returns.classes();
        let &[class] = self.program.signature(returns) else {
            panic!("call_one requires exactly one result");
        };
        let args = self.program.hold(args);
        self.push_one(Op::Call { function, args }, class)
    }

    pub fn if_(
        &mut self,
        condition: ValueId,
        results: &[Class],
        then: impl FnOnce(&mut Builder),
        otherwise: impl FnOnce(&mut Builder),
    ) -> Vec<ValueId> {
        let then_region = self.region(&[], |builder, _| then(builder));
        let else_region = self.region(&[], |builder, _| otherwise(builder));
        let op = Op::If {
            condition,
            then_region,
            else_region,
        };
        self.push(op, results)
    }

    /// The body runs with `initial`, then with whatever each `Continue`
    /// carries. `results` are the classes a `Break` leaves with.
    pub fn loop_(
        &mut self,
        initial: &[ValueId],
        results: &[Class],
        build: impl FnOnce(&mut Builder, &[ValueId]),
    ) -> Vec<ValueId> {
        let classes: Vec<_> = initial
            .iter()
            .map(|&value| self.program.class(value))
            .collect();
        let body = self.region(&classes, build);
        let initial = self.program.hold(initial);
        self.push(Op::Loop { initial, body }, results)
    }

    // Explicit transfers close the region. Its callback returns no token.

    pub fn ret(&mut self, values: &[ValueId]) {
        self.exit(Exit::Return, values);
    }

    pub fn yield_(&mut self, values: &[ValueId]) {
        self.exit(Exit::Yield, values);
    }

    pub fn continue_(&mut self, values: &[ValueId]) {
        self.exit(Exit::Continue, values);
    }

    pub fn break_(&mut self, values: &[ValueId]) {
        self.exit(Exit::Break, values);
    }

    fn exit(&mut self, exit: Exit, values: &[ValueId]) {
        self.open();
        self.terminator = Some(Terminator {
            exit,
            values: self.program.hold(values),
        });
    }

    fn open(&self) {
        assert!(
            self.terminator.is_none(),
            "a terminated region cannot be extended"
        );
    }

    fn region(
        &mut self,
        params: &[Class],
        build: impl FnOnce(&mut Builder, &[ValueId]),
    ) -> RegionId {
        self.open();
        let entry = self.program.mint(params);
        let params: Vec<_> = self.program.values(entry).to_vec();

        let mut builder = Builder {
            program: self.program,
            params: entry,
            ops: Vec::new(),
            results: Vec::new(),
            terminator: None,
        };
        build(&mut builder, &params);
        let region = builder.finish();

        self.program.regions.push(region)
    }

    /// The same, for results a signature already names.
    fn push_from(&mut self, op: Op, returns: Range) -> Vec<ValueId> {
        self.open();
        let results = self.program.mint_from(returns);
        let values = self.program.values(results).to_vec();
        self.ops.push(op);
        self.results.push(results);
        values
    }

    /// One result, which is every operation but a call and a construct that
    /// carries values out. Answers the value itself, so that the common case
    /// never builds a list to take the first of.
    fn push_one(&mut self, op: Op, class: Class) -> ValueId {
        self.open();
        let (value, results) = self.program.mint_one(class);
        self.ops.push(op);
        self.results.push(results);
        value
    }

    fn push(&mut self, op: Op, classes: &[Class]) -> Vec<ValueId> {
        self.open();
        let results = self.program.mint(classes);
        let values = self.program.values(results).to_vec();
        self.ops.push(op);
        self.results.push(results);
        values
    }

    /// Append this region's instructions to the program, where they become
    /// one contiguous run.
    fn finish(self) -> Region {
        let start = self.program.ops.len();
        let len = self.ops.len();
        self.program.ops.extend_from_slice(&self.ops);
        self.program.results.extend_from_slice(&self.results);

        Region {
            params: self.params,
            ops: Range::of(start, len),
            terminator: self.terminator,
        }
    }
}
