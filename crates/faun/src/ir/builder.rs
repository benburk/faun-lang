//! Building well-shaped programs.

use super::model::{
    Binary, Class, DataId, Definition, Exit, Function, FunctionId, Offset, Op, Origin, Program,
    Range, Region, RegionId, Relation, Returns, Span, Symbol, Terminator, ValueId, Width, wrap,
};

impl Program {
    /// A program and its entry function, which takes nothing and returns one
    /// word, the exit status. Unlike `default`, this reserves the entry before
    /// other declarations. No environment or builtin catalog is installed.
    #[must_use]
    pub fn new(entry: &str) -> (Self, FunctionId) {
        let mut program = Self::default();
        let entry = program.declare(entry, &[], &[Class::Word]);
        (program, entry)
    }

    /// # Panics
    ///
    /// If the program's data outgrows the 4 GiB a target can address.
    pub fn intern(&mut self, bytes: &[u8]) -> DataId {
        Self::place(&mut self.data, &mut self.spans, Origin::Data, bytes)
    }

    /// The same, for a datum the program writes to. Its initial contents are
    /// in the image, so a counter starting at zero is eight zero bytes.
    ///
    /// # Panics
    ///
    /// If the program's data outgrows the 4 GiB a target can address.
    pub fn global(&mut self, bytes: &[u8]) -> DataId {
        Self::place(&mut self.globals, &mut self.spans, Origin::Globals, bytes)
    }

    fn place(blob: &mut Vec<u8>, spans: &mut Vec<Span>, origin: Origin, bytes: &[u8]) -> DataId {
        let start = u32::try_from(blob.len()).expect("data within 4 GiB");
        let len = u32::try_from(bytes.len()).expect("a datum within 4 GiB");
        blob.extend_from_slice(bytes);
        spans.push(Span { origin, start, len });
        DataId::at(spans.len() - 1)
    }

    /// The symbol for `name`, the same symbol every time. This runs once
    /// per declaration and nowhere else, so the scan is over what a program
    /// declares rather than over its terms.
    ///
    /// # Panics
    ///
    /// If the program outgrew the names it may have.
    pub fn symbol(&mut self, name: &str) -> Symbol {
        let held = |at: &Range| &self.names[at.range()] == name.as_bytes();
        if let Some(at) = self.symbols.iter().position(held) {
            return Symbol::at(at);
        }
        let at = self.names.len();
        self.names.extend_from_slice(name.as_bytes());
        self.symbols.push(Range::of(at, name.len()));
        Symbol::at(self.symbols.len() - 1)
    }

    /// Declare an external function by its provider name, with source aliases
    /// already resolved. Targets check whether they can provide this name and
    /// signature.
    pub fn external(
        &mut self,
        name: &str,
        params: &[Class],
        returns: Returns<&[Class]>,
    ) -> FunctionId {
        let name = self.symbol(name);
        let params = self.sign(params);
        let returns = match returns {
            Returns::Never => Returns::Never,
            Returns::Values(classes) => Returns::Values(self.sign(classes)),
        };
        self.functions.push(Function {
            name,
            params,
            returns,
            definition: Definition::External,
        });
        FunctionId::at(self.functions.len() - 1)
    }

    /// Reserve parameters and a root slot, so a body may call a function
    /// declared after it, or itself. Validation rejects unbuilt declarations.
    pub fn declare(&mut self, name: &str, params: &[Class], returns: &[Class]) -> FunctionId {
        let values = self.mint(params);
        let params = self.sign(params);
        self.regions.push(Region {
            params: values,
            ops: Range::default(),
            terminator: None,
        });
        let name = self.symbol(name);
        let returns = self.sign(returns);
        self.functions.push(Function {
            name,
            params,
            returns: Returns::Values(returns),
            definition: Definition::Declared(RegionId::at(self.regions.len() - 1)),
        });
        FunctionId::at(self.functions.len() - 1)
    }

    /// Declare a function that never returns. Like `declare`, it must be
    /// defined before validation, even when nothing calls it yet.
    pub fn declare_never(&mut self, name: &str, params: &[Class]) -> FunctionId {
        let id = self.declare(name, params, &[]);
        self.functions[id.index()].returns = Returns::Never;
        id
    }

    /// Build a declared function or replace its existing body. The callback
    /// records explicit transfers on the builder; it need not add one after
    /// instructions which cannot fall through. Validation checks completion.
    ///
    /// # Panics
    /// If `function` is invalid or external.
    pub fn define(&mut self, function: FunctionId, build: impl FnOnce(&mut Builder, &[ValueId])) {
        let result: Result<(), std::convert::Infallible> =
            self.try_define(function, |b, params| {
                build(b, params);
                Ok(())
            });
        match result {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }

    /// Build a body without an error side channel or a fabricated terminator.
    ///
    /// # Errors
    /// Returns the callback's error without replacing the old body or marking
    /// an unbuilt declaration as defined. This is
    /// append-only construction, not a transaction: values, data and nested
    /// regions appended by the callback remain in the pools on failure. They
    /// are not attached to this function, but still undergo pool-wide checks.
    /// Discard the program if that retained construction storage is unwanted;
    /// retrying does not roll it back.
    ///
    /// # Panics
    /// If `function` is invalid or external.
    pub fn try_define<E>(
        &mut self,
        function: FunctionId,
        build: impl FnOnce(&mut Builder, &[ValueId]) -> Result<(), E>,
    ) -> Result<(), E> {
        let body = match self.functions[function.index()].definition {
            Definition::Declared(body) | Definition::Body(body) => body,
            Definition::External => panic!("an external function cannot be defined"),
        };
        let entry = self.regions[body.index()].params;
        let params = self.values(entry).to_vec();
        let mut builder = Builder {
            program: self,
            params: entry,
            ops: Vec::new(),
            results: Vec::new(),
            terminator: None,
        };
        build(&mut builder, &params)?;
        let region = builder.finish();
        self.regions[body.index()] = region;
        self.functions[function.index()].definition = Definition::Body(body);
        Ok(())
    }

    /// Hold a run of classes, for a signature.
    fn sign(&mut self, classes: &[Class]) -> Range {
        let at = self.signature.len();
        self.signature.extend_from_slice(classes);
        Range::of(at, classes.len())
    }

    /// One value of `class`, and the run of one that names it.
    fn mint_one(&mut self, class: Class) -> (ValueId, Range) {
        let start = self.operands.len();
        self.classes.push(class);
        let value = ValueId::at(self.classes.len() - 1);
        self.operands.push(value);
        (value, Range::of(start, 1))
    }

    /// A run of values for the classes a signature already names, read where
    /// they lie rather than copied out first.
    pub(super) fn mint_from(&mut self, signature: Range) -> Range {
        let start = self.operands.len();
        for at in signature.range() {
            let class = self.signature[at];
            self.classes.push(class);
            self.operands.push(ValueId::at(self.classes.len() - 1));
        }
        Range::of(start, signature.len())
    }

    fn mint(&mut self, classes: &[Class]) -> Range {
        let start = self.operands.len();
        for &class in classes {
            self.classes.push(class);
            self.operands.push(ValueId::at(self.classes.len() - 1));
        }
        Range::of(start, classes.len())
    }
}

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
            .signature(self.program.functions[function.index()].params)
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

    /// The same word, written the way a negative number reads.
    pub fn constant_signed(&mut self, class: Class, value: i64) -> ValueId {
        self.constant(class, value.cast_unsigned())
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
        let returns = self.program.functions[function.index()].returns.classes();
        let args = self.program.hold(args);
        self.push_from(Op::Call { function, args }, returns)
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

        self.program.regions.push(region);
        RegionId::at(self.program.regions.len() - 1)
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
