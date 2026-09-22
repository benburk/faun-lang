//! Program storage, queries, and construction entry points.

use super::builder::Builder;
use super::model::{
    Class, DataId, Definition, Exit, Function, FunctionId, Op, Origin, Parameter, Range, Region,
    RegionId, Returns, Span, Symbol, ValueId,
};
use crate::index::{Pool, append_range};

/// An empty construction state by default.
///
/// The first function is the logical entry; validation requires it to have a
/// body and one Word result, and rejects ordinary calls to it. Targets alone
/// enter it and supply named parameters from their process startup convention.
#[derive(Clone, Debug, Default)]
pub struct Program {
    /// Absent until a representation pass serializes target-sized data.
    pub(super) layout: Option<super::Layout>,
    /// Every datum end to end. A target adds its own base and nothing else,
    /// so two of them cannot disagree about the layout between.
    pub(super) data: Vec<u8>,
    /// The same, for what a program may write to.
    pub(super) globals: Vec<u8>,
    pub(super) spans: Pool<DataId, Span>,
    pub(super) functions: Pool<FunctionId, Function>,
    /// The class of every value, by value.
    pub(super) classes: Pool<ValueId, Class>,
    /// The classes a function takes and answers.
    pub(super) signature: Vec<Class>,
    /// Logical parameter names, in one run per function. Targets may use
    /// entry names to choose values from their startup convention.
    pub(super) parameters: Vec<Parameter>,
    pub(super) ops: Vec<Op>,
    /// What each instruction defines, beside it rather than in it: a pass
    /// that does not care never reads this array.
    pub(super) results: Vec<Range>,
    pub(super) operands: Vec<ValueId>,
    pub(super) regions: Pool<RegionId, Region>,
    /// Every name the program uses, each once, end to end.
    pub(super) names: Vec<u8>,
    pub(super) symbols: Pool<Symbol, Range>,
}
impl Program {
    /// The layout required by serialized data, if representation is bound.
    #[must_use]
    pub const fn layout(&self) -> Option<super::Layout> {
        self.layout
    }

    /// # Errors
    /// Rejects use of target-sized data at a different width or byte order.
    pub fn check_layout(&self, actual: super::Layout) -> Result<(), String> {
        if let Some(expected) = self.layout
            && expected != actual
        {
            return Err(format!(
                "program requires layout {expected:?}, not {actual:?}"
            ));
        }
        Ok(())
    }

    pub(super) fn bind_layout(&mut self, layout: super::Layout) -> Result<(), String> {
        self.check_layout(layout)?;
        self.layout = Some(layout);
        Ok(())
    }

    /// Keep a list of existing values, giving back the run it occupies.
    pub(super) fn hold(&mut self, values: &[ValueId]) -> Range {
        append_range(&mut self.operands, values)
    }

    /// The classes a run in the signature pool names.
    ///
    /// # Panics
    /// If the range is outside this program's signature pool.
    #[must_use]
    pub fn signature(&self, range: Range) -> &[Class] {
        &self.signature[range.range()]
    }

    /// Parameter names, in signature order.
    pub fn parameter_names(&self, function: FunctionId) -> impl Iterator<Item = &str> {
        self.parameters[self.functions[function].parameters.range()]
            .iter()
            .map(|parameter| self.name(parameter.name))
    }

    /// The name of one parameter.
    ///
    /// # Panics
    /// If `function` is invalid or `at` is outside its signature.
    #[must_use]
    pub fn parameter_name(&self, function: FunctionId, at: usize) -> &str {
        self.parameter_names(function)
            .nth(at)
            .expect("a parameter in the function signature")
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

    /// Values carried by the region's explicit transfer, or none when its
    /// instructions cannot fall through.
    #[must_use]
    pub fn outgoing(&self, region: RegionId) -> &[ValueId] {
        self.region(region)
            .terminator
            .map_or(&[], |term| self.values(term.values))
    }

    #[must_use]
    pub fn values(&self, operands: Range) -> &[ValueId] {
        &self.operands[operands.range()]
    }

    #[must_use]
    pub fn ops(&self, region: RegionId) -> &[Op] {
        let ops = self.regions[region].ops;
        &self.ops[ops.range()]
    }

    /// The instructions of a region, each with what it defines.
    ///
    /// Backwards as well as forwards: which instruction a value is read by
    /// is something a pass works out by reading a region the other way.
    #[must_use]
    pub fn walk(&self, region: RegionId) -> impl DoubleEndedIterator<Item = (&Op, &[ValueId])> {
        let ops = self.regions[region].ops;
        self.ops[ops.range()]
            .iter()
            .zip(&self.results[ops.range()])
            .map(|(op, results)| (op, &self.operands[results.range()]))
    }

    /// Every instruction in a region and in every region within it.
    ///
    /// A region holds regions, so anything asking what a program does has
    /// to walk down through them. Five places did, each writing the same
    /// descent past `If` and `Loop` to reach what it came for.
    ///
    /// # Panics
    ///
    /// Never: what it reads back is what it just read.
    pub fn every(&self, region: RegionId) -> impl Iterator<Item = &Op> {
        self.walk_within(region).map(|(op, _)| op)
    }

    /// The same, each with what it defines, for anything that has to read a
    /// value's class to know what an instruction meant.
    ///
    /// # Panics
    /// Never: what it reads back is what it just read.
    pub fn walk_within(&self, region: RegionId) -> impl Iterator<Item = (&Op, &[ValueId])> {
        let mut stack = vec![(region, 0usize)];
        std::iter::from_fn(move || {
            loop {
                let (region, at) = *stack.last()?;
                let ops = self.regions[region].ops;
                let Some(op) = self.ops(region).get(at) else {
                    stack.pop();
                    continue;
                };
                stack.last_mut().expect("the region just read").1 = at + 1;
                match *op {
                    Op::If {
                        then_region,
                        else_region,
                        ..
                    } => {
                        stack.push((then_region, 0));
                        stack.push((else_region, 0));
                    }
                    Op::Loop { body, .. } => stack.push((body, 0)),
                    _ => {}
                }
                return Some((
                    op,
                    &self.operands[self.results
                        [usize::try_from(ops.start()).expect("an index that fits") + at]
                        .range()],
                ));
            }
        })
    }

    /// Whether anything in the program calls a routine by this name.
    #[must_use]
    pub fn reaches(&self, name: &str) -> bool {
        self.functions
            .iter()
            .filter_map(Function::body)
            .flat_map(|body| self.every(body))
            .any(|op| match *op {
                Op::Call { function, .. } => self.functions[function]
                    .external()
                    .is_some_and(|symbol| self.name(symbol) == name),
                _ => false,
            })
    }

    #[must_use]
    pub fn region(&self, region: RegionId) -> Region {
        self.regions[region]
    }

    /// A function declaration by its typed ID, in any definition state.
    ///
    /// # Panics
    /// If the ID is outside this program's function table. IDs do not encode
    /// which program they came from.
    #[must_use]
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id]
    }

    #[must_use]
    pub fn functions(&self) -> &[Function] {
        self.functions.as_slice()
    }

    /// The first function's ID. [`Program::new`] declares it immediately;
    /// a default program must declare it before this ID can be used.
    #[must_use]
    pub const fn entry(&self) -> FunctionId {
        FunctionId(0)
    }

    #[must_use]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    #[must_use]
    pub fn globals(&self) -> &[u8] {
        &self.globals
    }

    #[must_use]
    pub fn datum(&self, data: DataId) -> Span {
        self.spans[data]
    }

    #[must_use]
    pub fn class(&self, value: ValueId) -> Class {
        self.classes[value]
    }

    #[must_use]
    pub const fn values_count(&self) -> usize {
        self.classes.len()
    }

    /// Whether a function's body ever comes back.
    ///
    /// A body leaving through a routine that answers `Never` falls off the
    /// end of its region rather than returning, and so does every region it
    /// could have left from. Nothing reads what such a body would have
    /// answered with, so a target may enter it rather than call it, and has
    /// nothing to write for after it.
    ///
    /// A declaration with no body answers yes: what something outside does
    /// is said by its contract, not read off a body that is not here.
    #[must_use]
    pub fn comes_back(&self, function: FunctionId) -> bool {
        let Some(body) = self.functions[function].body() else {
            return true;
        };
        let mut held = vec![body];
        while let Some(region) = held.pop() {
            let region = self.regions[region];
            if region
                .terminator
                .is_some_and(|held| held.exit == Exit::Return)
            {
                return true;
            }
            for op in &self.ops[region.ops.range()] {
                match *op {
                    Op::If {
                        then_region,
                        else_region,
                        ..
                    } => held.extend([then_region, else_region]),
                    Op::Loop { body, .. } => held.push(body),
                    _ => {}
                }
            }
        }
        false
    }
}

impl Program {
    /// A program and its parameterless entry function, returning one word.
    #[must_use]
    pub fn new(entry: &str) -> (Self, FunctionId) {
        Self::new_with_params(entry, &[])
    }

    /// A program and its logical entry function. Targets supply these named
    /// parameters from their process startup convention.
    #[must_use]
    pub fn new_with_params(entry: &str, params: &[(&str, Class)]) -> (Self, FunctionId) {
        let mut program = Self::default();
        let entry = program.declare_named(entry, params, &[Class::Word]);
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

    fn place(
        blob: &mut Vec<u8>,
        spans: &mut Pool<DataId, Span>,
        origin: Origin,
        bytes: &[u8],
    ) -> DataId {
        let start = u32::try_from(blob.len()).expect("data within 4 GiB");
        let len = u32::try_from(bytes.len()).expect("a datum within 4 GiB");
        blob.extend_from_slice(bytes);
        spans.push(Span { origin, start, len })
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
        if let Some(id) = self.symbols.position(held) {
            return id;
        }
        let name = append_range(&mut self.names, name.as_bytes());
        self.symbols.push(name)
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
        let names: Vec<_> = (0..params.len()).map(|at| format!("v{at}")).collect();
        let params: Vec<_> = names
            .iter()
            .zip(params)
            .map(|(name, &class)| (name.as_str(), class))
            .collect();
        self.external_named(name, &params, returns)
    }

    /// Declare an external with explicit parameter names.
    pub fn external_named(
        &mut self,
        name: &str,
        params: &[(&str, Class)],
        returns: Returns<&[Class]>,
    ) -> FunctionId {
        let name = self.symbol(name);
        let (params, parameters) = self.sign_named(params);
        let returns = match returns {
            Returns::Never => Returns::Never,
            Returns::Values(classes) => Returns::Values(self.sign(classes)),
        };
        self.functions.push(Function {
            name,
            params,
            parameters,
            returns,
            definition: Definition::External,
        })
    }

    /// Reserve parameters and a root slot, so a body may call a function
    /// declared after it, or itself. Validation rejects unbuilt declarations.
    pub fn declare(&mut self, name: &str, params: &[Class], returns: &[Class]) -> FunctionId {
        let names: Vec<_> = (0..params.len()).map(|at| format!("v{at}")).collect();
        let params: Vec<_> = names
            .iter()
            .zip(params)
            .map(|(name, &class)| (name.as_str(), class))
            .collect();
        self.declare_named(name, &params, returns)
    }

    /// Reserve a function whose parameters retain the supplied names.
    pub fn declare_named(
        &mut self,
        name: &str,
        params: &[(&str, Class)],
        returns: &[Class],
    ) -> FunctionId {
        let classes: Vec<_> = params.iter().map(|(_, class)| *class).collect();
        let values = self.mint(&classes);
        let (params, parameters) = self.sign_named(params);
        let body = self.regions.push(Region {
            params: values,
            ops: Range::default(),
            terminator: None,
        });
        let name = self.symbol(name);
        let returns = self.sign(returns);
        self.functions.push(Function {
            name,
            params,
            parameters,
            returns: Returns::Values(returns),
            definition: Definition::Declared(body),
        })
    }

    /// Declare a function that never returns. Like `declare`, it must be
    /// defined before validation, even when nothing calls it yet.
    pub fn declare_never(&mut self, name: &str, params: &[Class]) -> FunctionId {
        let names: Vec<_> = (0..params.len()).map(|at| format!("v{at}")).collect();
        let params: Vec<_> = names
            .iter()
            .zip(params)
            .map(|(name, &class)| (name.as_str(), class))
            .collect();
        self.declare_never_named(name, &params)
    }

    /// Reserve a nonreturning function with explicit parameter names.
    pub fn declare_never_named(&mut self, name: &str, params: &[(&str, Class)]) -> FunctionId {
        let id = self.declare_named(name, params, &[]);
        self.functions[id].returns = Returns::Never;
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
        let body = match self.functions[function].definition {
            Definition::Declared(body) | Definition::Body(body) => body,
            Definition::External => panic!("an external function cannot be defined"),
        };
        let entry = self.regions[body].params;
        let region = Builder::build(self, entry, build)?;
        self.regions[body] = region;
        self.functions[function].definition = Definition::Body(body);
        Ok(())
    }

    /// Hold a run of classes, for a signature.
    fn sign(&mut self, classes: &[Class]) -> Range {
        append_range(&mut self.signature, classes)
    }

    fn sign_named(&mut self, params: &[(&str, Class)]) -> (Range, Range) {
        let classes: Vec<_> = params.iter().map(|(_, class)| *class).collect();
        let classes = self.sign(&classes);
        let names: Vec<_> = params.iter().map(|(name, _)| self.symbol(name)).collect();
        let start = self.parameters.len();
        self.parameters
            .extend(names.into_iter().map(|name| Parameter { name }));
        (classes, Range::of(start, params.len()))
    }

    /// One value of `class`, and the run of one that names it.
    pub(super) fn mint_one(&mut self, class: Class) -> (ValueId, Range) {
        let start = self.operands.len();
        let value = self.classes.push(class);
        self.operands.push(value);
        (value, Range::of(start, 1))
    }

    /// A run of values for the classes a signature already names, read where
    /// they lie rather than copied out first.
    pub(super) fn mint_from(&mut self, signature: Range) -> Range {
        let start = self.operands.len();
        for at in signature.range() {
            let class = self.signature[at];
            let value = self.classes.push(class);
            self.operands.push(value);
        }
        Range::of(start, signature.len())
    }

    pub(super) fn mint(&mut self, classes: &[Class]) -> Range {
        let start = self.operands.len();
        for &class in classes {
            let value = self.classes.push(class);
            self.operands.push(value);
        }
        Range::of(start, classes.len())
    }
}
