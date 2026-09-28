//! What a target is entitled to assume.

use super::model::{
    Binary, Class, Definition, Exit, Function, Op, Origin, Range, RegionId, Returns, ShapeId,
    Symbol, Terminator, ValueId, Width,
};
use super::program::Program;
use crate::index::{Id, Pool};

/// Check pool references, lexical SSA scope, and operation/control-flow classes.
///
/// Narrow values may flow to wider consumers according to [`Class::fits`].
/// This is a structural check, not a proof of arithmetic bounds or memory safety.
///
/// # Errors
///
/// Names the first disagreement found, without indexing an unchecked pool reference.
pub fn validate(program: &Program) -> Result<(), String> {
    pools(program)?;
    let Some(entry) = program.functions.get(program.entry()) else {
        return Err("missing entry function".into());
    };
    if entry.body().is_none()
        || !matches!(entry.returns, Returns::Values(_))
        || program.signature(entry.returns.classes()) != [Class::Word]
    {
        return Err("entry must have a body and return one word".into());
    }
    let mut checker = Checker {
        program,
        defined: vec![false; program.classes.len()],
        visible: vec![false; program.classes.len()],
        entered: Vec::new(),
        regions: vec![false; program.regions.len()],
        ops: vec![false; program.ops.len()],
    };
    for function in program.functions() {
        checker
            .function(function)
            .map_err(|error| format!("{} {error}", program.name(function.name)))?;
    }
    Ok(())
}

fn slice<T>(pool: &[T], range: Range) -> Result<&[T], String> {
    let start = usize::try_from(range.start()).map_err(|_| "pool offset overflow")?;
    let end = start
        .checked_add(range.len())
        .ok_or("pool range overflow")?;
    pool.get(start..end)
        .ok_or_else(|| "invalid pool range".into())
}

/// Do this before using the convenient (indexing) public accessors. IDs are
/// public, so even a builder client can hand us an address of a missing datum
/// or a terminator whose operand range belongs to another program.
fn pools(p: &Program) -> Result<(), String> {
    let refs = References(p);
    refs.declarations()?;
    for span in &p.spans {
        let blob = match span.origin {
            Origin::Data => &p.data,
            Origin::Globals => &p.globals,
        };
        let start = usize::try_from(span.start).map_err(|_| "datum offset overflow")?;
        let len = usize::try_from(span.len).map_err(|_| "datum length overflow")?;
        slice(blob, Range::of(start, len))?;
    }
    if p.ops.len() != p.results.len() {
        return Err("operation and result pools have different lengths".into());
    }
    for &results in &p.results {
        refs.values(results)?;
    }
    for held in &p.regions {
        refs.values(held.params)?;
        slice(&p.ops, held.ops)?;
        if let Some(terminator) = held.terminator {
            refs.values(terminator.values)?;
        }
    }
    for op in &p.ops {
        refs.op(*op)?;
    }
    Ok(())
}

fn reference<I: Id, T>(pool: &Pool<I, T>, id: I, what: &str) -> Result<(), String> {
    pool.get(id)
        .map(|_| ())
        .ok_or_else(|| format!("invalid {what} reference"))
}

struct References<'a>(&'a Program);

impl References<'_> {
    fn value(&self, id: ValueId) -> Result<(), String> {
        reference(&self.0.classes, id, "value")
    }

    fn values(&self, range: Range) -> Result<(), String> {
        for &id in slice(&self.0.operands, range)? {
            self.value(id)?;
        }
        Ok(())
    }

    fn region(&self, id: RegionId) -> Result<(), String> {
        reference(&self.0.regions, id, "region")
    }

    fn symbol(&self, id: Symbol) -> Result<&str, String> {
        let range = self.0.symbols.get(id).ok_or("invalid symbol reference")?;
        std::str::from_utf8(slice(&self.0.names, *range)?).map_err(|_| "invalid name text".into())
    }

    fn declarations(&self) -> Result<(), String> {
        let p = self.0;
        for function in &p.functions {
            let name = self.symbol(function.name)?;
            if matches!(function.definition, Definition::Declared(_)) {
                return Err(format!("function `{name}` has not been defined"));
            }
            let params = slice(&p.signature, function.params)?;
            let names = slice(&p.parameters, function.parameters)?;
            if params.len() != names.len() {
                return Err(format!(
                    "function `{name}` has the wrong number of parameter names"
                ));
            }
            for parameter in names {
                self.symbol(parameter.name)?;
            }
            slice(&p.signature, function.returns.classes())?;
            if let Some(body) = function.body() {
                self.region(body)?;
            }
        }
        Ok(())
    }

    fn datum(&self, id: super::model::DataId) -> Result<&super::model::Span, String> {
        self.0
            .spans
            .get(id)
            .ok_or_else(|| "invalid datum reference".into())
    }

    fn natural_datum(&self, id: super::model::DataId) -> Result<(), String> {
        if self.datum(id)?.origin != Origin::Data {
            return Err("natural constant must use immutable data".into());
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "exhaustive operation dispatch keeps each operand reference check adjacent"
    )]
    fn op(&self, op: Op) -> Result<(), String> {
        let p = self.0;
        match op {
            Op::Constant { .. } => {}
            Op::BufferEmpty { shape } => reference(&p.shapes, shape, "shape")?,
            Op::BufferKnown {
                elements,
                shape,
                bytes,
            } => {
                reference(&p.shapes, shape, "shape")?;
                self.datum(elements)?;
                let len = p.datum_bytes(elements).len();
                let leaves = p.shaped(shape);
                if leaves.is_empty()
                    || !leaves
                        .iter()
                        .all(|class| matches!(class, Class::Held(_) | Class::Word | Class::Natural))
                {
                    return Err("a known buffer's elements are not scalars".into());
                }
                let element = leaves.len() * usize::from(bytes);
                if !(1..=8).contains(&bytes) || !len.is_multiple_of(element) {
                    return Err("a known buffer's bytes are not whole elements".into());
                }
            }
            Op::NaturalConstant(id) => self.natural_datum(id)?,
            Op::AddressOf(id) => return self.datum(id).map(|_| ()),
            Op::Cell { fields, shape, .. } => {
                reference(&p.shapes, shape, "shape")?;
                self.values(fields)?;
            }
            Op::CellTag { cell } => self.value(cell)?,
            Op::CellField { cell, shape, .. } => {
                reference(&p.shapes, shape, "shape")?;
                self.value(cell)?;
            }
            Op::BufferField { shape, .. } | Op::BufferAt { shape, .. }
                if p.shapes.get(shape).is_none() =>
            {
                return Err("invalid shape reference".into());
            }
            Op::BufferRoom { count, shape } => {
                reference(&p.shapes, shape, "shape")?;
                self.value(count)?;
            }
            Op::Binary { left, right, .. }
            | Op::Compare { left, right, .. }
            | Op::BufferField {
                buffer: left,
                start: right,
                ..
            }
            | Op::BufferAt {
                buffer: left,
                start: right,
                ..
            }
            | Op::Store {
                address: left,
                value: right,
                ..
            } => {
                self.value(left)?;
                self.value(right)?;
            }
            Op::Load { address: value, .. }
            | Op::Convert { value, .. }
            | Op::Shift { value, .. }
            | Op::Keep { value } => self.value(value)?,
            Op::Call { function, args } => {
                reference(&p.functions, function, "function")?;
                self.values(args)?;
            }
            Op::BufferPush { operands, shape }
            | Op::BufferReplace { operands, shape }
            | Op::BufferPrepend { operands, shape }
            | Op::BufferExtend { operands, shape } => {
                reference(&p.shapes, shape, "shape")?;
                self.values(operands)?;
            }
            Op::Float { operands, .. } => self.values(operands)?,
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                self.value(condition)?;
                self.region(then_region)?;
                self.region(else_region)?;
            }
            Op::Loop { initial, body } => {
                self.values(initial)?;
                self.region(body)?;
            }
        }
        Ok(())
    }
}

struct Context<'a> {
    returns: Option<&'a [Class]>,
    yields: Option<&'a [Class]>,
    // Carried parameters and results of the nearest enclosing loop.
    loops: Option<(&'a [Class], &'a [Class])>,
}

/// Transfers to enclosing constructs. These are independent possibilities:
/// one path may yield while another breaks. Returns and nonreturning calls
/// escape all local receivers, so need no bit here. Continue never exits a loop.
#[derive(Clone, Copy, Default)]
struct Transfers {
    yields: bool,
    breaks: bool,
}

impl Transfers {
    const fn merge(&mut self, other: Self) {
        self.yields |= other.yields;
        self.breaks |= other.breaks;
    }
}

struct Flow {
    next: bool,
    transfers: Transfers,
}

impl Flow {
    const NEXT: Self = Self {
        next: true,
        transfers: Transfers {
            yields: false,
            breaks: false,
        },
    };
}

struct Checker<'a> {
    program: &'a Program,
    // Definition uniqueness is program-wide; visibility is lexical. Restore
    // scope using an insertion log rather than copying it at every branch.
    defined: Vec<bool>,
    visible: Vec<bool>,
    entered: Vec<ValueId>,
    regions: Vec<bool>,
    ops: Vec<bool>,
}

impl Checker<'_> {
    fn function(&mut self, function: &Function) -> Result<(), String> {
        let Some(body) = function.body() else {
            return Ok(());
        };
        let p = self.program;
        if !p
            .values(p.region(body).params)
            .iter()
            .map(|&v| p.class(v))
            .eq(p.signature(function.params).iter().copied())
        {
            return Err("function and body parameters disagree".into());
        }
        let context = Context {
            returns: match function.returns {
                Returns::Never => None,
                Returns::Values(classes) => Some(p.signature(classes)),
            },
            yields: None,
            loops: None,
        };
        self.region(body, &context).map(|_| ())
    }

    fn define(&mut self, value: ValueId) -> Result<(), String> {
        if std::mem::replace(&mut self.defined[value.index()], true) {
            return Err(format!("defines {value:?} twice"));
        }
        self.visible[value.index()] = true;
        self.entered.push(value);
        Ok(())
    }

    fn read(&self, value: ValueId) -> Result<Class, String> {
        if !self.visible[value.index()] {
            return Err(format!(
                "reads {value:?} before it is available in this scope"
            ));
        }
        Ok(self.program.class(value))
    }

    fn require(&self, value: ValueId, wanted: Class) -> Result<(), String> {
        let held = self.read(value)?;
        if !held.fits(wanted) {
            return Err(format!("{held:?} read as {wanted:?}"));
        }
        Ok(())
    }

    fn classes(&self, values: &[ValueId]) -> Vec<Class> {
        values.iter().map(|&v| self.program.class(v)).collect()
    }

    fn given(&self, values: &[ValueId], wanted: &[Class], what: &str) -> Result<(), String> {
        if values.len() != wanted.len() {
            return Err(format!(
                "{what}: expected {} values, found {}",
                wanted.len(),
                values.len()
            ));
        }
        for (&value, &class) in values.iter().zip(wanted) {
            self.require(value, class)
                .map_err(|error| format!("{what}: {error}"))?;
        }
        Ok(())
    }

    /// The one class an instruction writes, for those that write one.
    ///
    /// What it writes is not something it reads, so nothing here asks
    /// whether the value is in scope: it is the value this brings into one.
    fn one(&self, results: &[ValueId]) -> Result<Class, String> {
        let [result] = results else {
            return Err("operation must have one result".into());
        };
        Ok(self.program.class(*result))
    }

    fn results(&self, results: &[ValueId], expected: &[Class]) -> Result<(), String> {
        let found = self.classes(results);
        if found != expected {
            return Err(format!(
                "operation results {found:?}, expected {expected:?}"
            ));
        }
        Ok(())
    }

    fn region(&mut self, id: RegionId, context: &Context<'_>) -> Result<Transfers, String> {
        if std::mem::replace(&mut self.regions[id.index()], true) {
            return Err(format!("region {id:?} is cyclic or has multiple owners"));
        }
        let p = self.program;
        let region = p.region(id);
        let mark = self.entered.len();
        for &param in p.values(region.params) {
            self.define(param)?;
        }
        let mut flow = self.instructions(region.ops, context)?;
        match (flow.next, region.terminator) {
            (true, Some(terminator)) => {
                self.terminator(terminator, context)?;
                flow.transfers.merge(Transfers {
                    yields: terminator.exit == Exit::Yield,
                    breaks: terminator.exit == Exit::Break,
                });
            }
            (false, None) => {}
            (true, None) => return Err("region can fall through but has no terminator".into()),
            (false, Some(_)) => return Err("region does not come back but has a terminator".into()),
        }
        for value in self.entered.drain(mark..) {
            self.visible[value.index()] = false;
        }
        Ok(flow.transfers)
    }

    fn instructions(&mut self, ops: Range, context: &Context<'_>) -> Result<Flow, String> {
        let p = self.program;
        let mut flow = Flow::NEXT;
        for at in ops.range() {
            if std::mem::replace(&mut self.ops[at], true) {
                return Err("instruction has multiple region owners".into());
            }
            if !flow.next {
                return Err("instruction follows control flow that does not come back".into());
            }
            let results = p.values(p.results[at]);
            let next = self.instruction(&p.ops[at], results, context)?;
            flow.next = next.next;
            flow.transfers.merge(next.transfers);
            for &result in results {
                self.define(result)?;
            }
        }
        Ok(flow)
    }

    fn terminator(&self, terminator: Terminator, context: &Context<'_>) -> Result<(), String> {
        let expected = match terminator.exit {
            Exit::Return => context.returns,
            Exit::Yield => context.yields,
            Exit::Continue => context.loops.map(|l| l.0),
            Exit::Break => context.loops.map(|l| l.1),
        }
        .ok_or_else(|| format!("{:?} has no enclosing receiver", terminator.exit))?;
        self.given(
            self.program.values(terminator.values),
            expected,
            &format!("{:?}", terminator.exit),
        )
    }

    #[expect(
        clippy::too_many_lines,
        reason = "exhaustive operation validation keeps each result and operand contract adjacent"
    )]
    fn instruction(
        &mut self,
        op: &Op,
        results: &[ValueId],
        context: &Context<'_>,
    ) -> Result<Flow, String> {
        match *op {
            // Address constants are supported, including a literal null pointer.
            // What one is held at is the class of the value it writes, so
            // there is nothing here for the two of them to disagree about.
            Op::Constant { .. } => {
                if matches!(self.one(results)?, Class::Cell | Class::Buffer) {
                    return Err("a managed value cannot be fabricated by a scalar constant".into());
                }
            }
            Op::Cell { fields, shape, .. } => {
                self.shaped(self.program.values(fields), shape)?;
                self.results(results, &[Class::Cell])?;
            }
            Op::CellTag { cell } => {
                self.require(cell, Class::Cell)?;
                self.results(results, &[Class::Word])?;
            }
            Op::CellField {
                cell, index, shape, ..
            } => {
                self.require(cell, Class::Cell)?;
                self.leaf(results, index, shape)?;
            }
            Op::BufferEmpty { .. } | Op::BufferKnown { .. } => {
                self.results(results, &[Class::Buffer])?;
            }
            Op::BufferPush { operands, shape } => {
                let operands = self.program.values(operands);
                let Some((sequence, fields)) = operands.split_first_chunk::<3>() else {
                    return Err("a push names no sequence".into());
                };
                self.sequence(*sequence)?;
                self.shaped(fields, shape)?;
                self.results(results, &[Class::Buffer, Class::Word])?;
            }
            Op::BufferReplace { operands, shape } => {
                let operands = self.program.values(operands);
                let Some((sequence, rest)) = operands.split_first_chunk::<3>() else {
                    return Err("a replacement names no sequence".into());
                };
                let Some((index, fields)) = rest.split_first() else {
                    return Err("a replacement names no index".into());
                };
                self.sequence(*sequence)?;
                self.length(*index)?;
                self.shaped(fields, shape)?;
                self.results(results, &[Class::Buffer, Class::Word])?;
            }
            Op::BufferPrepend { operands, .. } | Op::BufferExtend { operands, .. } => {
                let operands = self.program.values(operands);
                let Ok(both) = <[ValueId; 6]>::try_from(operands) else {
                    return Err("a prepend names two sequences".into());
                };
                self.sequence([both[0], both[1], both[2]])?;
                self.sequence([both[3], both[4], both[5]])?;
                self.results(results, &[Class::Buffer, Class::Word])?;
            }
            Op::BufferField {
                buffer,
                start,
                index,
                shape,
            } => {
                self.require(buffer, Class::Buffer)?;
                self.length(start)?;
                self.leaf(results, index, shape)?;
            }
            Op::BufferRoom { count, shape } => {
                self.length(count)?;
                if self
                    .program
                    .shaped(shape)
                    .iter()
                    .any(|&leaf| super::ownership::managed(leaf))
                {
                    return Err("a buffer to be written from outside holds only scalars".into());
                }
                self.results(results, &[Class::Buffer])?;
            }
            Op::BufferAt { buffer, start, .. } => {
                self.require(buffer, Class::Buffer)?;
                self.length(start)?;
                self.results(results, &[Class::Address])?;
            }
            Op::Keep { value } => {
                self.read(value)?;
                self.results(results, &[])?;
            }
            Op::Convert { value } => {
                let class = self.one(results)?;
                self.conversion(value, class)?;
            }
            Op::NaturalConstant(_) => self.results(results, &[Class::Natural])?,
            Op::AddressOf(_) => self.results(results, &[Class::Address])?,
            Op::Binary {
                op: Binary::Monus,
                left,
                right,
            } => self.monus(left, right, results)?,
            Op::Binary {
                op: Binary::ShiftUp | Binary::ShiftDown,
                ..
            } if results
                .iter()
                .any(|&result| self.program.class(result) == Class::Natural) =>
            {
                return Err("a shift is of a machine value, not a natural".into());
            }
            Op::Binary { left, right, .. } => self.binary(left, right, results)?,
            Op::Shift { value, by, .. } => self.shift(value, by, results)?,
            Op::Float { float, operands } => self.float(float, operands, results)?,
            Op::Compare { left, right, .. } => {
                self.comparison(left, right)?;
                self.results(results, &[Class::Word])?;
            }
            Op::Load { width, address, .. } => {
                self.width(width)?;
                self.require(address, Class::Address)?;
                // Even a byte load zero-extends into a Word in this IR.
                self.results(results, &[Class::Word])?;
            }
            Op::Store {
                width,
                address,
                value,
                ..
            } => {
                self.width(width)?;
                self.store(width, address, value)?;
                self.results(results, &[])?;
            }
            Op::Call { function, .. } => {
                self.call(*op, results)?;
                return Ok(Flow {
                    next: self.program.functions[function].returns != Returns::Never,
                    ..Flow::NEXT
                });
            }
            Op::If { .. } | Op::Loop { .. } => return self.control(*op, results, context),
        }
        Ok(Flow::NEXT)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "two structured receivers, with class and continuation checks"
    )]
    fn control(
        &mut self,
        op: Op,
        results: &[ValueId],
        context: &Context<'_>,
    ) -> Result<Flow, String> {
        let p = self.program;
        match op {
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                self.require(condition, Class::Word)?;
                let yields = self.classes(results);
                let inner = Context {
                    yields: Some(&yields),
                    ..*context
                };
                let mut transfers = Transfers::default();
                for branch in [then_region, else_region] {
                    if !p.values(p.region(branch).params).is_empty() {
                        return Err("branch region cannot have parameters".into());
                    }
                    transfers.merge(self.region(branch, &inner)?);
                }
                // Yield reaches this If's continuation; Break escapes it.
                Ok(Flow {
                    next: transfers.yields,
                    transfers: Transfers {
                        breaks: transfers.breaks,
                        yields: false,
                    },
                })
            }
            Op::Loop { initial, body } => {
                let carried = self.classes(p.values(p.region(body).params));
                self.given(p.values(initial), &carried, "loop initial values")?;
                let answers = self.classes(results);
                let inner = Context {
                    returns: context.returns,
                    yields: None,
                    loops: Some((&carried, &answers)),
                };
                let transfers = self.region(body, &inner)?;
                // Only a break from this loop reaches its continuation.
                // Breaks from nested loops were consumed at those loops.
                Ok(Flow {
                    next: transfers.breaks,
                    ..Flow::NEXT
                })
            }
            _ => unreachable!("only structured control"),
        }
    }

    fn call(&self, op: Op, results: &[ValueId]) -> Result<(), String> {
        let p = self.program;
        let Op::Call { function, args } = op else {
            unreachable!("only calls")
        };
        if function == p.entry() {
            return Err("calls the logical entry, which only the target may enter".into());
        }
        let callee = &p.functions[function];
        let what = format!("calls `{}`", p.name(callee.name));
        self.given(p.values(args), p.signature(callee.params), &what)?;
        self.results(results, p.signature(callee.returns.classes()))
    }

    /// A sequence length is a count a word holds.
    fn length(&self, len: ValueId) -> Result<(), String> {
        let class = self.read(len)?;
        if class.fits(Class::Word) {
            Ok(())
        } else {
            Err(format!("a buffer length must fit a word, not {class:?}"))
        }
    }

    fn conversion(&self, value: ValueId, class: Class) -> Result<(), String> {
        let from = self.read(value)?;
        let numeric = |c| !matches!(c, Class::Address | Class::Cell | Class::Buffer);
        if !(numeric(from) && numeric(class)
            || from == class
            || matches!(
                (from, class),
                (Class::Address, Class::Word) | (Class::Word, Class::Address)
            ))
        {
            return Err(format!("invalid conversion from {from:?} to {class:?}"));
        }
        Ok(())
    }

    fn binary(&self, left: ValueId, right: ValueId, results: &[ValueId]) -> Result<(), String> {
        let [result] = results else {
            return Err("binary operation must have one result".into());
        };
        let held = self.program.class(*result);
        if matches!(held, Class::Address | Class::Cell | Class::Buffer) {
            return Err("arithmetic result must be numeric".into());
        }
        self.require(left, held)?;
        self.require(right, held)
    }

    /// Saturating subtraction reads its operands as a comparison does and
    /// answers at any numeric class, since it answers no more than `left`.
    /// Only a natural's monus answers a natural: nothing else makes one.
    fn monus(&self, left: ValueId, right: ValueId, results: &[ValueId]) -> Result<(), String> {
        let [result] = results else {
            return Err("binary operation must have one result".into());
        };
        self.comparison(left, right)?;
        let operands = self.read(left)?;
        if operands == Class::Address {
            return Err("a monus subtracts numbers, not addresses".into());
        }
        let held = self.program.class(*result);
        let natural = operands == Class::Natural;
        match held {
            Class::Address | Class::Cell | Class::Buffer => {
                Err("arithmetic result must be numeric".into())
            }
            Class::Natural if !natural => Err("a monus of machine values answers one".into()),
            Class::Held(_) | Class::Word if natural => {
                Err("a monus of naturals answers a natural".into())
            }
            Class::Natural | Class::Held(_) | Class::Word => Ok(()),
        }
    }

    /// A shift moves a value the machine holds, by a distance it does not
    /// have to work out.
    ///
    /// Nought places is not a shift, and nothing writes one: a product by one
    /// is the value, and a rule saying so leaves the value rather than an
    /// instruction that does nothing. An arbitrary-precision natural has no
    /// bits to move -- its products go through the helpers -- and neither has
    /// an address.
    /// Patterns in and one out, each no wider than the format's.
    fn float(
        &self,
        float: crate::float::Float,
        operands: Range,
        results: &[ValueId],
    ) -> Result<(), String> {
        let [result] = results else {
            return Err("a float operation must have one result".into());
        };
        let pattern = Class::fixed(float.format.bits());
        if !self.program.class(*result).fits(pattern) || !pattern.fits(self.program.class(*result))
        {
            return Err(format!(
                "{float} must answer a pattern of {} bits",
                float.format.bits()
            ));
        }
        let operands = self.program.values(operands);
        if operands.len() != float.operation.arity() {
            return Err(format!(
                "{float} takes {} operands",
                float.operation.arity()
            ));
        }
        operands
            .iter()
            .try_for_each(|&operand| self.require(operand, pattern))
    }

    fn shift(&self, value: ValueId, by: u16, results: &[ValueId]) -> Result<(), String> {
        let [result] = results else {
            return Err("shift must have one result".into());
        };
        if by == 0 {
            return Err("shift must move at least one place".into());
        }
        let held = self.program.class(*result);
        if !matches!(held, Class::Held(_) | Class::Word) {
            return Err("shift must be over a value the machine holds".into());
        }
        self.require(value, held)
    }

    /// Two values may be compared where they are the same sort of thing.
    ///
    /// Not where one admits the other: two numbers that can be nothing the
    /// same are still two numbers, and asking whether they are equal is a
    /// question with an answer. What cannot be asked is whether a number
    /// equals an address, or a machine word an arbitrary-precision natural.
    fn comparison(&self, left: ValueId, right: ValueId) -> Result<(), String> {
        let (left, right) = (self.read(left)?, self.read(right)?);
        let alike = matches!(
            (left, right),
            (Class::Held(_) | Class::Word, Class::Held(_) | Class::Word)
                | (Class::Natural, Class::Natural)
                | (Class::Address, Class::Address)
        );
        if !alike {
            return Err(format!("{left:?} and {right:?} in one comparison"));
        }
        Ok(())
    }

    /// Fields stored as `shape` says: one per leaf, each something the
    /// leaf's class holds.
    fn shaped(&self, fields: &[ValueId], shape: ShapeId) -> Result<(), String> {
        let leaves = self.program.shaped(shape);
        if fields.len() != leaves.len() {
            return Err(format!(
                "{} fields stored as a shape of {} leaves",
                fields.len(),
                leaves.len()
            ));
        }
        for (&field, &leaf) in fields.iter().zip(leaves) {
            let held = self.read(field)?;
            if !(held == leaf || held.fits(leaf)) {
                return Err(format!("{held:?} stored as a leaf of {leaf:?}"));
            }
        }
        Ok(())
    }

    /// A sequence: a buffer, where in it the sequence starts, and how many
    /// elements it has.
    fn sequence(&self, [buffer, start, len]: [ValueId; 3]) -> Result<(), String> {
        self.require(buffer, Class::Buffer)?;
        self.length(start)?;
        self.length(len)
    }

    /// One leaf of `shape` read back.
    fn leaf(&self, results: &[ValueId], index: u32, shape: ShapeId) -> Result<(), String> {
        self.one(results)?;
        let leaves = self.program.shaped(shape);
        if usize::try_from(index).map_or(true, |index| index >= leaves.len()) {
            return Err(format!(
                "leaf {index} of a shape of {} leaves",
                leaves.len()
            ));
        }
        Ok(())
    }

    /// A width no wider than the word, where the program says how wide that
    /// is.
    fn width(&self, width: Width) -> Result<(), String> {
        match self.program.layout {
            Some(layout) if width.bytes(layout.word_bits) > layout.word_bits / 8 => Err(format!(
                "{width:?} is wider than a {} bit word",
                layout.word_bits
            )),
            _ => Ok(()),
        }
    }

    fn store(&self, width: Width, address: ValueId, value: ValueId) -> Result<(), String> {
        self.require(address, Class::Address)?;
        let held = self.read(value)?;
        // Byte stores deliberately truncate a word; word stores can
        // also save a pointer. Neither stores a runtime Natural.
        if !(held.fits(Class::Word) || width == Width::Word && held == Class::Address) {
            return Err(format!("invalid stored class {held:?}"));
        }
        Ok(())
    }
}
