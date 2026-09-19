//! What a target is entitled to assume.

use super::model::{
    Class, Exit, Op, Origin, Program, Range, RegionId, Symbol, Terminator, ValueId, Width,
};

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
    let Some(entry) = program.functions.first() else {
        return Err("missing entry function".into());
    };
    if !program.values(entry.params).is_empty() || program.signature(entry.returns) != [Class::Word]
    {
        return Err("entry must take nothing and return one word".into());
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
        let name = program.name(function.name);
        if program.values(function.params) != program.values(program.region(function.body).params) {
            return Err(format!("{name}: function and body parameters disagree"));
        }
        let context = Context {
            returns: program.signature(function.returns),
            yields: None,
            loops: None,
        };
        checker
            .region(function.body, &context)
            .map_err(|error| format!("{name} {error}"))?;
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
        refs.values(held.terminator.values)?;
    }
    for op in &p.ops {
        refs.op(*op)?;
    }
    Ok(())
}

fn reference<T>(pool: &[T], index: usize, what: &str) -> Result<(), String> {
    pool.get(index)
        .map(|_| ())
        .ok_or_else(|| format!("invalid {what} reference"))
}

struct References<'a>(&'a Program);

impl References<'_> {
    fn value(&self, id: ValueId) -> Result<(), String> {
        reference(&self.0.classes, id.index(), "value")
    }

    fn values(&self, range: Range) -> Result<(), String> {
        for &id in slice(&self.0.operands, range)? {
            self.value(id)?;
        }
        Ok(())
    }

    fn region(&self, id: RegionId) -> Result<(), String> {
        reference(&self.0.regions, id.index(), "region")
    }

    fn symbol(&self, id: Symbol) -> Result<&str, String> {
        let range = self
            .0
            .symbols
            .get(id.index())
            .ok_or("invalid symbol reference")?;
        std::str::from_utf8(slice(&self.0.names, *range)?).map_err(|_| "invalid name text".into())
    }

    fn declarations(&self) -> Result<(), String> {
        let p = self.0;
        for function in &p.functions {
            self.symbol(function.name)?;
            self.values(function.params)?;
            slice(&p.signature, function.returns)?;
            self.region(function.body)?;
        }
        for platform in &p.platform {
            let name = self.symbol(platform.name)?;
            let takes = slice(&p.signature, platform.params)?;
            let answers = slice(&p.signature, platform.returns)?;
            let routine = p
                .routines
                .get(name)
                .ok_or_else(|| format!("unknown platform `{name}`"))?;
            if takes != routine.takes || answers != routine.answers.as_slice() {
                return Err(format!(
                    "platform `{name}` disagrees with its routine signature"
                ));
            }
        }
        Ok(())
    }

    fn datum(&self, id: super::model::DataId, natural: bool) -> Result<(), String> {
        let span = self
            .0
            .spans
            .get(id.index())
            .ok_or("invalid datum reference")?;
        if natural && span.origin != Origin::Data {
            return Err("natural constant must use immutable data".into());
        }
        Ok(())
    }

    fn op(&self, op: Op) -> Result<(), String> {
        let p = self.0;
        match op {
            Op::Constant { .. } => {}
            Op::NaturalConstant(id) | Op::AddressOf(id) => {
                self.datum(id, matches!(op, Op::NaturalConstant(_)))?;
            }
            Op::Binary { left, right, .. }
            | Op::Compare { left, right, .. }
            | Op::Store {
                address: left,
                value: right,
                ..
            } => {
                self.value(left)?;
                self.value(right)?;
            }
            Op::Load { address: value, .. } | Op::Convert { value, .. } => self.value(value)?,
            Op::Call { function, args } => {
                reference(&p.functions, function.index(), "function")?;
                self.values(args)?;
            }
            Op::PlatformCall { platform, args } => {
                reference(&p.platform, platform.index(), "platform")?;
                self.values(args)?;
            }
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
    returns: &'a [Class],
    yields: Option<&'a [Class]>,
    // Carried parameters and results of the nearest enclosing loop.
    loops: Option<(&'a [Class], &'a [Class])>,
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

    fn results(&self, results: &[ValueId], expected: &[Class]) -> Result<(), String> {
        let found = self.classes(results);
        if found != expected {
            return Err(format!(
                "operation results {found:?}, expected {expected:?}"
            ));
        }
        Ok(())
    }

    fn region(&mut self, id: RegionId, context: &Context<'_>) -> Result<(), String> {
        if std::mem::replace(&mut self.regions[id.index()], true) {
            return Err(format!("region {id:?} is cyclic or has multiple owners"));
        }
        let p = self.program;
        let region = p.region(id);
        let mark = self.entered.len();
        for &param in p.values(region.params) {
            self.define(param)?;
        }
        for at in region.ops.range() {
            if std::mem::replace(&mut self.ops[at], true) {
                return Err("instruction has multiple region owners".into());
            }
            let results = p.values(p.results[at]);
            self.instruction(&p.ops[at], results, context)?;
            if let Op::PlatformCall { platform, .. } = p.ops[at] {
                let name = p.name(p.platform[platform.index()].name);
                if p.routines.get(name).is_some_and(|r| !r.comes_back)
                    && (at + 1 != region.ops.range().end
                        || region.terminator.exit != Exit::Unreachable)
                {
                    return Err(format!(
                        "calls `{name}`, which does not come back, and carries on"
                    ));
                }
            }
            for &result in results {
                self.define(result)?;
            }
        }
        self.terminator(region.terminator, context)?;
        for value in self.entered.drain(mark..) {
            self.visible[value.index()] = false;
        }
        Ok(())
    }

    fn terminator(&self, terminator: Terminator, context: &Context<'_>) -> Result<(), String> {
        let expected = match terminator.exit {
            Exit::Return => Some(context.returns),
            Exit::Yield => context.yields,
            Exit::Continue => context.loops.map(|l| l.0),
            Exit::Break => context.loops.map(|l| l.1),
            Exit::Unreachable => Some([].as_slice()),
        }
        .ok_or_else(|| format!("{:?} has no enclosing receiver", terminator.exit))?;
        self.given(
            self.program.values(terminator.values),
            expected,
            &format!("{:?}", terminator.exit),
        )
    }

    fn instruction(
        &mut self,
        op: &Op,
        results: &[ValueId],
        context: &Context<'_>,
    ) -> Result<(), String> {
        match *op {
            // Address constants are supported, including a literal null pointer.
            Op::Constant { class, .. } => self.results(results, &[class])?,
            Op::Convert { class, value } => {
                self.conversion(value, class)?;
                self.results(results, &[class])?;
            }
            Op::NaturalConstant(_) => self.results(results, &[Class::Natural])?,
            Op::AddressOf(_) => self.results(results, &[Class::Address])?,
            Op::Binary { left, right, .. } => self.binary(left, right, results)?,
            Op::Compare { left, right, .. } => {
                self.comparison(left, right)?;
                self.results(results, &[Class::Word])?;
            }
            Op::Load { address, .. } => {
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
                self.store(width, address, value)?;
                self.results(results, &[])?;
            }
            Op::Call { .. } | Op::PlatformCall { .. } => self.call(*op, results)?,
            Op::If { .. } | Op::Loop { .. } => self.control(*op, results, context)?,
        }
        Ok(())
    }

    fn control(
        &mut self,
        op: Op,
        results: &[ValueId],
        context: &Context<'_>,
    ) -> Result<(), String> {
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
                for branch in [then_region, else_region] {
                    if !p.values(p.region(branch).params).is_empty() {
                        return Err("branch region cannot have parameters".into());
                    }
                    self.region(branch, &inner)?;
                }
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
                self.region(body, &inner)?;
            }
            _ => unreachable!("only structured control"),
        }
        Ok(())
    }

    fn call(&self, op: Op, results: &[ValueId]) -> Result<(), String> {
        let p = self.program;
        let (name, params, returns, args) = match op {
            Op::Call { function, args } => {
                let callee = &p.functions[function.index()];
                (
                    callee.name,
                    self.classes(p.values(callee.params)),
                    callee.returns,
                    args,
                )
            }
            Op::PlatformCall { platform, args } => {
                let callee = &p.platform[platform.index()];
                (
                    callee.name,
                    p.signature(callee.params).to_vec(),
                    callee.returns,
                    args,
                )
            }
            _ => unreachable!("only calls"),
        };
        let what = format!("calls `{}`", p.name(name));
        self.given(p.values(args), &params, &what)?;
        self.results(results, p.signature(returns))
    }

    fn conversion(&self, value: ValueId, class: Class) -> Result<(), String> {
        let from = self.read(value)?;
        let numeric = |c| c != Class::Address;
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
        if held == Class::Address {
            return Err("arithmetic result must be numeric".into());
        }
        self.require(left, held)?;
        self.require(right, held)
    }

    fn comparison(&self, left: ValueId, right: ValueId) -> Result<(), String> {
        let (left, right) = (self.read(left)?, self.read(right)?);
        if !left.fits(right) && !right.fits(left) {
            return Err(format!("{left:?} and {right:?} in one comparison"));
        }
        Ok(())
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
