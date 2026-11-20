//! Recognize a comparison observed through a canonicalized floating difference.
use super::{Atom, Body, CtorId, Expr, ExprId, FnId, Local, Operation, Program, TypeShape};
use crate::float::{Float, Format, Operation as FloatOp};

/// Whether `left - right` has a nonnegative observed sign. NaNs answer yes.
/// The signed-zero case that differs from an ordered comparison is excluded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatComparison {
    pub format: Format,
    pub left: Atom,
    pub right: Atom,
    pub yes: CtorId,
    pub no: CtorId,
}

enum Value {
    Unknown,
    Number(u64),
    Natural(Operation, usize, usize),
    Float(Float, Vec<usize>),
    Choice(usize, Vec<(CtorId, usize)>),
}

struct Analysis<'a> {
    program: &'a Program,
    operations: &'a [Option<Operation>],
    values: Vec<Value>,
    found: Vec<Option<FloatComparison>>,
    visited: Vec<bool>,
}

pub(super) fn analyze(
    program: &Program,
    operations: &[Option<Operation>],
) -> Vec<Option<FloatComparison>> {
    if !program.functions().iter().any(|f| f.float.is_some()) {
        return Vec::new();
    }
    let mut analysis = Analysis {
        program,
        operations,
        values: Vec::new(),
        found: vec![None; program.exprs_count()],
        visited: vec![false; program.exprs_count()],
    };
    for (at, operation) in operations.iter().enumerate() {
        let id = FnId::at(at);
        if program.function(id).float.is_some() || operation.is_some() {
            continue;
        }
        if let Some(body) = program.function(id).body() {
            analysis.values.clear();
            let scope = program
                .params(id)
                .iter()
                .map(|_| analysis.add(Value::Unknown))
                .collect();
            analysis.body(body, scope);
        }
    }
    analysis.found
}

impl Analysis<'_> {
    fn add(&mut self, value: Value) -> usize {
        let id = self.values.len();
        self.values.push(value);
        id
    }

    fn body(&mut self, body: Body, mut scope: Vec<usize>) -> usize {
        for &expr in self.program.bindings(body.bindings) {
            scope.push(self.expr(expr, &scope));
        }
        self.expr(body.tail, &scope)
    }

    fn constant(&self, constant: super::ConstId) -> Value {
        let value = super::single_field_constant(self.program, self.program.constant(constant));
        match value.view() {
            super::ConstantView::Natural(n) => {
                n.try_u64().ok().map_or(Value::Unknown, Value::Number)
            }
            super::ConstantView::Constructor(_)
                if self.program.fields(value.constructor()).is_empty() =>
            {
                Value::Number(u64::from(self.program.tag(value.constructor())))
            }
            _ => Value::Unknown,
        }
    }

    fn call(&self, callee: FnId, args: super::Range, scope: &[usize]) -> Value {
        let args: Vec<_> = self
            .program
            .atoms(args)
            .iter()
            .map(|a| scope[a.0.index()])
            .collect();
        if let Some(float) = self.program.function(callee).float {
            Value::Float(float, args)
        } else if let (Some(op), &[a, b]) = (self.operations[callee.index()], args.as_slice()) {
            Value::Natural(op, a, b)
        } else {
            Value::Unknown
        }
    }

    fn choice(&mut self, on: Atom, arms: super::Range, scope: &[usize]) -> usize {
        let on = scope[on.0.index()];
        let mut choices = Vec::new();
        for arm in self.program.arms(arms) {
            let mut inner = scope.to_vec();
            let fields = self.program.fields(arm.ctor);
            if matches!(
                super::type_shape(self.program, self.program.ctor(arm.ctor).owner),
                TypeShape::Wrapper { .. }
            ) {
                inner.push(on);
            } else {
                inner.extend(fields.iter().map(|_| self.add(Value::Unknown)));
            }
            choices.push((arm.ctor, self.body(arm.body, inner)));
        }
        if choices.len() == 1 {
            return choices[0].1;
        }
        self.add(Value::Choice(on, choices))
    }

    fn expr(&mut self, id: ExprId, scope: &[usize]) -> usize {
        let value = match self.program.expr(id) {
            Expr::Atom(a) => return scope[a.0.index()],
            Expr::Static(constant) => self.constant(constant),
            Expr::Con(ctor, args) => {
                if matches!(
                    super::type_shape(self.program, self.program.ctor(ctor).owner),
                    TypeShape::Wrapper { .. }
                ) {
                    return scope[self.program.atoms(args)[0].0.index()];
                }
                if args.is_empty() {
                    Value::Number(u64::from(self.program.tag(ctor)))
                } else {
                    Value::Unknown
                }
            }
            Expr::Call(callee, args) => self.call(callee, args, scope),
            Expr::Match(on, arms) => {
                return self.choice(on, arms, scope);
            }
        };
        let value = self.add(value);
        let found = self.comparison(value, scope);
        if self.visited[id.index()] {
            if self.found[id.index()] != found {
                self.found[id.index()] = None;
            }
        } else {
            self.visited[id.index()] = true;
            self.found[id.index()] = found;
        }
        value
    }

    fn number(&self, id: usize) -> Option<u64> {
        match self.values[id] {
            Value::Number(n) => Some(n),
            _ => None,
        }
    }

    fn limits(&self, limit: usize) -> Option<(Format, u64, u64)> {
        Some(match self.number(limit)? {
            0x8000_0000 => (Format::Binary32, 0x8000_0000, 0x7f80_0000),
            0x8000_0000_0000_0000 => (
                Format::Binary64,
                0x8000_0000_0000_0000,
                0x7ff0_0000_0000_0000,
            ),
            _ => return None,
        })
    }

    fn difference(&self, raw: usize, format: Format) -> Option<(usize, usize)> {
        let Value::Float(float, ref operands) = self.values[raw] else {
            return None;
        };
        if float.format != format || float.operation != FloatOp::Sub {
            return None;
        }
        let &[a, b] = operands.as_slice() else {
            return None;
        };
        Some((a, b))
    }

    fn comparison(&self, id: usize, scope: &[usize]) -> Option<FloatComparison> {
        let Value::Natural(Operation::LessThan { yes, no }, observed, limit) = self.values[id]
        else {
            return None;
        };
        let (format, sign, infinity) = self.limits(limit)?;
        let Value::Choice(_, ref arms) = self.values[observed] else {
            return None;
        };
        for &(_, raw) in arms {
            let Some((a, b)) = self.difference(raw, format) else {
                continue;
            };
            // Only -0 minus +0 is negative zero while the operands compare equal.
            if self.number(a).is_none_or(|n| n & format.greatest() == sign)
                && self.number(b).is_none_or(|n| n & format.greatest() == 0)
            {
                continue;
            }
            let select = |category| self.select(observed, raw, (sign, infinity), category, 16);
            if select(0) != Some(raw) || select(1) != Some(raw) {
                continue;
            }
            if select(2)
                .and_then(|n| self.number(n))
                .is_none_or(|n| n >= sign)
            {
                continue;
            }
            return Some(FloatComparison {
                format,
                left: Atom(Local::at(scope.iter().position(|&n| n == a)?)),
                right: Atom(Local::at(scope.iter().position(|&n| n == b)?)),
                yes,
                no,
            });
        }
        None
    }

    fn magnitude(&self, id: usize, raw: usize, sign: u64) -> bool {
        match self.values[id] {
            Value::Natural(Operation::Mod, value, limit) => {
                value == raw && self.number(limit) == Some(sign)
            }
            Value::Natural(Operation::And, value, mask) => {
                value == raw && self.number(mask) == Some(sign - 1)
            }
            _ => false,
        }
    }

    /// Evaluate only the bounded decision tree testing magnitude against infinity.
    /// Categories are below infinity, exactly infinity, and above infinity.
    fn select(
        &self,
        id: usize,
        raw: usize,
        limits: (u64, u64),
        category: u8,
        depth: u8,
    ) -> Option<usize> {
        let Value::Choice(on, ref arms) = self.values[id] else {
            return Some(id);
        };
        let depth = depth.checked_sub(1)?;
        let selected = self.select(on, raw, limits, category, depth)?;
        let tag = match self.values[selected] {
            Value::Number(n) => n,
            Value::Natural(operation, left, right)
                if self.magnitude(left, raw, limits.0) && self.number(right) == Some(limits.1) =>
            {
                let ctor = match operation {
                    Operation::LessThan { yes, no } => {
                        if category == 0 {
                            yes
                        } else {
                            no
                        }
                    }
                    Operation::Equals { yes, no } => {
                        if category == 1 {
                            yes
                        } else {
                            no
                        }
                    }
                    _ => return None,
                };
                u64::from(self.program.tag(ctor))
            }
            _ => return None,
        };
        let &(_, next) = arms
            .iter()
            .find(|&&(ctor, _)| u64::from(self.program.tag(ctor)) == tag)?;
        self.select(next, raw, limits, category, depth)
    }
}
