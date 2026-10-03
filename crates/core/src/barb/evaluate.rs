//! Bounded evaluation over validated compact constants, not unary trees.
//! A value's structural kind and a reason not to fold are separate concepts.

use super::budget::{Budget, LimitExceeded};
use super::constant::{ConstantView, ConstructionError, Held, natural_size};
use super::{Body, Expr, ExprId, Operation, Program, TypeId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CannotFold {
    DynamicInput,
    ExternalCall,
    Limit(LimitExceeded),
}

impl From<LimitExceeded> for CannotFold {
    fn from(limit: LimitExceeded) -> Self {
        Self::Limit(limit)
    }
}

pub(super) type Evaluation = Result<Held, CannotFold>;

pub(super) struct Evaluator<'a> {
    pub program: &'a Program,
    pub operations: &'a [Option<Operation>],
}

impl Evaluator<'_> {
    pub(super) fn expr(&self, id: ExprId, env: &[Evaluation], budget: &mut Budget) -> Evaluation {
        budget.descend(|budget| self.expr_inner(id, env, budget))
    }

    fn args(
        &self,
        range: super::Range,
        env: &[Evaluation],
        budget: &mut Budget,
    ) -> Result<Vec<Held>, CannotFold> {
        let atoms = self.program.atoms(range);
        budget.spend(u64::try_from(atoms.len()).map_err(|_| LimitExceeded::Work)?)?;
        // Charge before allocating the argument vector or cloning values.
        for a in atoms {
            budget.bytes(env[a.0.index()].as_ref().map_err(|e| *e)?.encoded().len())?;
        }
        atoms.iter().map(|a| env[a.0.index()].clone()).collect()
    }

    fn expr_inner(&self, id: ExprId, env: &[Evaluation], budget: &mut Budget) -> Evaluation {
        match self.program.expr(id) {
            Expr::Atom(a) => {
                let value = env[a.0.index()].as_ref().map_err(|e| *e)?;
                budget.bytes(value.encoded().len())?;
                Ok(value.clone())
            }
            Expr::Static(value) => Ok(self.program.constant(value).to_owned(budget)?),
            Expr::Con(ctor, fields) => {
                self.construct(ctor, &self.args(fields, env, budget)?, budget)
            }
            Expr::Call(called, fields) => {
                let fields = self.args(fields, env, budget)?;
                self.call(called, fields, budget)
            }
            Expr::Match(value, arms) => self.branch(
                env[value.0.index()].as_ref().map_err(|e| *e)?,
                arms,
                env,
                budget,
            ),
        }
    }

    /// A call's answer: from its operands where it is claimed or recognized,
    /// and otherwise by walking its body.
    pub(super) fn call(
        &self,
        called: super::FnId,
        fields: Vec<Held>,
        budget: &mut Budget,
    ) -> Evaluation {
        if let Some(answered) = self.answered(called, &fields, budget) {
            return answered;
        }
        let body = self
            .program
            .function(called)
            .body()
            .ok_or(CannotFold::ExternalCall)?;
        self.body(body, fields.into_iter().map(Ok).collect(), budget)
    }

    /// A call's answer from its operands, where it is claimed or recognized.
    fn answered(
        &self,
        called: super::FnId,
        fields: &[Held],
        budget: &mut Budget,
    ) -> Option<Evaluation> {
        let function = self.program.function(called);
        if let Some(float) = function.float {
            if let Err(limit) = budget.spend(u64::try_from(fields.len()).unwrap_or(u64::MAX)) {
                return Some(Err(limit.into()));
            }
            let answered =
                super::claim::answer(self.program, float, function.result, fields, budget);
            if answered.is_some() {
                return answered;
            }
        }
        let op = self.operations[called.index()]?;
        Some(self.arithmetic(op, function.result, fields, budget))
    }

    pub(super) fn construct(
        &self,
        ctor: super::CtorId,
        fields: &[Held],
        budget: &mut Budget,
    ) -> Evaluation {
        match Held::build(self.program.type_info(), ctor, fields, budget) {
            Ok(value) => Ok(value),
            Err(ConstructionError::Limit(limit)) => Err(limit.into()),
            Err(error) => panic!("ill-typed Barb construction: {error}"),
        }
    }

    fn branch(
        &self,
        held: &Held,
        arms: super::Range,
        env: &[Evaluation],
        budget: &mut Budget,
    ) -> Evaluation {
        let (ctor, fields) = held.as_constant(self.program.type_info()).parts(budget)?;
        let arm = self
            .program
            .arms(arms)
            .iter()
            .find(|a| a.ctor == ctor)
            .expect("an exhaustive match");
        budget.spend(u64::try_from(env.len()).map_err(|_| LimitExceeded::Work)?)?;
        for value in env.iter().flatten() {
            budget.bytes(value.encoded().len())?;
        }
        let mut inner = env.to_vec();
        inner.extend(fields.into_iter().map(Ok));
        self.body(arm.body, inner, budget)
    }

    pub(super) fn arithmetic(
        &self,
        op: Operation,
        result: TypeId,
        fields: &[Held],
        budget: &mut Budget,
    ) -> Evaluation {
        // Recognition proves the operand shapes. Arguments are already size-checked.
        let (ConstantView::Natural(a), ConstantView::Natural(b)) = (
            fields[0].as_constant(self.program.type_info()).view(),
            fields[1].as_constant(self.program.type_info()).view(),
        ) else {
            panic!("recognized arithmetic takes naturals");
        };
        let (a, b) = (a.to_biguint(), b.to_biguint());
        let bits = a.bits().max(b.bits());
        let output = match op {
            Operation::Add => bits.saturating_add(1),
            Operation::Mul => a.bits().saturating_add(b.bits()),
            Operation::Pow => a
                .bits()
                .saturating_mul(u64::try_from(&b).unwrap_or(u64::MAX))
                .max(1),
            _ => bits,
        };
        budget.bytes(natural_size(output)?)?;
        let words = |bits: u64| bits.div_ceil(64).max(1);
        let work = match op {
            Operation::Mul => words(a.bits()).saturating_mul(words(b.bits())),
            Operation::Pow => words(output).saturating_mul(words(output)),
            Operation::Div | Operation::Mod => words(bits).saturating_mul(words(bits)),
            _ => words(bits),
        };
        budget.spend(work)?;
        if let Some(n) = op.calculate(&a, &b) {
            return Ok(Held::number(self.program.type_info(), result, &n));
        }
        let Some(ctor) = op.compare(&a, &b) else {
            return Err(LimitExceeded::ValueSize.into());
        };
        self.construct(ctor, &[], budget)
    }

    /// What `body` answers, where `env` holds what each local before it is.
    ///
    /// A tail taking a match's arm, or calling a definition answered by
    /// walking its body, goes on into that body here, in a loop rather than
    /// a level deeper: a loop as long as its input costs work, which the
    /// budget bounds, but not depth, which bounds what is nested.
    pub(super) fn body(
        &self,
        mut body: Body,
        mut env: Vec<Evaluation>,
        budget: &mut Budget,
    ) -> Evaluation {
        loop {
            for &binding in self.program.bindings(body.bindings) {
                // An unused eager binding may perform effects or fail to return.
                let value = self.expr(binding, &env, budget)?;
                env.push(Ok(value));
            }
            match self.program.expr(body.tail) {
                Expr::Match(value, arms) => {
                    budget.spend(1)?;
                    let held = env[value.0.index()].as_ref().map_err(|e| *e)?;
                    let (ctor, fields) =
                        held.as_constant(self.program.type_info()).parts(budget)?;
                    let arm = self
                        .program
                        .arms(arms)
                        .iter()
                        .find(|a| a.ctor == ctor)
                        .expect("an exhaustive match");
                    env.extend(fields.into_iter().map(Ok));
                    body = arm.body;
                }
                Expr::Call(called, args) => {
                    let fields = self.args(args, &env, budget)?;
                    if let Some(answered) = self.answered(called, &fields, budget) {
                        return answered;
                    }
                    budget.spend(1)?;
                    body = self
                        .program
                        .function(called)
                        .body()
                        .ok_or(CannotFold::ExternalCall)?;
                    env = fields.into_iter().map(Ok).collect();
                }
                Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => {
                    return self.expr(body.tail, &env, budget);
                }
            }
        }
    }
}
