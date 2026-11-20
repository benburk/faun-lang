//! Recognize rotation from natural arithmetic before choosing a word size.
use num_traits::ToPrimitive;
use std::rc::Rc;

use super::{Atom, Body, Expr, ExprId, FnId, Operation, Program, TypeShape, type_shape};

/// A left rotation of the first parameter by the second modulo `bits`.
/// The input must fit in `bits`; Facts checks that range before exposing it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rotation {
    pub bits: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Parameter(usize),
    Number(u128),
    Call(Operation, Rc<Self>, Rc<Self>),
}

struct Reader<'a> {
    program: &'a Program,
    operations: &'a [Option<Operation>],
    remaining: usize,
}

impl Reader<'_> {
    fn body(&mut self, body: Body, mut scope: Vec<Rc<Term>>) -> Option<Rc<Term>> {
        for &id in self.program.bindings(body.bindings) {
            scope.push(self.expr(id, &scope)?);
        }
        self.expr(body.tail, &scope)
    }

    fn constant(&self, value: super::ConstId) -> Option<Rc<Term>> {
        let value = super::single_field_constant(self.program, self.program.constant(value));
        let super::ConstantView::Natural(number) = value.view() else {
            return None;
        };
        Some(Rc::new(Term::Number(number.to_biguint().to_u128()?)))
    }

    fn expr(&mut self, id: ExprId, scope: &[Rc<Term>]) -> Option<Rc<Term>> {
        self.remaining = self.remaining.checked_sub(1)?;
        let atom = |a: Atom| scope[a.0.index()].clone();
        match self.program.expr(id) {
            Expr::Atom(a) => Some(atom(a)),
            Expr::Static(value) => self.constant(value),
            Expr::Call(callee, args) => {
                let operation = self.operations[callee.index()]?;
                let &[a, b] = self.program.atoms(args) else {
                    return None;
                };
                Some(Rc::new(Term::Call(operation, atom(a), atom(b))))
            }
            Expr::Con(ctor, fields)
                if matches!(
                    type_shape(self.program, self.program.ctor(ctor).owner),
                    TypeShape::Wrapper { .. }
                ) =>
            {
                Some(atom(self.program.atoms(fields)[0]))
            }
            Expr::Match(on, arms) => {
                let [arm] = self.program.arms(arms) else {
                    return None;
                };
                if !matches!(
                    type_shape(self.program, self.program.ctor(arm.ctor).owner),
                    TypeShape::Wrapper { .. }
                ) {
                    return None;
                }
                let mut inner = scope.to_vec();
                inner.push(atom(on));
                self.body(arm.body, inner)
            }
            Expr::Con(..) => None,
        }
    }
}

fn call(term: &Term, operation: Operation) -> Option<(&Term, &Term)> {
    match term {
        Term::Call(found, left, right) if *found == operation => Some((left, right)),
        _ => None,
    }
}

/// Only bounded structural matching runs here. Names and machine widths are absent.
pub(super) fn recognize(
    program: &Program,
    operations: &[Option<Operation>],
) -> Vec<Option<Rotation>> {
    (0..program.functions().len())
        .map(|at| {
            let id = FnId::at(at);
            if operations[at].is_some() || program.params(id).len() != 2 {
                return None;
            }
            let mut reader = Reader {
                program,
                operations,
                remaining: 128,
            };
            let answer = reader.body(
                program.function(id).body()?,
                vec![Rc::new(Term::Parameter(0)), Rc::new(Term::Parameter(1))],
            )?;
            let (left, right) = call(&answer, Operation::Add)?;
            recognize_parts(left, right).or_else(|| recognize_parts(right, left))
        })
        .collect()
}

fn recognize_parts(low: &Term, high: &Term) -> Option<Rotation> {
    let (moved, limit) = call(low, Operation::Mod)?;
    let (other, divisor) = call(high, Operation::Div)?;
    if moved != other || limit != divisor {
        return None;
    }
    let &Term::Number(limit) = limit else {
        return None;
    };
    if !limit.is_power_of_two() {
        return None;
    }
    let bits = u16::try_from(limit.trailing_zeros()).ok()?;
    if !matches!(bits, 8 | 16 | 32 | 64) {
        return None;
    }
    let (value, power) = call(moved, Operation::Mul)?;
    if value != &Term::Parameter(0) {
        return None;
    }
    let (two, count) = call(power, Operation::Pow)?;
    let (amount, modulus) = call(count, Operation::Mod)?;
    (two == &Term::Number(2)
        && amount == &Term::Parameter(1)
        && modulus == &Term::Number(u128::from(bits)))
        .then_some(Rotation { bits })
}
