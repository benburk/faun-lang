//! Value identities applied before storage or instruction selection.
use super::{Atom, Expr, FnId, Rewrite, Scope};
use faun_base::float::{Float, Format, Operation};

impl Rewrite<'_> {
    /// Reverse a bounded constructor chain directly onto its destination.
    /// Fields are already evaluated atoms, so effects retain their order.
    pub(super) fn short_reverse(
        &mut self,
        called: FnId,
        args: &[Atom],
        scope: &mut Scope,
    ) -> Option<Atom> {
        let ty = self.program.params(called)[0];
        let (_, push, recursive) = super::super::sequence::sequence(self.program, ty)?;
        let mut rest = args[0];
        let mut elements = Vec::new();
        while !self.empty(rest, ty) {
            if elements.len() == 4 {
                return None;
            }
            let written = (*self.written.get(rest.0.index())?)?;
            let Expr::Con(ctor, fields) = self.program.expr(written) else {
                return None;
            };
            if ctor != push {
                return None;
            }
            let fields = self.program.atoms(fields);
            elements.push(fields[1 - recursive]);
            rest = fields[recursive];
        }
        let mut answer = args[1];
        for element in elements {
            let mut fields = [element; 2];
            fields[recursive] = answer;
            let fields = self.program.terms.hold_atoms(fields.into_iter());
            answer = self.push(Expr::Con(push, fields), scope);
        }
        Some(answer)
    }

    fn float_bits(&self, atom: Atom) -> Option<u64> {
        let value = self.program.constant(self.known(atom)?);
        let value = super::super::single_field_constant(self.program, value);
        match value.view() {
            super::super::ConstantView::Natural(n) => n.try_u64().ok(),
            _ => None,
        }
    }

    /// Under Faun's IEEE semantics, doubling has the same rounded result
    /// through addition, including infinities and the sign of zero.
    pub(super) fn float_double(
        &mut self,
        called: FnId,
        args: &[Atom],
        scope: &mut Scope,
    ) -> Option<Atom> {
        let float = self.recognised.floats[called.index()]?;
        if float.operation != Operation::Mul {
            return None;
        }
        let two = match float.format {
            Format::Binary32 => u64::from(2.0f32.to_bits()),
            Format::Binary64 => 2.0f64.to_bits(),
        };
        let value = if self.float_bits(args[0]) == Some(two) {
            args[1]
        } else if self.float_bits(args[1]) == Some(two) {
            args[0]
        } else {
            return None;
        };
        let add = Float {
            operation: Operation::Add,
            ..float
        };
        let function = self
            .recognised
            .floats
            .iter()
            .enumerate()
            .find_map(|(at, found)| {
                let id = FnId::at(at);
                (*found == Some(add)
                    && self.program.params(id) == self.program.params(called)
                    && self.program.function(id).result == self.program.function(called).result)
                    .then_some(id)
            })?;
        let args = self.program.terms.hold_atoms([value, value].into_iter());
        Some(self.push(Expr::Call(function, args), scope))
    }
}
