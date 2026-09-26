//! Rebuilding a program, which is how a pass over machine IR changes one.
//!
//! Values, instructions and regions live in arenas addressed by position, so
//! nothing can be taken out of one where it stands: removing an instruction
//! would renumber every value after it, and every operand naming one. A pass
//! therefore reads one program and writes another.
//!
//! What every pass would otherwise write for itself is the walk between the
//! two -- the exhaustive descent past `If` and `Loop`, and the map from a
//! value in the old program to whatever stands for it in the new one. That
//! is here, once, so a pass is only the decision it came to make.
//!
//! A pass supplies [`Pass::op`]. Answering `false` copies the instruction;
//! answering `true` means the pass wrote what it wanted instead and said,
//! through [`Rebuild::stands_for`], which value each old result now names.
//! A pass that changes what crosses a boundary also answers [`Pass::enter`]
//! and [`Pass::exit`], and hands [`rebuild_declared`] the declarations it
//! rewrote.

use std::cell::Cell;

use crate::index::Pool;

use super::model::Parameter;
use super::{
    Builder, Class, Definition, Exit, Function, FunctionId, Op, Program, Range, RegionId,
    Terminator, ValueId,
};

/// One decision, made instruction by instruction.
pub(super) trait Pass {
    /// Write what this instruction becomes, or answer `false` to copy it.
    ///
    /// A pass that writes nothing and points the old results at values it
    /// already has is how an instruction goes away.
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool;

    /// Open a function's body: what each of the old body's parameters is,
    /// given the new body's. A pass that keeps signatures keeps these.
    fn enter(
        &mut self,
        _rebuild: &Rebuild<'_>,
        _b: &mut Builder,
        _function: FunctionId,
        params: &[ValueId],
    ) -> Vec<ValueId> {
        params.to_vec()
    }

    /// Write how a region leaves, or answer `false` to copy it.
    fn exit(&mut self, _rebuild: &Rebuild<'_>, _b: &mut Builder, _terminator: Terminator) -> bool {
        false
    }
}

/// Every function declaration, and the pools their signatures and parameter
/// names are runs of. A pass changing signatures writes new ones; the
/// function IDs, names and definitions they describe stay as they were.
pub(super) struct Declarations {
    pub functions: Pool<FunctionId, Function>,
    pub signature: Vec<Class>,
    pub parameters: Vec<Parameter>,
}

impl Declarations {
    /// The declarations as `source` has them.
    pub(super) fn of(source: &Program) -> Self {
        Self {
            functions: source.functions.clone(),
            signature: source.signature.clone(),
            parameters: source.parameters.clone(),
        }
    }
}

/// The old program, and what the new one calls each of its values.
pub(super) struct Rebuild<'a> {
    source: &'a Program,
    /// Interior mutability because the walk hands `&self` to the builder's
    /// region callbacks, which is where most values come to stand for one
    /// another.
    values: Vec<Cell<Option<ValueId>>>,
}

/// Read `source`, writing what `pass` makes of it.
///
/// Data, globals, names, function declarations and function IDs are carried
/// over untouched; only bodies are walked. An external declaration has no
/// body and is copied as it stands.
pub(super) fn rebuild<P: Pass>(source: &Program, pass: &mut P) -> Program {
    rebuild_declared(source, Declarations::of(source), pass)
}

/// Read `source` into a program declared as `declared` says.
///
/// Each function keeps its ID and definition kind; a body is opened with
/// parameters minted from its new signature and handed to [`Pass::enter`].
pub(super) fn rebuild_declared<P: Pass>(
    source: &Program,
    declared: Declarations,
    pass: &mut P,
) -> Program {
    let mut output = skeleton(source, declared);
    let rebuild = Rebuild {
        source,
        values: vec![Cell::new(None); source.values_count()],
    };
    for (id, function) in source.functions.iter_enumerated() {
        let Some(body) = function.body() else {
            continue;
        };
        output.define(id, |b, params| {
            let params = pass.enter(&rebuild, b, id, params);
            rebuild.region(b, body, &params, pass);
        });
    }
    output
}

/// The same program with its bodies emptied: every pool a rebuild keeps,
/// and none of the arenas it writes again.
fn skeleton(source: &Program, declared: Declarations) -> Program {
    let mut output = Program {
        layout: source.layout,
        runtime_cells: source.runtime_cells,
        runtime_naturals: source.runtime_naturals,
        data: source.data.clone(),
        globals: source.globals.clone(),
        spans: source.spans.clone(),
        functions: declared.functions,
        classes: Pool::default(),
        signature: declared.signature,
        parameters: declared.parameters,
        ops: Vec::new(),
        results: Vec::new(),
        operands: Vec::new(),
        regions: Pool::default(),
        names: source.names.clone(),
        symbols: source.symbols.clone(),
        shapes: source.shapes.clone(),
        shaped: source.shaped.clone(),
    };
    for id in output.functions.ids() {
        if output.functions[id].body().is_some() {
            let params = output.mint_from(output.functions[id].params);
            let body = output.regions.push(super::Region {
                params,
                ops: Range::EMPTY,
                terminator: None,
            });
            output.functions[id].definition = Definition::Declared(body);
        }
    }
    output
}

impl<'a> Rebuild<'a> {
    /// The program being read.
    #[must_use]
    pub(super) const fn source(&self) -> &'a Program {
        self.source
    }

    /// What the new program calls an old value.
    ///
    /// # Panics
    /// If the value has not been written yet, which validated IR cannot ask
    /// for: an operand names something the walk has already passed.
    #[must_use]
    pub(super) fn value(&self, old: ValueId) -> ValueId {
        self.values[old.index()]
            .get()
            .expect("a value written before it is read")
    }

    /// Say that `new` is what the new program has instead of `old`.
    pub(super) fn stands_for(&self, old: ValueId, new: ValueId) {
        self.values[old.index()].set(Some(new));
    }

    /// What the new program has instead of `old` so far, if anything, and
    /// saying so again, for a pass that names an old value differently
    /// within one region and then as it was.
    pub(super) fn standing(&self, old: ValueId) -> Option<ValueId> {
        self.values[old.index()].get()
    }

    pub(super) fn restand(&self, old: ValueId, new: Option<ValueId>) {
        self.values[old.index()].set(new);
    }

    /// A run of operands, each as the new program names it.
    #[must_use]
    pub(super) fn args(&self, operands: Range) -> Vec<ValueId> {
        self.source
            .values(operands)
            .iter()
            .map(|&old| self.value(old))
            .collect()
    }

    /// The classes a run of results is held at.
    #[must_use]
    pub(super) fn classes(&self, results: &[ValueId]) -> Vec<Class> {
        results.iter().map(|&old| self.source.class(old)).collect()
    }

    /// Write a region's instructions, then how it leaves.
    ///
    /// `params` are what the new region was opened with, standing for the
    /// old region's own.
    pub(super) fn region<P: Pass>(
        &self,
        b: &mut Builder,
        region: RegionId,
        params: &[ValueId],
        pass: &mut P,
    ) {
        let old = self.source.region(region);
        for (&was, &now) in self.source.values(old.params).iter().zip(params) {
            self.stands_for(was, now);
        }
        for (op, results) in self.source.walk(region) {
            if !pass.op(self, b, *op, results) {
                self.copy(b, *op, results, pass);
            }
        }
        if let Some(terminator) = old.terminator
            && !pass.exit(self, b, terminator)
        {
            self.exit(b, terminator);
        }
    }

    /// Write one instruction as it stands, with its operands renamed and any
    /// region it holds walked through `pass`.
    pub(super) fn copy<P: Pass>(&self, b: &mut Builder, op: Op, results: &[ValueId], pass: &mut P) {
        let fresh = match op {
            Op::If {
                condition,
                then_region,
                else_region,
            } => self.if_(
                b,
                self.value(condition),
                results,
                then_region,
                else_region,
                pass,
            ),
            Op::Loop { initial, body } => {
                // A loop goes round at the classes it was written with,
                // however much narrower what now starts it is.
                let params = self.source.values(self.source.region(body).params);
                let initial: Vec<_> = self
                    .args(initial)
                    .into_iter()
                    .zip(params)
                    .map(|(value, &param)| {
                        let class = self.source.class(param);
                        if b.class(value) == class {
                            value
                        } else {
                            b.convert(class, value)
                        }
                    })
                    .collect();
                b.loop_(&initial, &self.classes(results), |b, params| {
                    self.region(b, body, params, pass);
                })
            }
            held => self.plain(b, held, results),
        };
        for (&was, now) in results.iter().zip(fresh) {
            self.stands_for(was, now);
        }
    }

    /// The instructions that hold no region: each written again, reading
    /// whatever the new program has instead of what the old one read.
    ///
    /// # Panics
    /// If handed one that does hold a region, which [`Self::copy`] takes
    /// first because a region is walked rather than named.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per instruction; the length is the patterns"
    )]
    fn plain(&self, b: &mut Builder, op: Op, results: &[ValueId]) -> Vec<ValueId> {
        match op {
            Op::Constant { value } => vec![b.constant(self.source.class(results[0]), value)],
            Op::NaturalConstant(data) => vec![b.kept_natural(data)],
            Op::AddressOf(data) => vec![b.address_of(data)],
            Op::Cell { tag, fields, shape } => vec![b.cell(tag, shape, &self.args(fields))],
            Op::CellTag { cell } => vec![b.cell_tag(self.value(cell))],
            Op::BufferEmpty { shape } => vec![b.buffer_empty(shape)],
            Op::BufferKnown { elements, shape } => vec![b.buffer_known(elements, shape)],
            Op::BufferPush { operands, shape } => {
                let operands = self.args(operands);
                let (sequence, fields) = operands.split_at(3);
                b.buffer_push((sequence[0], sequence[1], sequence[2]), shape, fields)
                    .to_vec()
            }
            Op::BufferPrepend { operands, shape } => {
                let operands = self.args(operands);
                b.buffer_prepend(
                    (operands[0], operands[1], operands[2]),
                    (operands[3], operands[4], operands[5]),
                    shape,
                )
                .to_vec()
            }
            Op::BufferExtend { operands, shape } => {
                let operands = self.args(operands);
                b.buffer_extend(
                    (operands[0], operands[1], operands[2]),
                    (operands[3], operands[4], operands[5]),
                    shape,
                )
                .to_vec()
            }
            Op::BufferRoom { count, shape } => vec![b.buffer_room(self.value(count), shape)],
            Op::BufferAt {
                buffer,
                start,
                shape,
            } => vec![b.buffer_at((self.value(buffer), self.value(start)), shape)],
            Op::Keep { value } => {
                b.keep(self.value(value));
                Vec::new()
            }
            Op::BufferField {
                buffer,
                start,
                index,
                shape,
            } => vec![b.buffer_field(
                (self.source.class(results[0]), shape),
                (self.value(buffer), self.value(start)),
                index,
            )],
            Op::CellField { cell, index, shape } => vec![b.cell_field(
                (self.source.class(results[0]), shape),
                self.value(cell),
                index,
            )],
            Op::Binary { op, left, right } => vec![b.binary_at(
                self.source.class(results[0]),
                op,
                self.value(left),
                self.value(right),
            )],
            Op::Compare {
                relation,
                left,
                right,
            } => vec![b.compare(relation, self.value(left), self.value(right))],
            Op::Load {
                width,
                address,
                offset,
            } => vec![b.load(width, self.value(address), offset)],
            Op::Store {
                width,
                address,
                offset,
                value,
            } => {
                b.store(width, self.value(address), offset, self.value(value));
                Vec::new()
            }
            Op::Float { float, operands } => vec![b.float(float, &self.args(operands))],
            Op::Convert { value } => {
                vec![b.convert(self.source.class(results[0]), self.value(value))]
            }
            Op::Shift {
                direction,
                value,
                by,
            } => vec![b.shift(
                self.source.class(results[0]),
                direction,
                self.value(value),
                by,
            )],
            Op::Call { function, args } => b.call(function, &self.args(args)),
            Op::If { .. } | Op::Loop { .. } => unreachable!("a region is walked, not written"),
        }
    }

    /// An `if` whose arms are two of the old program's regions, in the order
    /// given. A pass swapping them writes the same call with the regions the
    /// other way round.
    pub(super) fn if_<P: Pass>(
        &self,
        b: &mut Builder,
        condition: ValueId,
        results: &[ValueId],
        then_region: RegionId,
        else_region: RegionId,
        pass: &mut P,
    ) -> Vec<ValueId> {
        // Both arms walk with the same pass, and `if_` builds them one after
        // the other, so they share it in turn rather than at once.
        let pass = std::cell::RefCell::new(pass);
        b.if_(
            condition,
            &self.classes(results),
            |b| {
                let mut pass = pass.borrow_mut();
                self.region(b, then_region, &[], &mut **pass);
            },
            |b| {
                let mut pass = pass.borrow_mut();
                self.region(b, else_region, &[], &mut **pass);
            },
        )
    }

    /// How a region leaves, with what it carries renamed.
    fn exit(&self, b: &mut Builder, terminator: Terminator) {
        let values = self.args(terminator.values);
        match terminator.exit {
            Exit::Return => b.ret(&values),
            Exit::Yield => b.yield_(&values),
            Exit::Continue => b.continue_(&values),
            Exit::Break => b.break_(&values),
        }
    }
}
