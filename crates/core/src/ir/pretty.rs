//! Diagnostic text with explicit values, classes and region edges, not pool runs.

use std::fmt::Write;

use super::{Class, Definition, FunctionId, Op, Program, Returns, ValueId};

const CLASS_LEGEND: &str = "\
# Classes are per-value representation requirements, not source types.
# low..high is every value one can be; it is a fit requirement, not a
# wrapping type, and a target holds one in whatever it has that is wide
# enough. A narrower sink requires a fit proof or an explicit conversion.

";

impl Program {
    /// Render declarations and regions in storage order.
    ///
    /// Region IDs make structured control flow explicit without recursively
    /// expanding it. This is diagnostic text, not a serialization or source language.
    /// References and pool ranges must be well formed, as for other queries;
    /// pending definitions and missing terminators are rendered explicitly.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::new();
        if !self.functions().is_empty() {
            out.push_str(CLASS_LEGEND);
        }
        if let Some(layout) = self.layout() {
            let _ = writeln!(out, "layout {layout:?}");
        }
        if !self.data().is_empty() {
            let _ = writeln!(out, "data = {:02x?}", self.data());
        }
        if !self.globals().is_empty() {
            let _ = writeln!(out, "globals = {:02x?}", self.globals());
        }
        for (id, span) in self.spans.iter().enumerate() {
            let end = u64::from(span.start) + u64::from(span.len);
            let _ = writeln!(out, "d{id} = {:?}[{}..{end}]", span.origin, span.start);
        }
        self.render_shapes(&mut out);
        for (id, function) in self.functions().iter().enumerate() {
            let params = self.render_params(FunctionId::at(id));
            let returns = match function.returns {
                Returns::Never => "never".to_owned(),
                Returns::Values(classes) => format!("({})", class_list(self.signature(classes))),
            };
            let body = match function.definition {
                Definition::External => "external".to_owned(),
                Definition::Declared(root) => format!("pending r{}", root.index()),
                Definition::Body(root) => format!("r{}", root.index()),
            };
            let _ = writeln!(
                out,
                "fn f{id} {}({params}) -> {returns} = {body}",
                self.name(function.name)
            );
        }
        self.render_regions(&mut out);
        out
    }

    /// Each shape an object or an element is stored as, by the leaves it
    /// names.
    fn render_shapes(&self, out: &mut String) {
        for shape in self.shape_ids() {
            let _ = writeln!(
                out,
                "s{} = ({})",
                shape.index(),
                class_list(self.shaped(shape))
            );
        }
    }

    fn render_params(&self, id: FunctionId) -> String {
        let function = self.function(id);
        self.parameter_names(id)
            .zip(self.signature(function.params))
            .map(|(name, held)| format!("{name}: {}", class(*held)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn render_regions(&self, out: &mut String) {
        for id in self.regions.ids() {
            let region = self.region(id);
            let _ = writeln!(
                out,
                "\nr{}({}):",
                id.index(),
                self.bindings(self.values(region.params))
            );
            for (op, results) in self.walk(id) {
                out.push_str("  ");
                if !results.is_empty() {
                    let _ = write!(out, "{} = ", self.bindings(results));
                }
                let _ = writeln!(out, "{}", self.render_op(*op, results));
            }
            if let Some(term) = region.terminator {
                let _ = writeln!(
                    out,
                    "  {:?}({})",
                    term.exit,
                    arguments(self.values(term.values))
                );
            } else {
                out.push_str("  <no terminator>\n");
            }
        }
    }

    fn bindings(&self, values: &[ValueId]) -> String {
        values
            .iter()
            .map(|&v| format!("v{}: {}", v.index(), class(self.class(v))))
            .collect::<Vec<_>>()
            .join(", ")
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one textual form per operation in an exhaustive match"
    )]
    fn render_op(&self, op: Op, results: &[ValueId]) -> String {
        match op {
            Op::Constant { value, .. } => format!("const {value}"),
            Op::NaturalConstant(data) => format!("natural d{}", data.index()),
            Op::AddressOf(data) => format!("address d{}", data.index()),
            Op::Cell { tag, fields, shape } => {
                format!(
                    "cell {tag}({}) as s{}",
                    arguments(self.values(fields)),
                    shape.index()
                )
            }
            Op::CellTag { cell } => format!("cell_tag v{}", cell.index()),
            Op::CellField { cell, index, shape } => {
                format!(
                    "cell_field v{}, {index} of s{}",
                    cell.index(),
                    shape.index()
                )
            }
            Op::BufferEmpty => "buffer_empty".to_owned(),
            Op::BufferPush {
                buffer,
                len,
                fields,
                shape,
            } => format!(
                "buffer_push v{}, v{}, ({}) as s{}",
                buffer.index(),
                len.index(),
                arguments(self.values(fields)),
                shape.index()
            ),
            Op::BufferPrepend {
                buffer,
                len,
                from,
                from_len,
                reversed,
            } => format!(
                "buffer_prepend{} v{}, v{}, v{}, v{}",
                if reversed { "_reversed" } else { "" },
                buffer.index(),
                len.index(),
                from.index(),
                from_len.index()
            ),
            Op::BufferField {
                buffer,
                len,
                index,
                shape,
            } => {
                format!(
                    "buffer_field v{}, v{}, {index} of s{}",
                    buffer.index(),
                    len.index(),
                    shape.index()
                )
            }
            Op::Binary { op, left, right } => {
                format!("{op:?} v{}, v{}", left.index(), right.index())
            }
            Op::Float { float, operands } => {
                format!("{float} {}", arguments(self.values(operands)))
            }
            Op::Shift {
                direction,
                value,
                by,
            } => format!("{direction:?} v{} by {by}", value.index()),
            Op::Compare {
                relation,
                left,
                right,
            } => format!("{relation:?} v{}, v{}", left.index(), right.index()),
            Op::Load {
                width,
                address,
                offset,
            } => format!("load.{width:?} v{}, {offset:?}", address.index()),
            Op::Store {
                width,
                address,
                offset,
                value,
            } => format!(
                "store.{width:?} v{}, {offset:?}, v{}",
                address.index(),
                value.index()
            ),
            // The class is the one the value it writes is held at, shown
            // beside that value already; saying it again here is for whoever
            // reads a conversion and wants to see what it converts to.
            Op::Convert { value } => format!(
                "convert v{} to {}",
                value.index(),
                class(self.class(results[0]))
            ),
            Op::Call { function, args } => format!(
                "call {}({})  # f{}",
                self.name(self.function(function).name),
                arguments(self.values(args)),
                function.index()
            ),
            Op::If {
                condition,
                then_region,
                else_region,
            } => format!(
                "if v{} then r{} else r{}",
                condition.index(),
                then_region.index(),
                else_region.index()
            ),
            Op::Loop { initial, body } => format!(
                "loop r{}({})",
                body.index(),
                arguments(self.values(initial))
            ),
        }
    }
}

fn class(held: Class) -> String {
    match held {
        Class::Cell => "cell".to_owned(),
        Class::Buffer => "buffer".to_owned(),
        Class::Natural => "natural".to_owned(),
        Class::Word => "word".to_owned(),
        Class::Address => "address".to_owned(),
        // What is known, not how wide it makes the value. A width rounds
        // the greatest up to the next power of two and says nothing of the
        // least, so it hides what this tier was told.
        Class::Held(facts) => facts.high.map_or_else(
            || format!("{}..", facts.low),
            |high| format!("{}..{high}", facts.low),
        ),
    }
}

fn class_list(classes: &[Class]) -> String {
    classes
        .iter()
        .map(|&c| class(c))
        .collect::<Vec<_>>()
        .join(", ")
}

fn arguments(values: &[ValueId]) -> String {
    values
        .iter()
        .map(|v| format!("v{}", v.index()))
        .collect::<Vec<_>>()
        .join(", ")
}
