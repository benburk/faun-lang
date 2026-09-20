//! Diagnostic text with explicit values, classes and region edges, not pool runs.

use std::fmt::Write;

use super::{Class, Definition, Op, Program, Returns, ValueId};

const CLASS_LEGEND: &str = "\
# Classes are per-value representation requirements, not source types.
# fixedN means 0 <= value < 2^N; it is a fit requirement, not a wrapping type.
# A narrower sink requires a fit proof or an explicit conversion.

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
        for (id, function) in self.functions().iter().enumerate() {
            let params = class_list(self.signature(function.params));
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
                let _ = writeln!(out, "{}", self.render_op(*op));
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
    fn render_op(&self, op: Op) -> String {
        match op {
            Op::Constant { value, .. } => format!("const {value}"),
            Op::NaturalConstant(data) => format!("natural d{}", data.index()),
            Op::AddressOf(data) => format!("address d{}", data.index()),
            Op::Binary { op, left, right } => {
                format!("{op:?} v{}, v{}", left.index(), right.index())
            }
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
            Op::Convert { class: to, value } => {
                format!("convert v{} to {}", value.index(), class(to))
            }
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
        Class::Natural => "natural".to_owned(),
        Class::Word => "word".to_owned(),
        Class::Address => "address".to_owned(),
        Class::Fixed { bits } => format!("fixed{bits}"),
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
