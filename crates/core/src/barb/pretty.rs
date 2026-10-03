//! Rendering a program as text, so that one can be read.

use std::fmt::Write;

use super::model::{Body, ConstId, Expr, ExprId, FnId, Range, Symbol, TypeId};
use super::program::Program;
use super::{Operation, SequenceOperation};

impl Program {
    /// The whole program: its types, then its functions.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::new();
        for id in 0..self.types().len() {
            let id = TypeId::at(id);
            if !self.type_(id).is_inline() {
                self.render_type(id, &mut out);
            }
        }
        let shown = self.shown();
        let mut hidden = Vec::new();
        for (at, &shown) in shown.iter().enumerate() {
            let id = FnId::at(at);
            if shown {
                out.push('\n');
                self.render_function(id, &mut out);
            } else {
                hidden.push(self.name(self.function(id).name));
            }
        }
        if !hidden.is_empty() {
            let _ = writeln!(
                out,
                "\nCalled only by an answered body: {}",
                hidden.join(", ")
            );
        }
        out
    }

    /// Which definitions to render: all but those the entry reaches only
    /// by going into an answered definition's body. Those are what an
    /// answered operation's body is written with -- a target with the
    /// instruction never walks them -- and are only named.
    fn shown(&self) -> Vec<bool> {
        let count = self.functions().len();
        let Some(entry) = self.entry() else {
            return vec![true; count];
        };
        let through = self.reached(entry, true);
        let around = self.reached(entry, false);
        through
            .iter()
            .zip(around)
            .map(|(&through, around)| around || !through)
            .collect()
    }

    /// Which definitions `entry` reaches, going into answered definitions'
    /// bodies only where `answered` says to.
    fn reached(&self, entry: FnId, answered: bool) -> Vec<bool> {
        let mut reached = vec![false; self.functions().len()];
        let mut waiting = vec![entry];
        while let Some(id) = waiting.pop() {
            if std::mem::replace(&mut reached[id.index()], true) {
                continue;
            }
            if !answered && self.answered_as(id).is_some() {
                continue;
            }
            let Some(body) = self.function(id).body() else {
                continue;
            };
            waiting.extend(super::walk::within(self, body).filter_map(
                |expr| match self.expr(expr) {
                    Expr::Call(called, _) => Some(called),
                    _ => None,
                },
            ));
        }
        reached
    }

    fn render_type(&self, id: TypeId, out: &mut String) {
        let ctors: Vec<String> = self
            .ctors(id)
            .iter()
            .map(|ctor| {
                let names = self.field_names(ctor);
                let fields: Vec<String> = self
                    .types_of(ctor.fields)
                    .iter()
                    .zip(names)
                    .map(|(field, name)| {
                        let ty = self.name(self.type_(*field).name);
                        name.map_or_else(|| ty.to_owned(), |name| format!("{name}: {ty}"))
                    })
                    .collect();
                if fields.is_empty() {
                    self.name(ctor.name).to_owned()
                } else {
                    format!("{}({})", self.name(ctor.name), fields.join(", "))
                }
            })
            .collect();
        let name = self.name(self.type_(id).name);
        // A type with no constructors has nothing to be written equal to.
        let _ = if ctors.is_empty() {
            writeln!(out, "{name}")
        } else {
            writeln!(out, "{name} = {}", ctors.join(" | "))
        };
    }

    fn render_function(&self, id: FnId, out: &mut String) {
        let function = self.function(id);
        let params: Vec<String> = self
            .parameter_names(id)
            .zip(self.params(id))
            .map(|(name, type_)| format!("{name}: {}", self.name(self.type_(*type_).name)))
            .collect();
        let _ = write!(
            out,
            "{}({}) -> {} =",
            self.name(function.name),
            params.join(", "),
            self.name(self.type_(function.result).name)
        );
        if let Some(answered) = self.answered_as(id) {
            let _ = writeln!(out, " <{answered}>");
            return;
        }
        match function.body() {
            Some(body) => {
                out.push('\n');
                let level = u32::try_from(self.params(id).len()).expect("a sane arity");
                self.render_body(body, level, 1, out);
            }
            None => out.push_str(" <elsewhere>\n"),
        }
    }

    /// What a definition is answered as rather than walked, where it is:
    /// the IEEE 754 operation it is claimed to compute, or, once the program
    /// is analyzed, the operation it was recognized as. Its body is the
    /// operation's equations and says nothing new, so it is not rendered.
    fn answered_as(&self, id: FnId) -> Option<String> {
        if let Some(float) = self.function(id).float {
            return Some(float.to_string());
        }
        let facts = self.facts()?;
        if let Some(operation) = facts.operation(id) {
            let name = match operation {
                Operation::Add => "add",
                Operation::Monus => "monus",
                Operation::Mul => "mul",
                Operation::Div => "div",
                Operation::Mod => "mod",
                Operation::And => "and",
                Operation::Or => "or",
                Operation::Xor => "xor",
                Operation::Pow => "pow",
                Operation::Equals { .. } => "equals",
                Operation::LessThan { .. } => "less than",
            };
            return Some(name.to_owned());
        }
        let name = match facts.sequence_operation(id)? {
            SequenceOperation::Length => "length",
            SequenceOperation::ReverseOnto => "reverse onto",
            SequenceOperation::Prepend => "prepend",
            SequenceOperation::Append => "append",
            SequenceOperation::Drop => "drop",
            SequenceOperation::Take => "take",
            SequenceOperation::Replace => "replace",
        };
        Some(name.to_owned())
    }

    /// Each binding on its own line, then what the body answers.
    fn render_body(&self, body: Body, level: u32, depth: usize, out: &mut String) {
        let pad = "  ".repeat(depth);
        let mut level = level;
        for &binding in self.bindings(body.bindings) {
            let mut bound = String::new();
            self.render_expr(binding, level, depth, &mut bound);
            // A match bound to a name runs over several lines; the rest keep
            // the indentation they were rendered with.
            let text = bound.trim_end();
            let (first, rest) = text.split_once('\n').unwrap_or((text, ""));
            let _ = writeln!(out, "{pad}v{level} = {}", first.trim_start());
            if !rest.is_empty() {
                let _ = writeln!(out, "{rest}");
            }
            level += 1;
        }
        self.render_expr(body.tail, level, depth, out);
    }

    fn render_expr(&self, expr: ExprId, level: u32, depth: usize, out: &mut String) {
        let pad = "  ".repeat(depth);
        match self.expr(expr) {
            Expr::Atom(atom) => {
                let _ = writeln!(out, "{pad}v{}", atom.0.0);
            }
            Expr::Con(ctor, args) => {
                let _ = writeln!(out, "{pad}{}", self.render_call(self.ctor(ctor).name, args));
            }
            Expr::Call(function, args) => {
                let name = self.function(function).name;
                let _ = writeln!(out, "{pad}{}", self.render_call(name, args));
            }
            Expr::Static(value) => {
                let _ = writeln!(out, "{pad}{}", self.render_known(value));
            }
            Expr::Match(scrutinee, arms) => {
                let _ = writeln!(out, "{pad}match v{}", scrutinee.0.0);
                for arm in self.arms(arms) {
                    let fields = self.types_of(self.ctor(arm.ctor).fields).len();
                    let bound: Vec<String> = (0..fields)
                        .map(|at| format!("v{}", level + u32::try_from(at).expect("a sane arity")))
                        .collect();
                    let name = self.name(self.ctor(arm.ctor).name);
                    let _ = if bound.is_empty() {
                        writeln!(out, "{pad}  {name} =>")
                    } else {
                        writeln!(out, "{pad}  {name}({}) =>", bound.join(", "))
                    };
                    let inner = level + u32::try_from(fields).expect("a sane arity");
                    self.render_body(arm.body, inner, depth + 2, out);
                }
            }
        }
    }

    fn render_call(&self, name: Symbol, args: Range) -> String {
        let args: Vec<String> = self
            .atoms(args)
            .iter()
            .map(|atom| format!("v{}", atom.0.0))
            .collect();
        if args.is_empty() {
            self.name(name).to_owned()
        } else {
            format!("{}({})", self.name(name), args.join(", "))
        }
    }

    /// A known value as what it stands for, not as its bytes.
    fn render_known(&self, value: ConstId) -> String {
        let known = self.constant(value);
        match known.view() {
            super::ConstantView::Natural(number) => number.to_biguint().to_string(),
            super::ConstantView::Spine(spine) => {
                if let Some(run) = spine.to_bytes()
                    && let Ok(text) = std::str::from_utf8(&run)
                {
                    return format!("{text:?}");
                }
                format!("<{} bytes>", known.encoded().len())
            }
            super::ConstantView::Constructor(_) => {
                format!("<{}>", self.name(self.type_(known.owner()).name))
            }
        }
    }
}
