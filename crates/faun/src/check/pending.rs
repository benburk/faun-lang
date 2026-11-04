//! What inference holds until a type decides it: a method call until its
//! receiver is known, a word a declaration claims until its position's
//! type chooses the tag or the constructor, and a numeral until its type
//! is. Each is settled once unification has said what it can, at the end
//! of a binding, a clause, or a group of definitions inferred together.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::unify::{Scheme, Ty, free_variables, replaced, show, ty_embeds};
use super::{
    Bound, Checker, Finish, Marks, MethodImpl, PendingMethod, PendingNumeral, PendingTag, Reach,
    Reading, apply_signature, failure,
};
use crate::blessed::{self, NumeralType};
use crate::diagnostic::{Advised, Refusal, counted};
use crate::hir as h;
use crate::{ModuleId, Symbol};

/// How far a pass over pending methods goes with one whose receiver is
/// not yet known.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Pass {
    /// Partway through a definition: it waits, as what follows may say
    /// what the receiver is.
    Waiting,
    /// Before a numeral takes its default: it is the one type in scope
    /// whose method fits, unless the receiver is generic.
    Choosing,
    /// The last: what is left is chosen, a bound, or refused.
    Final,
}

impl Checker<'_> {
    /// A claimed word at a position whose type will decide its reading.
    pub(super) fn defer_tag(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        dual: &h::Dual,
        fields: Option<Vec<Ty>>,
        field_sites: Vec<(h::SiteId, crate::ast::Span)>,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_tags.push(PendingTag {
            module,
            span,
            dual: dual.clone(),
            fields,
            field_sites,
            result: result.clone(),
            resolved: false,
        });
        result
    }

    /// A pending word's field flowing into the type its reading gives it:
    /// widened where it is written in an expression and the reading's type
    /// is a row a caller may widen, unified otherwise.
    fn field_flows(
        &mut self,
        pending: &PendingTag,
        at: usize,
        field: &Ty,
        wanted: &Ty,
    ) -> Result<(), Refusal> {
        let Some(&(site, span)) = pending.field_sites.get(at) else {
            return self.unify_at(pending.module, pending.span, field, wanted);
        };
        let widened = self
            .infer
            .subsume(field, wanted)
            .map_err(|reason| self.mismatch(pending.module, span, field, wanted, &reason))?;
        if widened {
            self.widenings
                .push((pending.module, span, site, wanted.clone()));
        }
        Ok(())
    }

    /// A value of any row holding `label` with these fields: open, so it
    /// flows to whatever handles more.
    pub(super) fn tag(&mut self, label: Symbol, fields: Rc<[Ty]>) -> Ty {
        Ty::Variants(
            Rc::from([(label, fields)]),
            Some(Rc::new(self.infer.fresh())),
        )
    }

    pub(super) fn method(
        &mut self,
        module: ModuleId,
        (site, span): (h::SiteId, crate::ast::Span),
        receiver: &h::Expr,
        name: Symbol,
        arguments: &[h::Expr],
        locals: &mut Vec<Option<Scheme>>,
    ) -> Result<Ty, Refusal> {
        let receiver = self.expr(module, receiver, locals)?;
        let mut argument_types = Vec::with_capacity(arguments.len());
        for argument in arguments {
            argument_types.push(self.expr(module, argument, locals)?);
        }
        Ok(self.defer_method(module, (site, span), receiver, name, argument_types, false))
    }

    pub(super) fn defer_method(
        &mut self,
        module: ModuleId,
        (site, span): (h::SiteId, crate::ast::Span),
        receiver: Ty,
        name: Symbol,
        arguments: Vec<Ty>,
        member: bool,
    ) -> Ty {
        let result = self.infer.fresh();
        self.pending_methods.push(PendingMethod {
            site: Some(site),
            module,
            span,
            name,
            receiver,
            arguments,
            result: result.clone(),
            reach: if member { Reach::Bare } else { Reach::Called },
            resolved: false,
            owed: None,
            owing: None,
            numeral: false,
        });
        result
    }

    /// Owe, where `definition` is used, the bounds its scheme has, at the
    /// variables this use instantiated it with.
    pub(super) fn oblige(
        &mut self,
        module: ModuleId,
        span: crate::ast::Span,
        definition: Symbol,
        replacements: &HashMap<u32, Ty>,
    ) -> Result<(), Refusal> {
        let Some(bounds) = self.bounds.get(&definition).cloned() else {
            return Ok(());
        };
        for bound in bounds {
            let bound = bound.substituted(replacements);
            let Ty::Function(parameters, result) = bound.ty else {
                continue;
            };
            let skipped = usize::from(!bound.associated);
            let asked = self.infer.resolve(&Ty::Function(
                std::iter::once(bound.owner.clone())
                    .chain(parameters.iter().skip(skipped).cloned())
                    .collect(),
                result.clone(),
            ));
            if self.owed_again(bound.member, definition, &asked, (module, span))? {
                continue;
            }
            self.pending_methods.push(PendingMethod {
                site: None,
                module,
                span,
                name: bound.member,
                receiver: bound.owner,
                arguments: parameters.iter().skip(skipped).cloned().collect(),
                result: Rc::unwrap_or_clone(result),
                reach: if bound.associated {
                    Reach::Type
                } else if bound.bare {
                    Reach::Bare
                } else {
                    Reach::Called
                },
                resolved: false,
                owed: Some((definition, bound.through)),
                owing: self.obliging,
                numeral: bound.numeral,
            });
        }
        Ok(())
    }

    /// Whether `definition`'s bound asking `member` at `asked` is owed
    /// already, by the pending method whose implementation owes it or one
    /// owing that: then it is met where that one is, as a call of itself
    /// is. One asked again at a larger type would owe another larger still
    /// each time it is met, and is refused.
    fn owed_again(
        &self,
        member: Symbol,
        definition: Symbol,
        asked: &Ty,
        (module, span): (ModuleId, crate::ast::Span),
    ) -> Result<bool, Refusal> {
        let mut owing = self.obliging;
        while let Some(index) = owing {
            let pending = &self.pending_methods[index];
            if pending.name == member && pending.owed.is_some_and(|(owner, _)| owner == definition)
            {
                let earlier = self.infer.resolve(&Ty::Function(
                    std::iter::once(pending.receiver.clone())
                        .chain(pending.arguments.iter().cloned())
                        .collect(),
                    Rc::new(pending.result.clone()),
                ));
                if earlier == *asked {
                    return Ok(true);
                }
                if ty_embeds(&earlier, asked) {
                    let name = self.symbols.spelling(member);
                    return Err(failure(
                        module,
                        span,
                        format!("this asks for `{name}` through its bound again, at a larger type"),
                    )
                    .note("each time the bound is met it would owe another, without end")
                    .help("bound the method by types no larger than its own"));
                }
            }
            owing = pending.owing;
        }
        Ok(false)
    }

    pub(super) const fn marks(&self) -> Marks {
        Marks {
            methods: self.pending_methods.len(),
            numerals: self.pending_numerals.len(),
            tags: self.pending_tags.len(),
            closings: self.pending_closings.len(),
            handings: self.handings.len(),
        }
    }

    /// Settle what the stretch since `marks` left pending, as `finish`
    /// asks. A value it built that stores a function is refused first,
    /// whatever else settling found: a function stored and never called
    /// leaves its own types undecided, which is no fault of its own.
    pub(super) fn finish_pending(
        &mut self,
        marks: Marks,
        finish: Finish<'_>,
    ) -> Result<(), Refusal> {
        let finished = self.settle_pending(marks, finish);
        self.stored_function(marks.handings)?;
        finished
    }

    /// The first expression since `handings` handed a function that builds
    /// a value holding one: a record, tuple, list or tag written with it,
    /// or what a generic definition answers from it. A function answered
    /// is left to specialization, which also catches one whose type is
    /// known only there.
    fn stored_function(&self, handings: usize) -> Result<(), Refusal> {
        for handing in &self.handings[handings..] {
            let resolved = self.infer.resolve(&handing.ty);
            if matches!(resolved, Ty::Function(..)) || !holds_function(&resolved) {
                continue;
            }
            let handed_function = handing
                .handed
                .iter()
                .any(|ty| matches!(self.infer.resolve(ty), Ty::Function(..)));
            if !handed_function {
                continue;
            }
            let message = format!("`{}` holds a function", show(&resolved, self.symbols));
            return Err(Refusal::at(handing.module, handing.span, message)
                .note("data may not store functions; a function is passed into a call"));
        }
        Ok(())
    }

    /// [`Self::finish_pending`]'s settling, before what it built is looked at.
    fn settle_pending(&mut self, marks: Marks, finish: Finish<'_>) -> Result<(), Refusal> {
        let (method_start, numeral_start) = (marks.methods, marks.numerals);
        // Once its definition is done, a receiver nothing typed is the one
        // type in scope whose method fits, before anything takes a default,
        // so `'a'.is_digit()` reads its numeral as a `U8`; a generic one
        // stays open, and is a bound. A binding leaves it to its definition.
        let (pass, open) = match finish {
            Finish::Binding => (Pass::Waiting, HashSet::new()),
            Finish::Signed => (Pass::Choosing, HashSet::new()),
            Finish::Unsigned(types, names) => {
                (Pass::Choosing, self.generic_variables(types, names))
            }
        };
        self.settle_by(marks, pass, &open)?;
        // A word nothing decided takes its one declared reading, before a
        // numeral does its default: `W(3)` builds a `W`, whatever `3` is.
        // One at a time, since reading one may prove another's position a
        // tag row.
        while let Some(index) = (marks.tags..self.pending_tags.len()).find(|&index| {
            let pending = &self.pending_tags[index];
            !pending.resolved && pending.dual.candidates.len() == 1
        }) {
            let pending = self.pending_tags[index].clone();
            self.settle_nominal(&pending)?;
            self.pending_tags[index].resolved = true;
            self.settle_by(marks, pass, &open)?;
        }
        if let Some(pending) = self.pending_tags[marks.tags..]
            .iter()
            .find(|pending| !pending.resolved)
        {
            return Err(self.ambiguous(pending));
        }
        if matches!(finish, Finish::Binding) {
            return self.finish_binding(marks);
        }
        if self.settle_bare(true)? {
            self.settle_by(marks, pass, &open)?;
        }
        let generic = match finish {
            Finish::Unsigned(types, names) => {
                let generic = self.generic_variables(types, names);
                self.link_shapes(method_start, &generic);
                self.settle_by(marks, pass, &generic)?;
                generic
            }
            _ => HashSet::new(),
        };
        let is_generic = |checker: &Self, ty: &Ty| matches!(checker.infer.resolve(ty), Ty::Var(variable) if generic.contains(&variable));
        // A numeral nothing typed takes its default one at a time, a
        // negative one first since only `Int` holds it, and what that
        // settles may type the rest: in `-2 < 1` the `1` is compared with an
        // `Int`, so it is one. A numeral a definition used here carries in
        // is owed as its type's `of_nat`, `of_decimal` or `neg`, and takes
        // its default as a written one does: `t = 200` used where nothing
        // types it is a `Nat`.
        loop {
            let undecided = |negative: bool| {
                (numeral_start..self.pending_numerals.len()).find(|&index| {
                    let numeral = &self.pending_numerals[index];
                    !numeral.resolved
                        && numeral.negative == negative
                        && matches!(self.infer.resolve(&numeral.ty), Ty::Var(_))
                        && !is_generic(self, &numeral.ty)
                })
            };
            let owed = |negative: bool| {
                (method_start..self.pending_methods.len()).find(|&index| {
                    let pending = &self.pending_methods[index];
                    pending.numeral
                        && !pending.resolved
                        && (self.symbols.text(pending.name) == "neg") == negative
                        && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_))
                        && !is_generic(self, &pending.receiver)
                })
            };
            // Where it stands, its type, and whether it is a decimal.
            let next = |negative: bool| {
                let written = undecided(negative).map(|index| {
                    let numeral = &self.pending_numerals[index];
                    let decimal = numeral.scale.is_some();
                    (numeral.module, numeral.span, numeral.ty.clone(), decimal)
                });
                let carried = || {
                    let pending = &self.pending_methods[owed(negative)?];
                    let ty = pending.receiver.clone();
                    let decimal = self.owes_decimal(method_start, &ty);
                    Some((pending.module, pending.span, ty, decimal))
                };
                written.or_else(carried)
            };
            let negative = next(true);
            let negated = negative.is_some();
            let Some((module, span, ty, decimal)) = negative.or_else(|| next(false)) else {
                break;
            };
            let default = match (decimal, self.prelude.floats.first()) {
                (true, Some(float)) => Ty::Named(float.ty, Rc::default()),
                (true, None) => {
                    return Err(failure(
                        module,
                        span,
                        "a decimal numeral is a float, and no float is in the prelude",
                    ));
                }
                (false, _) if negated => Ty::Named(self.prelude.int, Rc::default()),
                (false, _) => Ty::Named(self.prelude.nat, Rc::default()),
            };
            self.unify_at(module, span, &ty, &default)?;
            self.settle_by(marks, pass, &generic)?;
        }
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if !numeral.resolved && is_generic(self, &numeral.ty) {
                self.defer_numeral(&numeral)?;
                self.pending_numerals[index].resolved = true;
            }
        }
        self.settle_methods(method_start, Pass::Final, &generic)?;
        for index in numeral_start..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved {
                continue;
            }
            self.elaborate(&numeral)?;
            self.pending_numerals[index].resolved = true;
        }
        let closings = self.pending_closings.split_off(marks.closings);
        for closing in closings {
            self.close_rows(&closing.ty, closing.rows)
                .map_err(|message| failure(closing.module, closing.span, message))?;
        }
        Ok(())
    }

    /// Whether a numeral a definition used here carries in at `receiver`
    /// is a decimal, owing its `of_decimal`: its default is a float.
    fn owes_decimal(&self, start: usize, receiver: &Ty) -> bool {
        let receiver = self.infer.resolve(receiver);
        self.pending_methods[start..].iter().any(|pending| {
            pending.numeral
                && self.symbols.text(pending.name) == "of_decimal"
                && self.infer.resolve(&pending.receiver) == receiver
        })
    }

    /// A numeral at the type its position gave it: a natural, or a call of
    /// the type's `of_nat`, or for a decimal its float's `of_decimal`.
    fn elaborate(&mut self, numeral: &PendingNumeral) -> Result<(), Refusal> {
        let ty = self.infer.resolve(&numeral.ty);
        let float = match &ty {
            Ty::Named(name, arguments) if arguments.is_empty() => {
                self.prelude.floats.iter().find(|float| float.ty == *name)
            }
            _ => None,
        };
        match (numeral.scale, float) {
            (Some(scale), Some(float)) => {
                if let Some(site) = numeral.site {
                    self.checked.literals.insert(
                        site,
                        blessed::decimal(numeral.magnitude.clone(), scale, numeral.negative, float),
                    );
                }
                return Ok(());
            }
            (Some(_), None) => {
                return Err(failure(
                    numeral.module,
                    numeral.span,
                    format!(
                        "a decimal numeral cannot be a `{}`: it is a float, an `F32` or an `F64`",
                        show(&ty, self.symbols)
                    ),
                ));
            }
            (None, Some(float)) => {
                return Err(failure(
                    numeral.module,
                    numeral.span,
                    format!(
                        "a numeral with no point is not a float: write the `{}` with one, as `3.0`",
                        float.name
                    ),
                ));
            }
            (None, None) => {}
        }
        let kind = match ty {
            Ty::Named(name, ref arguments) if name == self.prelude.nat && arguments.is_empty() => {
                NumeralType::Nat
            }
            Ty::Named(name, ref arguments) if name == self.prelude.int && arguments.is_empty() => {
                NumeralType::Int
            }
            Ty::Named(name, ref arguments)
                if arguments.is_empty()
                    && self.prelude.words.iter().any(|word| word.ty == name) =>
            {
                let word = self
                    .prelude
                    .words
                    .iter()
                    .find(|word| word.ty == name)
                    .expect("guarded");
                NumeralType::Word(word)
            }
            // Only the prelude's integers are numerals, and no conversion
            // is inserted to make one fit anything else.
            other => {
                let shown = show(&other, self.symbols);
                let message = format!("a numeral cannot be a `{shown}`");
                return Err(failure(numeral.module, numeral.span, message)
                    .label(format!("expected `{shown}`, found a numeral"))
                    .note("a numeral is a `Nat`, `Int`, `U8`, `U16`, `U32`, or `U64`")
                    .help("convert a value with `of_nat`"));
            }
        };
        let refuse = |error: blessed::LiteralElaborationError| {
            error.advise(failure(numeral.module, numeral.span, error.to_string()))
        };
        if numeral.character {
            blessed::character(&numeral.magnitude, kind, self.prelude).map_err(refuse)?;
        }
        let value = blessed::numeral(
            numeral.magnitude.clone(),
            numeral.negative,
            kind,
            self.prelude,
        )
        .map_err(refuse)?;
        if let Some(site) = numeral.site {
            self.checked.literals.insert(site, value);
        }
        Ok(())
    }

    /// A binding settles what it can and leaves the rest to its definition,
    /// which may yet decide a numeral's type or a method's receiver.
    fn finish_binding(&mut self, marks: Marks) -> Result<(), Refusal> {
        for index in marks.numerals..self.pending_numerals.len() {
            let numeral = self.pending_numerals[index].clone();
            if numeral.resolved || matches!(self.infer.resolve(&numeral.ty), Ty::Var(_)) {
                continue;
            }
            self.elaborate(&numeral)?;
            self.pending_numerals[index].resolved = true;
        }
        let closings = self.pending_closings.split_off(marks.closings);
        for closing in closings {
            self.close_rows(&closing.ty, closing.rows)
                .map_err(|message| failure(closing.module, closing.span, message))?;
        }
        Ok(())
    }

    /// The variables of a component's types that generalizing it will
    /// quantify: those nothing outside it holds.
    fn generic_variables(&self, types: &[Ty], names: &HashSet<Symbol>) -> HashSet<u32> {
        let mut generic: HashSet<u32> = types
            .iter()
            .flat_map(|ty| free_variables(&self.infer.resolve(ty)))
            .collect();
        let fixed = self.fixed(names);
        generic.retain(|variable| !fixed.contains(variable));
        generic
    }

    /// Where every method a generic receiver could have shares a shape --
    /// every `mul` is `T T -> T`, every `equals` answers a `Bool` -- that
    /// shape is context for the call before any default: in
    /// `double(x) -> x.mul(2)` the `2` is whatever `x` is.
    fn link_shapes(&mut self, start: usize, generic: &HashSet<u32>) {
        for index in start..self.pending_methods.len() {
            let pending = self.pending_methods[index].clone();
            if pending.resolved || pending.reach != Reach::Called {
                continue;
            }
            let Ty::Var(receiver) = self.infer.resolve(&pending.receiver) else {
                continue;
            };
            if !generic.contains(&receiver) {
                continue;
            }
            let Some(implementations) = self.methods.get(&pending.name) else {
                continue;
            };
            let visible = &self.visible_methods[&pending.module];
            let shapes: Vec<_> = implementations
                .iter()
                .filter(|implementation| visible.contains(&implementation.target))
                .filter_map(|implementation| {
                    self.infer
                        .probe(|trial| match trial.instantiate(&implementation.scheme) {
                            Ty::Function(parameters, result)
                                if parameters.len() == pending.arguments.len() + 1 =>
                            {
                                let receiver = trial.resolve(&parameters[0]);
                                let shape = |ty: &Ty| {
                                    let ty = trial.resolve(ty);
                                    if ty == receiver {
                                        Some(None)
                                    } else if free_variables(&ty).is_empty() {
                                        Some(Some(ty))
                                    } else {
                                        None
                                    }
                                };
                                Some((
                                    parameters[1..].iter().map(shape).collect::<Vec<_>>(),
                                    shape(&result),
                                ))
                            }
                            _ => None,
                        })
                })
                .collect();
            let Some((first_arguments, first_result)) = shapes.first().cloned() else {
                continue;
            };
            let shared = |position: &Option<Option<Ty>>, all: Vec<&Option<Option<Ty>>>| {
                position.is_some() && all.iter().all(|other| *other == position)
            };
            for (at, position) in first_arguments.iter().enumerate() {
                if shared(
                    position,
                    shapes.iter().map(|(arguments, _)| &arguments[at]).collect(),
                ) {
                    let linked = position.clone().flatten().unwrap_or(Ty::Var(receiver));
                    let _ = self.infer.unify(&pending.arguments[at], &linked);
                }
            }
            if shared(
                &first_result,
                shapes.iter().map(|(_, result)| result).collect(),
            ) {
                let linked = first_result.flatten().unwrap_or(Ty::Var(receiver));
                let _ = self.infer.unify(&pending.result, &linked);
            }
        }
    }

    /// A numeral of a generic type is built through that type's `of_nat`,
    /// and `neg` where it is negated, at each specialization: the component
    /// owes both as bounds, and the numeral waits for its type.
    fn defer_numeral(&mut self, numeral: &PendingNumeral) -> Result<(), Refusal> {
        let builder = if numeral.scale.is_some() {
            "of_decimal"
        } else {
            "of_nat"
        };
        let builder = self.method_symbol(numeral.module, numeral.span, builder)?;
        let nat = Ty::Named(self.prelude.nat, Rc::default());
        let arguments = if numeral.scale.is_some() {
            vec![nat.clone(), nat]
        } else {
            vec![nat]
        };
        self.pending_methods.push(PendingMethod {
            site: None,
            module: numeral.module,
            span: numeral.span,
            name: builder,
            receiver: numeral.ty.clone(),
            arguments,
            result: numeral.ty.clone(),
            reach: Reach::Type,
            resolved: false,
            owed: None,
            owing: None,
            numeral: true,
        });
        if numeral.negative {
            let neg = self.method_symbol(numeral.module, numeral.span, "neg")?;
            self.pending_methods.push(PendingMethod {
                site: None,
                module: numeral.module,
                span: numeral.span,
                name: neg,
                receiver: numeral.ty.clone(),
                arguments: Vec::new(),
                result: numeral.ty.clone(),
                reach: Reach::Called,
                resolved: false,
                owed: None,
                owing: None,
                numeral: true,
            });
        }
        if let Some(site) = numeral.site {
            self.checked.deferred_numerals.insert(
                site,
                crate::typed::Numeral {
                    magnitude: numeral.magnitude.clone(),
                    negative: numeral.negative,
                    scale: numeral.scale,
                    character: numeral.character,
                },
            );
        }
        Ok(())
    }

    /// What stays open on a component's generic variables after it is
    /// checked: each becomes a bound its definitions carry, and a call
    /// written through one is recorded as a call through a bound. The same
    /// member on the same variable twice is one bound, at one type.
    pub(super) fn inferred_bounds(&mut self, marks: Marks) -> Result<Vec<Bound>, Refusal> {
        let mut bounds: Vec<Bound> = Vec::new();
        for index in marks.methods..self.pending_methods.len() {
            let pending = self.pending_methods[index].clone();
            if pending.resolved {
                continue;
            }
            let owner = self.infer.resolve(&pending.receiver);
            let mut parameters = pending.arguments.clone();
            if pending.reach != Reach::Type {
                parameters.insert(0, owner.clone());
            }
            let ty = Ty::Function(parameters.into(), Rc::new(pending.result.clone()));
            match bounds.iter().position(|bound| {
                bound.member == pending.name
                    && bound.associated == (pending.reach == Reach::Type)
                    && bound.bare == (pending.reach == Reach::Bare)
                    && self.infer.resolve(&bound.owner) == owner
            }) {
                Some(at) => {
                    bounds[at].numeral |= pending.numeral;
                    let existing = bounds[at].ty.clone();
                    self.unify_at(pending.module, pending.span, &ty, &existing)?;
                }
                None => bounds.push(Bound {
                    owner: owner.clone(),
                    member: pending.name,
                    ty,
                    associated: pending.reach == Reach::Type,
                    bare: pending.reach == Reach::Bare,
                    through: None,
                    numeral: pending.numeral,
                }),
            }
            if let Some(site) = pending.site {
                self.bound_sites
                    .push((pending.module, pending.span, site, owner, pending.name));
            }
            self.pending_methods[index].resolved = true;
        }
        Ok(bounds)
    }

    /// Settle methods and claimed words together until neither moves: a
    /// method's answer can decide a word's position, and a word's reading
    /// a method's receiver.
    pub(super) fn settle(&mut self, marks: Marks) -> Result<(), Refusal> {
        self.settle_by(marks, Pass::Waiting, &HashSet::new())
    }

    /// The same, as far as `pass` goes with a receiver not yet known, the
    /// `generic` variables being those a bound may hold.
    fn settle_by(
        &mut self,
        marks: Marks,
        pass: Pass,
        generic: &HashSet<u32>,
    ) -> Result<(), Refusal> {
        loop {
            self.settle_methods(marks.methods, pass, generic)?;
            if !self.settle_tags(marks.tags)? {
                return Ok(());
            }
        }
    }

    /// Give every pending word whose position has a type its reading there:
    /// a tag row takes the tag, anything else a declared constructor.
    /// Answers whether any did.
    fn settle_tags(&mut self, start: usize) -> Result<bool, Refusal> {
        let mut progress = self.settle_bare(false)?;
        for index in start..self.pending_tags.len() {
            if self.pending_tags[index].resolved {
                continue;
            }
            let pending = self.pending_tags[index].clone();
            match self.infer.resolve(&pending.result) {
                Ty::Var(_) => continue,
                Ty::Variants(tags, _) => {
                    let fields = pending.fields.clone().unwrap_or_default();
                    // Where the row already holds the tag, each field flows
                    // into what the row says it holds.
                    let fields = match tags
                        .iter()
                        .find(|(label, _)| *label == pending.dual.spelling)
                    {
                        Some((_, wanted)) if wanted.len() == fields.len() => {
                            for (at, (field, wanted)) in
                                fields.iter().zip(wanted.iter()).enumerate()
                            {
                                self.field_flows(&pending, at, field, wanted)?;
                            }
                            wanted.clone()
                        }
                        _ => fields.into(),
                    };
                    let row = self.tag(pending.dual.spelling, fields);
                    self.unify_at(pending.module, pending.span, &row, &pending.result)?;
                    self.checked
                        .readings
                        .insert(pending.dual.site, Reading::Tag(pending.dual.spelling));
                }
                _ => self.settle_nominal(&pending)?,
            }
            self.pending_tags[index].resolved = true;
            progress = true;
        }
        Ok(progress)
    }

    /// Give each bare tag whose position has a type its reading there: a
    /// function's answer is the tag with the function's parameters as its
    /// fields, anything else the tag with none. Where nothing decided, and
    /// `default` says so, it is the tag with none.
    fn settle_bare(&mut self, default: bool) -> Result<bool, Refusal> {
        let mut progress = false;
        for index in 0..self.pending_bare.len() {
            let pending = self.pending_bare[index].clone();
            if pending.resolved {
                continue;
            }
            let wanted = match self.infer.resolve(&pending.ty) {
                Ty::Var(_) if !default => continue,
                Ty::Function(parameters, _) => {
                    let row = self.tag(pending.label, parameters.clone());
                    Ty::Function(parameters, Rc::new(row))
                }
                _ => self.tag(pending.label, Rc::default()),
            };
            // The position wants its type; the tag is what is there.
            self.unify_at(pending.module, pending.span, &wanted, &pending.ty)?;
            self.pending_bare[index].resolved = true;
            progress = true;
        }
        Ok(progress)
    }

    /// Read a pending word as the declared constructor its position
    /// demands: its only claimant, or the one whose type the position has.
    fn settle_nominal(&mut self, pending: &PendingTag) -> Result<(), Refusal> {
        let chosen = match pending.dual.candidates.as_slice() {
            [only] => *only,
            candidates => {
                let head = match self.infer.resolve(&pending.result) {
                    Ty::Named(head, _) => Some(head),
                    Ty::Function(_, result) => match *result {
                        Ty::Named(head, _) => Some(head),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(head) = head else {
                    return Err(self.ambiguous(pending));
                };
                *candidates
                    .iter()
                    .find(|candidate| self.constructor_owner(**candidate) == Some(head))
                    .ok_or_else(|| {
                        failure(
                            pending.module,
                            pending.span,
                            format!(
                                "type `{}` has no constructor `{}`",
                                self.symbols.spelling(head),
                                self.symbols.text(pending.dual.spelling)
                            ),
                        )
                    })?
            }
        };
        if let Some(home) = pending.dual.home
            && home != chosen
        {
            let owner = self
                .constructor_owner(home)
                .map_or("", |owner| self.symbols.spelling(owner));
            let other = self
                .constructor_owner(chosen)
                .map_or("", |owner| self.symbols.spelling(owner));
            let word = self.symbols.text(pending.dual.spelling);
            let message = format!("the bare `{word}` reads as `{owner}.{word}` here");
            return Err(failure(pending.module, pending.span, message)
                .note(format!(
                    "inside `{owner}`'s block, a bare constructor is `{owner}`'s own"
                ))
                .help(format!("write `{other}.{word}` for `{other}`'s")));
        }
        let scheme = self.constructors.get(&chosen).cloned().ok_or_else(|| {
            failure(
                pending.module,
                pending.span,
                "constructor has no declared type",
            )
        })?;
        let ty = self.infer.instantiate(&scheme);
        // Where the position already has a type, that the constructor
        // builds another is the whole of what is wrong.
        let builds = |checker: &mut Self, built: &Ty| {
            let wanted = checker.infer.resolve(&pending.result);
            checker.infer.unify(&pending.result, built).map_err(|_| {
                let built = show(&checker.infer.resolve(built), checker.symbols);
                let wanted = show(&wanted, checker.symbols);
                failure(pending.module, pending.span, "mismatched types")
                    .label(format!("expected `{wanted}`, found `{built}`"))
                    .note(format!(
                        "`{}` builds `{built}`",
                        checker.symbols.text(pending.dual.spelling)
                    ))
            })
        };
        match &pending.fields {
            None => builds(self, &ty)?,
            Some(fields) => {
                let (parameters, result) = match ty {
                    Ty::Function(parameters, result) => (parameters, Rc::unwrap_or_clone(result)),
                    result => (Rc::default(), result),
                };
                if parameters.len() != fields.len() {
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "constructor `{}` takes {}, but is given {}",
                            self.symbols.text(pending.dual.spelling),
                            counted(parameters.len(), "field"),
                            fields.len()
                        ),
                    ));
                }
                builds(self, &result)?;
                for (at, (field, parameter)) in fields.iter().zip(parameters.iter()).enumerate() {
                    self.field_flows(pending, at, field, parameter)?;
                }
            }
        }
        self.checked
            .readings
            .insert(pending.dual.site, Reading::Constructor(chosen));
        Ok(())
    }

    /// The type a declared constructor builds.
    fn constructor_owner(&self, constructor: Symbol) -> Option<Symbol> {
        let scheme = self.constructors.get(&constructor)?;
        let result = match &scheme.ty {
            Ty::Function(_, result) => result.as_ref(),
            result => result,
        };
        match result {
            Ty::Named(owner, _) => Some(*owner),
            _ => None,
        }
    }

    /// The one honest ambiguity: several types claim the word, and nothing
    /// says which type its position has.
    fn ambiguous(&self, pending: &PendingTag) -> Refusal {
        let word = self.symbols.text(pending.dual.spelling);
        let readings: Vec<_> = pending
            .dual
            .candidates
            .iter()
            .filter_map(|candidate| self.constructor_owner(*candidate))
            .map(|owner| format!("`{}.{word}`", self.symbols.spelling(owner)))
            .collect();
        let message = format!("constructor `{word}` is ambiguous here");
        failure(pending.module, pending.span, message)
            .note(format!(
                "nothing decides between {}",
                readings.join(" and ")
            ))
            .help("qualify it, or let a signature decide")
    }

    /// Resolve pending methods. On the final pass one still ambiguous is an
    /// error, except on a receiver in `generic`, which becomes a bound.
    fn settle_methods(
        &mut self,
        start: usize,
        pass: Pass,
        generic: &HashSet<u32>,
    ) -> Result<(), Refusal> {
        let final_pass = pass == Pass::Final;
        let mut generic = generic.clone();
        let mut unresolved: Vec<_> = (start..self.pending_methods.len())
            .filter(|index| !self.pending_methods[*index].resolved)
            .collect();
        loop {
            if pass != Pass::Waiting && self.may_spread(&unresolved, &generic) {
                self.spread_generic(start, &mut generic);
            }
            let mut progress = false;
            let mut next = Vec::new();
            let pushed = self.pending_methods.len();
            for index in unresolved {
                let pending = self.pending_methods[index].clone();
                let fields = self.field_candidates(&pending);
                if let [field] = fields.as_slice() {
                    self.apply_field(&pending, field)?;
                    self.pending_methods[index].resolved = true;
                    progress = true;
                    continue;
                }
                if fields.len() > 1 {
                    next.push(index);
                    continue;
                }
                match self.structural(&pending, final_pass)? {
                    Some(true) => {
                        self.pending_methods[index].resolved = true;
                        progress = true;
                        continue;
                    }
                    None => {
                        next.push(index);
                        continue;
                    }
                    Some(false) => {}
                }
                let owned = self.owned_methods(&pending);
                // A bare word with nothing handed it, on a receiver nothing
                // has said anything of yet, is a field of whatever it turns
                // out to be, as Ori reads `.name` without parentheses: it
                // waits for the receiver, and is no guess at a method.
                let may_be_field = pending.reach == Reach::Bare
                    && pending.arguments.is_empty()
                    && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_));
                // A receiver not yet known is taken for a type in scope
                // whose method fits only once its definition is done, as
                // what follows may make it a type not in scope with such a
                // method of its own, as `host.stdout` is; and a generic one
                // never is, owing the method as a bound.
                let unknown = matches!(self.infer.resolve(&pending.receiver), Ty::Var(_));
                let generic_receiver = matches!(
                    self.infer.resolve(&pending.receiver),
                    Ty::Var(variable) if generic.contains(&variable)
                );
                let waits = unknown && (pass == Pass::Waiting || generic_receiver);
                // The one method the receiver has is applied whether or not
                // it fits, which says why where it does not; on a receiver
                // not yet known, only once nothing else will say it, as the
                // call that answers it may have no such method itself.
                let candidates: Vec<_> = if may_be_field || waits {
                    Vec::new()
                } else if let [only] = owned.as_slice()
                    && (final_pass || !unknown)
                {
                    vec![only.clone()]
                } else {
                    owned
                        .iter()
                        .filter(|implementation| self.fits(&pending, implementation))
                        .cloned()
                        .collect()
                };
                match candidates.as_slice() {
                    // A field of a receiver nothing else says anything of is
                    // a field of whatever record it turns out to be, unless
                    // the receiver is generic: then it is a bound, met by
                    // any record or declared type having the field.
                    [] if pending.reach == Reach::Bare
                        && pending.arguments.is_empty()
                        && matches!(self.infer.resolve(&pending.receiver), Ty::Var(_)) =>
                    {
                        if final_pass && !generic_receiver {
                            let projection = Self::projection(pending.name);
                            self.apply_field(&pending, &projection)?;
                            self.pending_methods[index].resolved = true;
                            progress = true;
                        } else {
                            next.push(index);
                        }
                    }
                    // A receiver not yet known may be one that has it, or a
                    // generic one owing it as a bound.
                    [] if match self.infer.resolve(&pending.receiver) {
                        Ty::Var(variable) => !final_pass || generic.contains(&variable),
                        _ => false,
                    } =>
                    {
                        next.push(index);
                    }
                    // Said on the final pass, when what the call answers is
                    // known too, so the bound the refusal suggests is whole.
                    [] if !final_pass => next.push(index),
                    // A declared type's field that does not fit is still
                    // the field read, so what it answers is told against
                    // what is wanted rather than the field said missing.
                    [] if let Some(field) = self.declared_field(&pending) => {
                        self.apply_field(&pending, &field)?;
                        self.pending_methods[index].resolved = true;
                        progress = true;
                    }
                    [] => {
                        let name = self.symbols.text(pending.name);
                        let refused = match self.infer.resolve(&pending.receiver) {
                            Ty::Var(_) => {
                                let message = format!("no field or method `{name}` is in scope");
                                failure(pending.module, pending.span, message)
                            }
                            // A signature's variable has only what its bounds give.
                            Ty::Rigid(_) => self.unbounded(&pending),
                            receiver => {
                                let message = format!(
                                    "`{}` has no field or method `{name}`",
                                    show(&receiver, self.symbols)
                                );
                                let refused = failure(pending.module, pending.span, message);
                                match pending.site.and_then(|site| self.prefix_helps.get(&site)) {
                                    Some(help) => refused.help(*help),
                                    None => refused,
                                }
                            }
                        };
                        return Err(refused);
                    }
                    [candidate] => {
                        self.obliging = Some(index);
                        let applied = self.apply_method(&pending, candidate);
                        self.obliging = None;
                        applied?;
                        self.pending_methods[index].resolved = true;
                        progress = true;
                    }
                    _ => next.push(index),
                }
            }
            // What resolving these owes, and the calls a structural member
            // makes of its components, are asked in the next round.
            next.extend(pushed..self.pending_methods.len());
            if next.is_empty() {
                return Ok(());
            }
            if !progress {
                let waiting = next.iter().find(|index| {
                    !matches!(self.infer.resolve(&self.pending_methods[**index].receiver),
                        Ty::Var(variable) if generic.contains(&variable))
                });
                if final_pass && let Some(&index) = waiting {
                    let pending = &self.pending_methods[index];
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "method `{}` is ambiguous for the inferred receiver type",
                            self.symbols.text(pending.name)
                        ),
                    ));
                }
                return Ok(());
            }
            unresolved = next;
        }
    }

    /// Why a signed body's own variable has no `pending`: its signature
    /// gives it none. Where a definition used here asks it, that says so,
    /// and the alias it asks through is what to write.
    fn unbounded(&self, pending: &PendingMethod) -> Refusal {
        let member = self.symbols.text(pending.name);
        let receiver = self.infer.resolve(&pending.receiver);
        let variable = self
            .current_names
            .iter()
            .find(|(_, ty)| self.infer.resolve(ty) == receiver)
            .map(|(name, _)| self.symbols.text(*name));
        let message = variable.map_or_else(
            || format!("a type variable has no field or method `{member}`"),
            |variable| format!("the type variable `{variable}` has no field or method `{member}`"),
        );
        let refused = failure(pending.module, pending.span, message);
        let written = variable.and_then(|variable| self.written_bound(pending, variable));
        let help = written.map_or_else(
            || format!("give it `{member}` with a `where` bound in the signature"),
            |bound| format!("write `{bound}` in the signature's `where`"),
        );
        let Some((definition, through)) = pending.owed else {
            return refused.help(help);
        };
        let definition = self.symbols.spelling(definition);
        let refused = refused.note(format!("`{definition}`, used here, asks for `{member}`"));
        match (through, variable) {
            (Some(alias), Some(variable)) => refused.help(format!(
                "write `{}({variable})` in the signature's `where`, as `{definition}` does",
                self.symbols.spelling(alias)
            )),
            _ => refused.help(help),
        }
    }

    /// The bound that would give `variable` what `pending` calls on it, as
    /// a signature writes it, where every type in it is known.
    fn written_bound(&self, pending: &PendingMethod, variable: &str) -> Option<String> {
        if pending.reach != Reach::Called {
            return None;
        }
        let names: HashMap<u32, Symbol> = self
            .current_names
            .iter()
            .filter_map(|(name, ty)| match self.infer.resolve(ty) {
                Ty::Rigid(variable) => Some((variable, *name)),
                _ => None,
            })
            .collect();
        let parameters: Rc<[Ty]> = std::iter::once(&pending.receiver)
            .chain(&pending.arguments)
            .map(|ty| self.infer.resolve(ty))
            .collect();
        let ty = Ty::Function(parameters, Rc::new(self.infer.resolve(&pending.result)));
        let known = replaced(&ty, &|leaf| match leaf {
            Ty::Rigid(variable) => names
                .get(variable)
                .map(|name| Ty::Named(*name, Rc::default())),
            _ => None,
        });
        let shown = show(&known, self.symbols);
        let member = self.symbols.text(pending.name);
        (!shown.contains(['_', '\''])).then(|| format!("{variable}.{member} : {shown}"))
    }

    fn field_candidates(&mut self, pending: &PendingMethod) -> Vec<Scheme> {
        if pending.reach != Reach::Bare || !pending.arguments.is_empty() {
            return Vec::new();
        }
        let receiver = self.infer.resolve(&pending.receiver);
        // A closed record without the field has none, and is refused as
        // having no such member.
        if let Ty::Record(fields, tail) = &receiver {
            let has = tail.is_some() || fields.iter().any(|(name, _)| *name == pending.name);
            return if has {
                vec![Self::projection(pending.name)]
            } else {
                Vec::new()
            };
        }
        let Some(fields) = self.fields.get(&pending.name) else {
            return Vec::new();
        };
        // A receiver not yet known waits to be known, and is at the last
        // a record having the field: which declared types have a field of
        // that name says nothing of it, and one declared anywhere would
        // otherwise change what an unrelated projection means.
        let Ty::Named(owner, _) = receiver else {
            return Vec::new();
        };
        fields
            .iter()
            .filter(|field| field.owner == owner)
            .filter(|field| {
                self.infer.probe(|trial| {
                    apply_signature(trial, pending, &field.scheme, self.symbols).is_ok()
                })
            })
            .map(|field| field.scheme.clone())
            .collect()
    }

    /// The field `pending` reads off a declared type having one of that
    /// name, whether or not it fits.
    fn declared_field(&self, pending: &PendingMethod) -> Option<Scheme> {
        if pending.reach != Reach::Bare || !pending.arguments.is_empty() {
            return None;
        }
        let Ty::Named(owner, _) = self.infer.resolve(&pending.receiver) else {
            return None;
        };
        let fields = self.fields.get(&pending.name)?;
        let field = fields.iter().find(|field| field.owner == owner)?;
        Some(field.scheme.clone())
    }

    /// Whether spreading `generic` could say anything of these: only a
    /// receiver not yet known, and not yet held generic, asks it. Each
    /// spread walks every pending method, and a pass may go round once
    /// for each it resolves.
    fn may_spread(&self, unresolved: &[usize], generic: &HashSet<u32>) -> bool {
        !generic.is_empty()
            && unresolved.iter().any(|&index| {
                matches!(
                    self.infer.resolve(&self.pending_methods[index].receiver),
                    Ty::Var(variable) if !generic.contains(&variable)
                )
            })
    }

    /// Add to `generic` what a member of a receiver holding a generic
    /// variable reads and answers: a field read off a generic record, or
    /// what a generic value's member takes and answers, is as generic as
    /// the value, and a bound on it will say so. Until nothing more joins.
    fn spread_generic(&self, start: usize, generic: &mut HashSet<u32>) {
        loop {
            let before = generic.len();
            // A generic variable since bound to a record holds what the
            // record does.
            let bound: Vec<u32> = generic
                .iter()
                .flat_map(|&variable| free_variables(&self.infer.resolve(&Ty::Var(variable))))
                .collect();
            generic.extend(bound);
            for pending in &self.pending_methods[start..] {
                let receiver = free_variables(&self.infer.resolve(&pending.receiver));
                if receiver.iter().any(|variable| generic.contains(variable)) {
                    generic.extend(receiver);
                    for ty in pending.arguments.iter().chain([&pending.result]) {
                        generic.extend(free_variables(&self.infer.resolve(ty)));
                    }
                }
            }
            if generic.len() == before {
                return;
            }
        }
    }

    /// Reading field `name` of a record: `{name: t, *} -> t`, which reads it
    /// from a record that has it and asks it of one that is open. Its two
    /// variables are the scheme's own, never linked, since a scheme is
    /// instantiated before it is used.
    fn projection(name: Symbol) -> Scheme {
        let (field, rest) = (u32::MAX, u32::MAX - 1);
        Scheme {
            variables: vec![field, rest],
            ty: Ty::Function(
                Rc::from([Ty::Record(
                    Rc::from([(name, Ty::Var(field))]),
                    Some(Rc::new(Ty::Var(rest))),
                )]),
                Rc::new(Ty::Var(field)),
            ),
        }
    }

    /// `equals` and `to_str` on a closed record, a tuple or a tag row, `cmp`
    /// on a tuple, and `hash_into` on a record or a tuple, which such values have with no
    /// declaration: each asks the same of every component, position by
    /// position for a tuple and field by field of each tag for a row. A
    /// record and a row have no `cmp`, having no order of their fields or
    /// tags, and an open record has neither, its other fields being a
    /// caller's, as a row a caller may add tags to has neither `equals` nor
    /// `to_str`. Answers whether `pending` was one, or nothing while a record
    /// or row may yet be closed.
    fn structural(
        &mut self,
        pending: &PendingMethod,
        final_pass: bool,
    ) -> Result<Option<bool>, Refusal> {
        let receiver = self.infer.resolve(&pending.receiver);
        let components = match &receiver {
            Ty::Tuple(members) => members.clone(),
            Ty::Record(fields, _) => fields.iter().map(|(_, ty)| ty.clone()).collect(),
            Ty::Variants(tags, _) => tags
                .iter()
                .flat_map(|(_, fields)| fields.iter().cloned())
                .collect(),
            _ => return Ok(Some(false)),
        };
        let spelled = self.symbols.text(pending.name);
        // `hash_into` feeds each component to a hasher and answers it fed:
        // what it answers is whatever hasher it was handed.
        let hashing = spelled == "hash_into"
            && matches!(receiver, Ty::Tuple(_) | Ty::Record(..))
            && pending.arguments.len() == 1;
        let answer = match (spelled, &receiver) {
            ("equals", _) => Ty::Named(self.prelude.bool_, Rc::default()),
            ("cmp", Ty::Tuple(_)) => Ty::Named(self.prelude.order, Rc::default()),
            ("to_str", _) => Ty::Named(self.prelude.str_, Rc::default()),
            _ if hashing => pending.arguments[0].clone(),
            _ => return Ok(Some(false)),
        };
        if let Ty::Record(_, Some(tail)) = &receiver {
            if !final_pass && matches!(**tail, Ty::Var(_)) {
                return Ok(None);
            }
            return Err(failure(
                pending.module,
                pending.span,
                format!("a record with `*` has no `{spelled}`: its other fields are a caller's"),
            ));
        }
        // A row's rest nothing else fills closes to nothing, but may be
        // filled yet until checking is done.
        if let Ty::Variants(_, Some(tail)) = &receiver {
            match &**tail {
                Ty::Var(_) if !final_pass => return Ok(None),
                Ty::Var(_) => {}
                _ => {
                    return Err(failure(
                        pending.module,
                        pending.span,
                        format!(
                            "`{}` may hold tags a caller adds, which it cannot say `{spelled}` of",
                            show(&receiver, self.symbols)
                        ),
                    ));
                }
            }
        }
        // `to_str` takes the value alone, `hash_into` a hasher, and the
        // others a second like it.
        let unary = spelled == "to_str";
        match pending.arguments.as_slice() {
            [] if unary => {}
            [_] if hashing => {}
            [other] if !unary => self.unify_at(pending.module, pending.span, other, &receiver)?,
            _ => return Ok(Some(false)),
        }
        self.unify_at(pending.module, pending.span, &answer, &pending.result)?;
        for component in components.iter() {
            let arguments = if unary {
                Vec::new()
            } else if hashing {
                vec![answer.clone()]
            } else {
                vec![component.clone()]
            };
            self.pending_methods.push(PendingMethod {
                site: None,
                module: pending.module,
                span: pending.span,
                name: pending.name,
                receiver: component.clone(),
                arguments,
                result: answer.clone(),
                reach: Reach::Called,
                resolved: false,
                owed: None,
                owing: None,
                numeral: false,
            });
        }
        if let Some(site) = pending.site {
            self.checked.methods.insert(site, pending.name);
        }
        Ok(Some(true))
    }

    /// The visible methods named at `pending` that its receiver could have.
    fn owned_methods(&self, pending: &PendingMethod) -> Vec<MethodImpl> {
        let implementations = self
            .methods
            .get(&pending.name)
            .map_or(&[][..], Vec::as_slice);
        let receiver = self.infer.resolve(&pending.receiver);
        // A rigid receiver is a signed body's own variable: what it has is
        // what its bounds say. One not yet known may be such a variable too,
        // so a bound is as much a candidate for it as a declared method.
        let bounded = self
            .current
            .iter()
            .filter(|bound| {
                bound.member == pending.name
                    && bound.associated == (pending.reach == Reach::Type)
                    && match &receiver {
                        Ty::Rigid(_) => self.infer.resolve(&bound.owner) == receiver,
                        Ty::Var(_) => true,
                        _ => false,
                    }
            })
            .map(|bound| MethodImpl {
                owner: pending.name,
                target: pending.name,
                scheme: Scheme {
                    variables: Vec::new(),
                    ty: bound.ty.clone(),
                },
                bound: true,
            });
        if let Ty::Rigid(_) = receiver {
            return bounded.collect();
        }
        // A value's own type's methods are its, wherever the value went and
        // whether or not its type was imported; one not yet known may have
        // only those in scope, which are what inference chooses among.
        let visible = &self.visible_methods[&pending.module];
        implementations
            .iter()
            .filter(|implementation| match &receiver {
                Ty::Named(owner, _) => implementation.owner == *owner,
                Ty::Var(_) => visible.contains(&implementation.target),
                _ => false,
            })
            .cloned()
            .chain(bounded)
            .collect()
    }

    /// Whether `implementation` takes the arguments given at `pending`.
    fn fits(&mut self, pending: &PendingMethod, implementation: &MethodImpl) -> bool {
        let symbols = self.symbols;
        self.infer
            .probe(|trial| apply_signature(trial, pending, &implementation.scheme, symbols).is_ok())
    }

    fn apply_field(&mut self, pending: &PendingMethod, scheme: &Scheme) -> Result<(), Refusal> {
        apply_signature(&mut self.infer, pending, scheme, self.symbols)
            .map_err(|message| failure(pending.module, pending.span, message))?;
        // A bound a use owes, met by a field, names nothing where it stands.
        if let Some(site) = pending.site {
            self.checked.projections.insert(site, pending.name);
        }
        Ok(())
    }

    fn apply_method(
        &mut self,
        pending: &PendingMethod,
        implementation: &MethodImpl,
    ) -> Result<(), Refusal> {
        let replacements = apply_signature(
            &mut self.infer,
            pending,
            &implementation.scheme,
            self.symbols,
        )
        .map_err(|message| failure(pending.module, pending.span, message))?;
        // An obligation names nothing where it stands; a call through a
        // bound names its implementation only once it is specialized; a call
        // of an implementation owes that implementation's own bounds.
        if implementation.bound {
            if let Some(site) = pending.site {
                self.bound_sites.push((
                    pending.module,
                    pending.span,
                    site,
                    pending.receiver.clone(),
                    pending.name,
                ));
            }
        } else {
            if let Some(site) = pending.site {
                self.checked.methods.insert(site, implementation.target);
            }
            self.oblige(
                pending.module,
                pending.span,
                implementation.target,
                &replacements,
            )?;
        }
        Ok(())
    }
}

/// Whether an inferred type holds a function anywhere, itself included.
fn holds_function(ty: &Ty) -> bool {
    match ty {
        Ty::Function(..) => true,
        Ty::Var(_) | Ty::Rigid(_) => false,
        Ty::Named(_, parts) | Ty::Tuple(parts) => parts.iter().any(holds_function),
        Ty::Variants(tags, tail) => tags
            .iter()
            .flat_map(|(_, fields)| fields.iter())
            .chain(tail.as_deref())
            .any(holds_function),
        Ty::Record(fields, tail) => fields
            .iter()
            .map(|(_, field)| field)
            .chain(tail.as_deref())
            .any(holds_function),
    }
}
