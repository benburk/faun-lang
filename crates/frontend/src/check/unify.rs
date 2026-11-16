//! Types as inference holds them, and the unifier that binds their
//! variables.
//!
//! A [`Ty`] shares its parts, so cloning one is a count. [`Infer`] holds
//! what each variable is bound to; unification binds them, and subsumption
//! lets a closed tag row stand where a wider one is wanted. Rows unify as
//! Rémy's: shared entries unify, and an open side's tail takes what only
//! the other holds.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::{InferredType, TypeVariable};
use crate::{Symbol, Symbols};

/// A type as inference holds it. Its parts are shared, not owned: cloning
/// one is a count, not a copy, and resolving one rebuilds only the parts a
/// binding changed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Ty {
    Var(u32),
    Rigid(u32),
    Named(Symbol, Rc<[Self]>),
    Function(Rc<[Self]>, Rc<Self>),
    /// A tag row: the tags it holds, and where it is open, a tail standing
    /// for the rest. A tail is a variable, which unification may widen, or
    /// rigid: a signed definition's own result row, which its body may not
    /// widen and each caller may.
    Variants(Rc<[(Symbol, Rc<[Self]>)]>, Option<Rc<Self>>),
    /// A record's fields, in one order, and where it is open, a tail
    /// standing for the fields a caller's record has besides.
    Record(Rc<[(Symbol, Self)]>, Option<Rc<Self>>),
    /// A positional product of two or more, which never unifies with a
    /// record.
    Tuple(Rc<[Self]>),
}

/// Something a type holds a list of: a type, or a named field or tag.
pub(super) trait Entry {
    type Part;
    fn part(&self) -> &Self::Part;
    #[must_use]
    fn with(&self, part: Self::Part) -> Self;
}

impl Entry for Ty {
    type Part = Self;
    fn part(&self) -> &Self {
        self
    }
    fn with(&self, part: Self) -> Self {
        part
    }
}

impl<P> Entry for (Symbol, P) {
    type Part = P;
    fn part(&self) -> &P {
        &self.1
    }
    fn with(&self, part: P) -> Self {
        (self.0, part)
    }
}

/// Each entry of `entries` with what `part` resolves it to, or nothing
/// where it resolves none: the ones before the first it does are
/// cloned only once one does.
pub(super) fn resolved_entries<T: Clone + Entry>(
    entries: &[T],
    part: impl Fn(&T::Part) -> Option<T::Part>,
) -> Option<Vec<T>> {
    let mut resolved: Option<Vec<T>> = None;
    for (at, entry) in entries.iter().enumerate() {
        match part(entry.part()) {
            Some(new) => resolved
                .get_or_insert_with(|| entries[..at].to_vec())
                .push(entry.with(new)),
            None => {
                if let Some(resolved) = &mut resolved {
                    resolved.push(entry.clone());
                }
            }
        }
    }
    resolved
}

/// A row's own tail, where it has one.
pub(super) fn ty_tail(ty: &Ty) -> Option<Rc<Ty>> {
    match ty {
        Ty::Variants(_, tail) | Ty::Record(_, tail) => tail.clone(),
        _ => None,
    }
}

/// A tag of a row, with its fields; or a record's field, as a one-type
/// tag, where a row unification treats both alike.
pub(super) type Tag = (Symbol, Rc<[Ty]>);

/// The tags of a row, each with its fields.
pub(super) type Tags = Vec<Tag>;

/// Which kind of row a row unification builds: a tag row, whose entries
/// are tags and their fields, or a record, whose entries are fields each
/// held as a one-type entry.
#[derive(Clone, Copy, Debug)]
pub(super) enum Former {
    Tags,
    Fields,
}

impl Former {
    pub(super) fn build(self, entries: Tags, tail: Option<Rc<Ty>>) -> Ty {
        match self {
            Self::Tags => Ty::Variants(entries.into(), tail),
            Self::Fields => Ty::Record(
                entries
                    .into_iter()
                    .map(|(name, held)| (name, held[0].clone()))
                    .collect(),
                tail,
            ),
        }
    }
}

/// A record's fields as row entries.
pub(super) fn entries(fields: &[(Symbol, Ty)]) -> Tags {
    fields
        .iter()
        .map(|(name, ty)| (*name, Rc::from([ty.clone()])))
        .collect()
}

/// Why two types do not unify.
#[derive(Clone, Debug)]
pub(super) enum Mismatch {
    Reason(&'static str),
    /// One tag written with two numbers of fields.
    Fields(usize, usize),
    /// Tags a row holds that `row` -- closed, or a caller's to widen --
    /// cannot take.
    NotAmong {
        tags: Vec<Symbol>,
        row: Ty,
    },
}

impl Mismatch {
    pub(super) fn describe(&self, symbols: &Symbols) -> String {
        match self {
            Self::Reason(reason) => (*reason).to_owned(),
            Self::Fields(one, other) => {
                format!("one tag is written with {one} and with {other} fields")
            }
            Self::NotAmong {
                tags: fields,
                row: row @ Ty::Record(..),
            } => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|field| format!("`{}`", symbols.text(*field)))
                    .collect();
                format!(
                    "the record `{}` has no field {}",
                    show(row, symbols),
                    fields.join(" or ")
                )
            }
            Self::NotAmong { tags, row } => {
                let tags: Vec<_> = tags
                    .iter()
                    .map(|tag| format!("`{}`", symbols.spelling(*tag)))
                    .collect();
                let (subject, verb) = if tags.len() == 1 {
                    (tags[0].clone(), "is")
                } else {
                    (tags.join(" and "), "are")
                };
                format!(
                    "{subject} {verb} not among the tags of `{}`, which admits no others",
                    show(row, symbols)
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Scheme {
    pub(super) variables: Vec<u32>,
    pub(super) ty: Ty,
}

#[derive(Debug, Default)]
pub(super) struct Infer {
    /// What each variable is bound to. Resolving one stores back what it
    /// resolved to, so a chain of variables is walked once: interior, as
    /// resolving only reads what inference holds.
    links: RefCell<Vec<Option<Ty>>>,
    next_rigid: u32,
    /// The variables bound since the outermost open probe began, which it
    /// unbinds when it ends.
    trail: Vec<u32>,
    probing: bool,
}

impl Infer {
    /// What `trial` answers, with every variable it made or bound undone:
    /// a probe costs what it does, not what inference holds.
    pub(super) fn probe<T>(&mut self, trial: impl FnOnce(&mut Self) -> T) -> T {
        let variables = self.links.get_mut().len();
        let (bound, outer) = (self.trail.len(), self.probing);
        self.probing = true;
        let answer = trial(self);
        for id in self.trail.drain(bound..) {
            self.links.get_mut()[usize::try_from(id).expect("u32 fits usize")] = None;
        }
        self.links.get_mut().truncate(variables);
        self.probing = outer;
        answer
    }

    fn bind(&mut self, id: u32, ty: Ty) {
        if self.probing {
            self.trail.push(id);
        }
        self.links.get_mut()[usize::try_from(id).expect("u32 fits usize")] = Some(ty);
    }

    pub(super) fn fresh(&mut self) -> Ty {
        let links = self.links.get_mut();
        let id = u32::try_from(links.len()).expect("fewer than 2^32 inference variables");
        links.push(None);
        Ty::Var(id)
    }

    /// `ty` with every bound variable in it replaced by what it is bound
    /// to, rows flattened and records' fields in order. The parts no
    /// binding reaches are `ty`'s own, shared rather than rebuilt.
    pub(super) fn resolve(&self, ty: &Ty) -> Ty {
        self.resolved(ty).unwrap_or_else(|| ty.clone())
    }

    /// `ty` resolved, or nothing where it already is.
    fn resolved(&self, ty: &Ty) -> Option<Ty> {
        match ty {
            Ty::Var(id) => {
                let at = usize::try_from(*id).expect("u32 fits usize");
                let link = self.links.borrow()[at].clone()?;
                let resolved = self.resolve(&link);
                // A probe's bindings are undone, so what it resolves is
                // not kept.
                if !self.probing {
                    self.links.borrow_mut()[at] = Some(resolved.clone());
                }
                Some(resolved)
            }
            Ty::Rigid(_) => None,
            Ty::Named(name, arguments) => {
                let arguments = self.resolved_all(arguments)?;
                Some(Ty::Named(*name, arguments))
            }
            Ty::Function(parameters, result) => {
                let resolved_parameters = self.resolved_all(parameters);
                let resolved_result = self.resolved(result);
                if resolved_parameters.is_none() && resolved_result.is_none() {
                    return None;
                }
                let parameters = resolved_parameters.unwrap_or_else(|| parameters.clone());
                let result = resolved_result.map_or_else(|| result.clone(), Rc::new);
                Some(Ty::Function(parameters, result))
            }
            // A row is resolved flat: a tail bound to a row gives up its
            // tags, so what comes back ends in an unbound tail or none.
            Ty::Variants(tags, tail) => {
                let fields = resolved_entries(tags, |fields| self.resolved_all(fields));
                let tail = tail.as_deref().and_then(|tail| self.resolved(tail));
                if fields.is_none() && tail.is_none() {
                    return None;
                }
                let mut tags = fields.unwrap_or_else(|| tags.to_vec());
                let tail = match tail {
                    Some(Ty::Variants(more, rest)) => {
                        tags.extend(more.iter().cloned());
                        rest
                    }
                    Some(other) => Some(Rc::new(other)),
                    None => ty_tail(ty),
                };
                Some(Ty::Variants(tags.into(), tail))
            }
            Ty::Record(fields, tail) => {
                let resolved = resolved_entries(fields, |field| self.resolved(field));
                let tail = tail.as_deref().and_then(|tail| self.resolved(tail));
                let sorted = fields.is_sorted_by_key(|(name, _)| *name);
                if resolved.is_none() && tail.is_none() && sorted {
                    return None;
                }
                let mut fields = resolved.unwrap_or_else(|| fields.to_vec());
                let tail = match tail {
                    Some(Ty::Record(more, rest)) => {
                        fields.extend(more.iter().cloned());
                        rest
                    }
                    Some(other) => Some(Rc::new(other)),
                    None => ty_tail(ty),
                };
                fields.sort_by_key(|(name, _)| *name);
                Some(Ty::Record(fields.into(), tail))
            }
            Ty::Tuple(members) => Some(Ty::Tuple(self.resolved_all(members)?)),
        }
    }

    /// `types` resolved, or nothing where each already is.
    fn resolved_all(&self, types: &Rc<[Ty]>) -> Option<Rc<[Ty]>> {
        resolved_entries(types, |ty| self.resolved(ty)).map(Rc::from)
    }

    pub(super) fn unify(&mut self, left: &Ty, right: &Ty) -> Result<(), Mismatch> {
        let left = self.resolve(left);
        let right = self.resolve(right);
        match (&left, &right) {
            (Ty::Var(a), Ty::Var(b)) if a == b => Ok(()),
            (Ty::Rigid(a), Ty::Rigid(b)) if a == b => Ok(()),
            (Ty::Var(id), other) | (other, Ty::Var(id)) => {
                if contains(other, *id) {
                    Err(Mismatch::Reason("a type would contain itself"))
                } else {
                    self.bind(*id, other.clone());
                    Ok(())
                }
            }
            (Ty::Named(a, aa), Ty::Named(b, ba)) if a == b && aa.len() == ba.len() => {
                for (a, b) in aa.iter().zip(ba.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (Ty::Function(ap, ar), Ty::Function(bp, br)) if ap.len() == bp.len() => {
                for (a, b) in ap.iter().zip(bp.iter()) {
                    self.unify(a, b)?;
                }
                self.unify(ar, br)
            }
            (Ty::Variants(a, at), Ty::Variants(b, bt)) => {
                self.unify_rows(Former::Tags, (a, at.as_deref()), (b, bt.as_deref()))
            }
            (Ty::Record(a, at), Ty::Record(b, bt)) => self.unify_rows(
                Former::Fields,
                (&entries(a), at.as_deref()),
                (&entries(b), bt.as_deref()),
            ),
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            _ => Err(Mismatch::Reason("incompatible types")),
        }
    }

    /// Unify what a body answers with what its signature says it answers,
    /// except that a closed tag row may stand where the signature's row is
    /// one a caller may widen, if it holds none of the caller's tags. That
    /// takes a widening where the value is answered, which this says.
    ///
    /// Unification alone would refuse `f : [A] -> [A]` written `f(x) -> x`:
    /// the parameter is closed, and the result's rest is the caller's.
    pub(super) fn subsume(&mut self, actual: &Ty, expected: &Ty) -> Result<bool, Mismatch> {
        let actual = self.resolve(actual);
        let expected = self.resolve(expected);
        match (&actual, &expected) {
            (Ty::Named(a, aa), Ty::Named(b, ba)) if a == b && aa.len() == ba.len() => {
                let mut widened = false;
                for (a, b) in aa.iter().zip(ba.iter()) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                let mut widened = false;
                for (a, b) in a.iter().zip(b.iter()) {
                    widened |= self.subsume(a, b)?;
                }
                Ok(widened)
            }
            (Ty::Record(a, a_tail), Ty::Record(b, b_tail)) => {
                let mut widened = false;
                for (name, field) in a.iter() {
                    if let Some((_, other)) = b.iter().find(|(found, _)| found == name) {
                        widened |= self.subsume(field, other)?;
                    }
                }
                // The shared fields are settled, so the left takes the
                // right's types for them; what remains is which fields each
                // record has.
                let settled = |fields: &[(Symbol, Ty)], other: &[(Symbol, Ty)]| -> Tags {
                    fields
                        .iter()
                        .map(|(name, ty)| {
                            let shared = other.iter().find(|(found, _)| found == name);
                            let ty = shared.map_or_else(|| ty.clone(), |(_, ty)| ty.clone());
                            (*name, Rc::from([ty]))
                        })
                        .collect()
                };
                self.unify_rows(
                    Former::Fields,
                    (&settled(a, b), a_tail.as_deref()),
                    (&entries(b), b_tail.as_deref()),
                )?;
                Ok(widened)
            }
            (Ty::Variants(a, a_tail), Ty::Variants(b, b_tail)) => {
                let mut widened = false;
                for (name, fields) in a.iter() {
                    if let Some((_, other)) = b.iter().find(|(found, _)| found == name) {
                        if fields.len() != other.len() {
                            return Err(Mismatch::Fields(fields.len(), other.len()));
                        }
                        for (field, other) in fields.iter().zip(other.iter()) {
                            widened |= self.subsume(field, other)?;
                        }
                    }
                }
                // The shared tags' fields are settled; what remains is which
                // tags each row holds.
                let settled = |tags: &[Tag], other: &[Tag]| -> Tags {
                    tags.iter()
                        .map(|(name, fields)| {
                            let shared = other.iter().any(|(found, _)| found == name);
                            (
                                *name,
                                if shared {
                                    Rc::default()
                                } else {
                                    fields.clone()
                                },
                            )
                        })
                        .collect()
                };
                let (left, right) = (settled(a, b), settled(b, a));
                match self.unify_rows(
                    Former::Tags,
                    (&left, a_tail.as_deref()),
                    (&right, b_tail.as_deref()),
                ) {
                    Ok(()) => Ok(widened),
                    Err(_)
                        if a_tail.is_none()
                            && matches!(b_tail.as_deref(), Some(Ty::Rigid(_)))
                            && a.iter()
                                .all(|(name, _)| b.iter().any(|(found, _)| found == name)) =>
                    {
                        Ok(true)
                    }
                    // A closed row answered where the row is still being
                    // worked out joins it, as Ori's rows join: the open
                    // row takes the tags only this one holds, and this
                    // value is rebuilt in it where it is answered.
                    Err(_) if a_tail.is_none() && matches!(b_tail.as_deref(), Some(Ty::Var(_))) => {
                        let open = self.fresh();
                        self.unify_rows(
                            Former::Tags,
                            (&left, Some(&open)),
                            (&right, b_tail.as_deref()),
                        )?;
                        Ok(true)
                    }
                    // A closed row holding tags the signature's lacks is
                    // refused for those tags, which is the whole of it.
                    Err(_)
                        if a_tail.is_none() && matches!(b_tail.as_deref(), Some(Ty::Rigid(_))) =>
                    {
                        Err(Mismatch::NotAmong {
                            tags: a
                                .iter()
                                .filter(|(name, _)| !b.iter().any(|(found, _)| found == name))
                                .map(|(name, _)| *name)
                                .collect(),
                            row: expected.clone(),
                        })
                    }
                    Err(mismatch) => Err(mismatch),
                }
            }
            _ => self.unify(&actual, &expected).map(|()| false),
        }
    }

    /// Row unification, for tag rows and record rows alike: entries both
    /// rows hold unify, and each
    /// open side's tail takes the tags only the other holds. A closed row
    /// takes nothing, and neither does a rigid tail, which stands for tags
    /// only a caller knows.
    fn unify_rows(
        &mut self,
        former: Former,
        (left, left_tail): (&[Tag], Option<&Ty>),
        (right, right_tail): (&[Tag], Option<&Ty>),
    ) -> Result<(), Mismatch> {
        for (name, fields) in left {
            if let Some((_, other)) = right.iter().find(|(found, _)| found == name) {
                if fields.len() != other.len() {
                    return Err(Mismatch::Fields(fields.len(), other.len()));
                }
                for (a, b) in fields.iter().zip(other.iter()) {
                    self.unify(a, b)?;
                }
            }
        }
        let only = |from: &[Tag], other: &[Tag]| -> Tags {
            from.iter()
                .filter(|(name, _)| !other.iter().any(|(found, _)| found == name))
                .cloned()
                .collect()
        };
        let (only_left, only_right) = (only(left, right), only(right, left));
        let not_among = |extra: &Tags, tags: &[Tag], tail: Option<&Ty>| Mismatch::NotAmong {
            tags: extra.iter().map(|(name, _)| *name).collect(),
            row: former.build(tags.to_vec(), tail.cloned().map(Rc::new)),
        };
        match (left_tail, right_tail) {
            (None, None) if only_left.is_empty() && only_right.is_empty() => Ok(()),
            (None, None) if only_left.is_empty() => Err(not_among(&only_right, left, None)),
            (None, None) => Err(not_among(&only_left, right, None)),
            (Some(Ty::Var(v)), None) => {
                if !only_left.is_empty() {
                    return Err(not_among(&only_left, right, None));
                }
                self.unify(&Ty::Var(*v), &former.build(only_right, None))
            }
            (None, Some(Ty::Var(v))) => {
                if !only_right.is_empty() {
                    return Err(not_among(&only_right, left, None));
                }
                self.unify(&Ty::Var(*v), &former.build(only_left, None))
            }
            (Some(Ty::Var(v)), Some(Ty::Var(w))) => {
                if v == w {
                    return if only_left.is_empty() && only_right.is_empty() {
                        Ok(())
                    } else {
                        Err(Mismatch::Reason(
                            "two rows share their rest, so neither may hold what the other lacks",
                        ))
                    };
                }
                let rest = Rc::new(self.fresh());
                self.unify(&Ty::Var(*v), &former.build(only_right, Some(rest.clone())))?;
                self.unify(&Ty::Var(*w), &former.build(only_left, Some(rest)))
            }
            (Some(Ty::Var(v)), Some(rigid @ Ty::Rigid(_))) => {
                if !only_left.is_empty() {
                    return Err(not_among(&only_left, right, right_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_right, Some(Rc::new(rigid.clone()))),
                )
            }
            (Some(rigid @ Ty::Rigid(_)), Some(Ty::Var(v))) => {
                if !only_right.is_empty() {
                    return Err(not_among(&only_right, left, left_tail));
                }
                self.unify(
                    &Ty::Var(*v),
                    &former.build(only_left, Some(Rc::new(rigid.clone()))),
                )
            }
            (Some(Ty::Rigid(a)), Some(Ty::Rigid(b)))
                if a == b && only_left.is_empty() && only_right.is_empty() =>
            {
                Ok(())
            }
            _ => Err(Mismatch::Reason(
                "a row whose rest a caller chooses is neither closed nor another caller's",
            )),
        }
    }

    pub(super) fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        self.instantiated(scheme).0
    }

    /// A scheme instantiated, with the variable each of its own became.
    pub(super) fn instantiated(&mut self, scheme: &Scheme) -> (Ty, HashMap<u32, Ty>) {
        let replacements: HashMap<_, _> = scheme
            .variables
            .iter()
            .map(|variable| (*variable, self.fresh()))
            .collect();
        (substitute(&scheme.ty, &replacements), replacements)
    }

    pub(super) fn skolemize(&mut self, scheme: &Scheme) -> (Ty, HashMap<u32, Ty>) {
        let replacements: HashMap<_, _> = scheme
            .variables
            .iter()
            .map(|variable| {
                let rigid = self.next_rigid;
                self.next_rigid = self
                    .next_rigid
                    .checked_add(1)
                    .expect("fewer than 2^32 rigid type variables");
                (*variable, Ty::Rigid(rigid))
            })
            .collect();
        (substitute(&scheme.ty, &replacements), replacements)
    }
}

pub(super) fn contains(ty: &Ty, variable: u32) -> bool {
    match ty {
        Ty::Var(id) => *id == variable,
        Ty::Rigid(_) => false,
        Ty::Named(_, arguments) => arguments.iter().any(|ty| contains(ty, variable)),
        Ty::Function(parameters, result) => {
            parameters.iter().any(|ty| contains(ty, variable)) || contains(result, variable)
        }
        Ty::Variants(tags, tail) => {
            tags.iter()
                .flat_map(|(_, fields)| fields.iter())
                .any(|ty| contains(ty, variable))
                || tail.as_deref().is_some_and(|tail| contains(tail, variable))
        }
        Ty::Record(fields, tail) => {
            fields.iter().any(|(_, ty)| contains(ty, variable))
                || tail.as_deref().is_some_and(|tail| contains(tail, variable))
        }
        Ty::Tuple(members) => members.iter().any(|ty| contains(ty, variable)),
    }
}

pub(super) fn substitute(ty: &Ty, replacements: &HashMap<u32, Ty>) -> Ty {
    replaced(ty, &|leaf| match leaf {
        Ty::Var(id) => replacements.get(id).cloned(),
        _ => None,
    })
}

/// `ty` with each variable, flexible or rigid, that `leaf` answers for
/// replaced by what it answers.
pub(super) fn replaced(ty: &Ty, leaf: &impl Fn(&Ty) -> Option<Ty>) -> Ty {
    match ty {
        Ty::Var(_) | Ty::Rigid(_) => leaf(ty).unwrap_or_else(|| ty.clone()),
        Ty::Named(name, arguments) => Ty::Named(
            *name,
            arguments.iter().map(|ty| replaced(ty, leaf)).collect(),
        ),
        Ty::Function(parameters, result) => Ty::Function(
            parameters.iter().map(|ty| replaced(ty, leaf)).collect(),
            Rc::new(replaced(result, leaf)),
        ),
        Ty::Variants(tags, tail) => Ty::Variants(
            tags.iter()
                .map(|(name, fields)| (*name, fields.iter().map(|ty| replaced(ty, leaf)).collect()))
                .collect(),
            tail.as_deref().map(|tail| Rc::new(replaced(tail, leaf))),
        ),
        Ty::Record(fields, tail) => Ty::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, replaced(ty, leaf)))
                .collect(),
            tail.as_deref().map(|tail| Rc::new(replaced(tail, leaf))),
        ),
        Ty::Tuple(members) => Ty::Tuple(members.iter().map(|ty| replaced(ty, leaf)).collect()),
    }
}

pub(super) fn public_type(ty: &Ty) -> InferredType {
    match ty {
        Ty::Var(variable) => InferredType::Variable(TypeVariable {
            index: *variable,
            rigid: false,
        }),
        Ty::Rigid(variable) => InferredType::Variable(TypeVariable {
            index: *variable,
            rigid: true,
        }),
        Ty::Named(name, arguments) => {
            InferredType::Named(*name, arguments.iter().map(public_type).collect())
        }
        Ty::Function(parameters, result) => InferredType::Function(
            parameters.iter().map(public_type).collect(),
            Box::new(public_type(result)),
        ),
        Ty::Variants(tags, tail) => InferredType::Variants(
            tags.iter()
                .map(|(name, fields)| (*name, fields.iter().map(public_type).collect()))
                .collect(),
            tail.as_deref().map(|tail| Box::new(public_type(tail))),
        ),
        Ty::Record(fields, tail) => InferredType::Record(
            fields
                .iter()
                .map(|(name, ty)| (*name, public_type(ty)))
                .collect(),
            tail.as_deref().map(|tail| Box::new(public_type(tail))),
        ),
        Ty::Tuple(members) => InferredType::Tuple(members.iter().map(public_type).collect()),
    }
}

pub(super) fn free_variables(ty: &Ty) -> Vec<u32> {
    fn collect(ty: &Ty, output: &mut Vec<u32>) {
        match ty {
            Ty::Var(variable) => {
                if !output.contains(variable) {
                    output.push(*variable);
                }
            }
            Ty::Rigid(_) => {}
            Ty::Named(_, arguments) => {
                for ty in arguments.iter() {
                    collect(ty, output);
                }
            }
            Ty::Function(parameters, result) => {
                for ty in parameters.iter() {
                    collect(ty, output);
                }
                collect(result, output);
            }
            Ty::Variants(tags, tail) => {
                for (_, fields) in tags.iter() {
                    for ty in fields.iter() {
                        collect(ty, output);
                    }
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Record(fields, tail) => {
                for (_, ty) in fields.iter() {
                    collect(ty, output);
                }
                if let Some(tail) = tail {
                    collect(tail, output);
                }
            }
            Ty::Tuple(members) => {
                for ty in members.iter() {
                    collect(ty, output);
                }
            }
        }
    }
    let mut output = Vec::new();
    collect(ty, &mut output);
    output
}

pub(super) fn free_scheme(scheme: &Scheme) -> HashSet<u32> {
    free_variables(&scheme.ty)
        .into_iter()
        .filter(|variable| !scheme.variables.contains(variable))
        .collect()
}

/// Whether `small` is `large` with parts left out, as specialization asks
/// of its keys: each part of `small` found in `large`, in its place. Each
/// pair of parts is compared once.
pub(super) fn ty_embeds(small: &Ty, large: &Ty) -> bool {
    TyEmbedding::default().embeds(small, large)
}

#[derive(Default)]
struct TyEmbedding {
    known: HashMap<(*const Ty, *const Ty), bool>,
}

impl TyEmbedding {
    fn embeds(&mut self, small: &Ty, large: &Ty) -> bool {
        let pair = (std::ptr::from_ref(small), std::ptr::from_ref(large));
        if let Some(&found) = self.known.get(&pair) {
            return found;
        }
        let found = self.couples(small, large)
            || Self::parts(large)
                .into_iter()
                .any(|part| self.embeds(small, part));
        self.known.insert(pair, found);
        found
    }

    fn all(&mut self, small: &[Ty], large: &[Ty]) -> bool {
        small.len() == large.len() && small.iter().zip(large).all(|(a, b)| self.embeds(a, b))
    }

    fn tails(&mut self, small: Option<&Rc<Ty>>, large: Option<&Rc<Ty>>) -> bool {
        match (small, large) {
            (None, None) => true,
            (Some(a), Some(b)) => self.embeds(a, b),
            _ => false,
        }
    }

    fn couples(&mut self, small: &Ty, large: &Ty) -> bool {
        match (small, large) {
            (Ty::Var(a), Ty::Var(b)) | (Ty::Rigid(a), Ty::Rigid(b)) => a == b,
            (Ty::Named(a, xs), Ty::Named(b, ys)) => a == b && self.all(xs, ys),
            (Ty::Function(xs, x), Ty::Function(ys, y)) => self.all(xs, ys) && self.embeds(x, y),
            (Ty::Tuple(xs), Ty::Tuple(ys)) => self.all(xs, ys),
            (Ty::Variants(xs, x), Ty::Variants(ys, y)) => {
                xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys.iter())
                        .all(|((a, xs), (b, ys))| a == b && self.all(xs, ys))
                    && self.tails(x.as_ref(), y.as_ref())
            }
            (Ty::Record(xs, x), Ty::Record(ys, y)) => {
                xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys.iter())
                        .all(|((a, x), (b, y))| a == b && self.embeds(x, y))
                    && self.tails(x.as_ref(), y.as_ref())
            }
            _ => false,
        }
    }

    /// The types directly inside `ty`, where they lie in it, so that each
    /// keeps its place as a key while `ty` is borrowed.
    fn parts(ty: &Ty) -> Vec<&Ty> {
        match ty {
            Ty::Var(_) | Ty::Rigid(_) => Vec::new(),
            Ty::Named(_, parts) | Ty::Tuple(parts) => parts.iter().collect(),
            Ty::Function(parameters, result) => {
                parameters.iter().chain([result.as_ref()]).collect()
            }
            Ty::Variants(tags, tail) => tags
                .iter()
                .flat_map(|(_, fields)| fields.iter())
                .chain(tail.as_deref())
                .collect(),
            Ty::Record(fields, tail) => fields
                .iter()
                .map(|(_, field)| field)
                .chain(tail.as_deref())
                .collect(),
        }
    }
}

pub(super) fn show(ty: &Ty, symbols: &Symbols) -> String {
    match ty {
        // A type not yet known is shown as a signature writes one to be
        // inferred: its number is the checker's, and says nothing.
        Ty::Var(_) => "_".to_owned(),
        Ty::Rigid(variable) => format!("'a{variable}"),
        Ty::Named(name, arguments) if arguments.is_empty() => symbols.spelling(*name).to_owned(),
        Ty::Named(name, arguments) => format!(
            "{}({})",
            symbols.spelling(*name),
            arguments
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        // One parameter needs no parentheses, unless it is a tuple or a
        // function, whose own would be read as the list's.
        Ty::Function(parameters, result) => match &**parameters {
            [one] if !matches!(one, Ty::Tuple(_) | Ty::Function(..)) => {
                format!("{} -> {}", show(one, symbols), show(result, symbols))
            }
            _ => format!(
                "({}) -> {}",
                parameters
                    .iter()
                    .map(|ty| show(ty, symbols))
                    .collect::<Vec<_>>()
                    .join(", "),
                show(result, symbols)
            ),
        },
        // An open row shows its rest as `*`: the tags a caller may add.
        Ty::Variants(tags, tail) => {
            let mut shown: Vec<_> = tags
                .iter()
                .map(|(name, fields)| {
                    if fields.is_empty() {
                        symbols.spelling(*name).to_owned()
                    } else {
                        let fields: Vec<_> = fields.iter().map(|ty| show(ty, symbols)).collect();
                        format!("{}({})", symbols.spelling(*name), fields.join(", "))
                    }
                })
                .collect();
            // A rigid rest is a caller's: where it shows, in the body it
            // belongs to, the row is exactly its tags.
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("[{}]", shown.join(", "))
        }
        Ty::Record(fields, tail) => {
            let mut shown: Vec<_> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", symbols.text(*name), show(ty, symbols)))
                .collect();
            if matches!(tail.as_deref(), Some(Ty::Var(_))) {
                shown.push("*".to_owned());
            }
            format!("{{{}}}", shown.join(", "))
        }
        Ty::Tuple(members) => format!(
            "({})",
            members
                .iter()
                .map(|ty| show(ty, symbols))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}
