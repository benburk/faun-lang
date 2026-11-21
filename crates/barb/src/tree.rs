//! Representation-independent roles of recursive tree builders and readers.
use super::{Atom, Body, Expr, FnId, Program, TypeId, TypeShape, type_shape};

/// What a definition does with a recursive tree of scalars.
///
/// One of Barb's facts, as [`Facts::tree_role`](super::Facts::tree_role)
/// answers it, which machine lowering carries on the function it lowers the
/// definition to, for its storage proofs to read.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TreeRole {
    /// Neither builds nor reads one.
    #[default]
    Other,
    /// Builds a tree from scalars alone.
    Builder,
    /// Reads one tree, beside scalars, into a scalar.
    Reader,
}

pub(super) fn analyze(program: &Program, recognized: &super::facts::Recognised) -> Vec<TreeRole> {
    (0..program.functions().len())
        .map(|at| role(program, recognized, FnId::at(at)))
        .collect()
}

fn scalar(program: &Program, ty: TypeId, remaining: usize) -> bool {
    if remaining == 0 {
        return false;
    }
    match type_shape(program, ty) {
        TypeShape::Natural { .. } | TypeShape::Enumeration | TypeShape::Unit { .. } => true,
        TypeShape::Wrapper { field, .. } => scalar(program, field, remaining - 1),
        TypeShape::Product { constructor } => program
            .fields(constructor)
            .iter()
            .all(|&field| scalar(program, field, remaining - 1)),
        _ => false,
    }
}

fn tree(program: &Program, ty: TypeId) -> bool {
    let mut recursive = false;
    let valid = program.ctors(ty).iter().all(|ctor| {
        program.types_of(ctor.fields).iter().all(|&field| {
            if field == ty {
                recursive = true;
                true
            } else {
                scalar(program, field, program.types().len())
            }
        })
    });
    valid && recursive && matches!(type_shape(program, ty), TypeShape::Sum)
}

fn candidate(program: &Program, id: FnId) -> Option<(TreeRole, TypeId)> {
    let result = program.function(id).result;
    let params = program.params(id);
    if tree(program, result)
        && params
            .iter()
            .all(|&ty| scalar(program, ty, program.types().len()))
    {
        Some((TreeRole::Builder, result))
    } else if scalar(program, result, program.types().len()) {
        let trees: Vec<_> = params
            .iter()
            .copied()
            .filter(|&ty| tree(program, ty))
            .collect();
        (trees.len() == 1
            && params
                .iter()
                .all(|&ty| ty == trees[0] || scalar(program, ty, program.types().len())))
        .then(|| (TreeRole::Reader, trees[0]))
    } else {
        None
    }
}

fn role(program: &Program, recognized: &super::facts::Recognised, id: FnId) -> TreeRole {
    let Some(body) = program.function(id).body() else {
        return TreeRole::Other;
    };
    let params = program.params(id);
    let candidate = candidate(program, id);
    let Some((role, tree)) = candidate else {
        return TreeRole::Other;
    };
    let mut scan = Scan {
        program,
        recognized,
        id,
        tree,
        role,
        recurses: false,
        constructs: false,
    };
    if scan.body(body, params.to_vec()).is_some()
        && (role == TreeRole::Reader || scan.recurses && scan.constructs)
    {
        role
    } else {
        TreeRole::Other
    }
}

struct Scan<'a> {
    program: &'a Program,
    recognized: &'a super::facts::Recognised,
    id: FnId,
    tree: TypeId,
    role: TreeRole,
    recurses: bool,
    constructs: bool,
}

impl Scan<'_> {
    fn body(&mut self, body: Body, mut scope: Vec<TypeId>) -> Option<TypeId> {
        for &id in self.program.bindings(body.bindings) {
            scope.push(self.expr(self.program.expr(id), &scope)?);
        }
        self.expr(self.program.expr(body.tail), &scope)
    }

    fn match_(&mut self, on: Atom, arms: super::Range, scope: &[TypeId]) -> Option<TypeId> {
        if scope[on.0.index()] == self.tree && self.role != TreeRole::Reader {
            return None;
        }
        let mut result = None;
        for arm in self.program.arms(arms) {
            let mut inner = scope.to_vec();
            inner.extend_from_slice(self.program.fields(arm.ctor));
            let found = self.body(arm.body, inner)?;
            if result.is_some_and(|other| other != found) {
                return None;
            }
            result = Some(found);
        }
        result
    }

    fn expr(&mut self, expr: Expr, scope: &[TypeId]) -> Option<TypeId> {
        let ty = |atom: Atom| scope[atom.0.index()];
        match expr {
            Expr::Atom(atom) => Some(ty(atom)),
            Expr::Static(value) => {
                let value = self.program.constant(value);
                let owner = value.owner();
                // Static leaves are self-contained; other known trees require
                // a separate analysis of their descendants.
                (owner != self.tree || self.program.fields(value.constructor()).is_empty())
                    .then_some(owner)
            }
            Expr::Con(ctor, args) => {
                let owner = self.program.ctor(ctor).owner;
                if owner == self.tree {
                    if self.role != TreeRole::Builder {
                        return None;
                    }
                    self.constructs = true;
                } else if self.program.atoms(args).iter().any(|&a| ty(a) == self.tree) {
                    return None;
                }
                Some(owner)
            }
            Expr::Call(callee, args) => {
                if callee == self.id {
                    self.recurses = true;
                } else if !self.recognized.answered(callee)
                    || self.program.atoms(args).iter().any(|&a| ty(a) == self.tree)
                {
                    return None;
                }
                Some(self.program.function(callee).result)
            }
            Expr::Match(on, arms) => self.match_(on, arms, scope),
        }
    }
}
