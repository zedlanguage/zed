//! Dropping the syntax tree. Each child is moved to a work list before its parent goes, so a
//! tree of any depth is dropped on the heap, not the thread stack.

use std::mem;

use super::{
    Annot, BoundaryItem, Expr, ExprKind, Field, Function, IndexKey, IndexedDef, Method, Param,
    Pattern, RangeEnd, Stmt, StmtKind, StrPart, Struct, Type, TypeKind,
};

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        expr_kids(&mut self.kind, &mut stack);
        while let Some(mut e) = stack.pop() {
            expr_kids(&mut e.kind, &mut stack);
        }
    }
}

/// Moves the expressions directly in `kind` to `out`, and leaves a leaf in its place.
fn expr_kids(kind: &mut ExprKind, out: &mut Vec<Expr>) {
    match mem::replace(kind, ExprKind::Bool(false)) {
        ExprKind::Int { .. }
        | ExprKind::Float(_)
        | ExprKind::Rat(_)
        | ExprKind::Bool(_)
        | ExprKind::Atom(_)
        | ExprKind::Name(_)
        | ExprKind::This
        | ExprKind::Section(_) => {}
        ExprKind::Str(parts) => out.extend(parts.into_iter().filter_map(|p| match p {
            StrPart::Hole(e) => Some(e),
            StrPart::Text(_) => None,
        })),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Member { of: a, .. }
        | ExprKind::Read { of: a, .. }
        | ExprKind::Loop { body: a, .. }
        | ExprKind::Break(a)
        | ExprKind::Spread { of: a, .. }
        | ExprKind::SortKey { key: a, .. } => out.push(*a),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::In { of: a, set: b, .. }
        | ExprKind::Reduce { of: a, op: b }
        | ExprKind::Else {
            of: a, default: b, ..
        } => {
            out.push(*a);
            out.push(*b);
        }
        ExprKind::Call {
            callee,
            mut positional,
            named,
            ..
        } => {
            out.push(*callee);
            out.append(&mut positional);
            out.extend(named.into_iter().map(|(_, e)| e));
        }
        ExprKind::Tuple(mut es) | ExprKind::Seq(mut es) | ExprKind::Set(mut es) => {
            out.append(&mut es)
        }
        ExprKind::Map(entries) => {
            for (k, v) in entries {
                out.extend([k, v]);
            }
        }
        ExprKind::Range(from, to) => {
            out.push(*from);
            match to {
                RangeEnd::Below(b) | RangeEnd::Through(b) => out.push(*b),
                RangeEnd::Open => {}
            }
        }
        ExprKind::For {
            source,
            guard,
            body,
            ..
        } => {
            out.push(*source);
            out.extend(guard.map(|g| *g));
            out.push(*body);
        }
        ExprKind::Lambda { params, body } => {
            param_kids(params, out);
            out.push(*body);
        }
        ExprKind::Block(stmts) => {
            for Stmt { kind, .. } in stmts {
                stmt_kids(kind, out);
            }
        }
        ExprKind::Match { of, arms } => {
            out.push(*of);
            for a in arms {
                out.extend(a.guard);
                out.push(a.body);
            }
        }
        ExprKind::Record(fields) => out.extend(fields.into_iter().map(|(_, e)| e)),
        ExprKind::With { of, updates } => {
            out.push(*of);
            out.extend(updates.into_iter().map(|u| u.value));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => out.extend([*cond, *then, *otherwise]),
    }
}

/// Moves the expressions directly in the statement `kind` to `out`.
fn stmt_kids(kind: StmtKind, out: &mut Vec<Expr>) {
    match kind {
        StmtKind::Bind {
            value, boundary, ..
        } => {
            out.push(value);
            boundary_kids(boundary, out);
        }
        StmtKind::Push { value, .. }
        | StmtKind::While(value)
        | StmtKind::Until(value)
        | StmtKind::Expr(value) => out.push(value),
        StmtKind::IndexedDef(IndexedDef {
            keys,
            value,
            boundary,
            ..
        }) => {
            key_kids(keys, out);
            out.push(value);
            boundary_kids(boundary, out);
        }
        // A `mutable` holds a binding, so this recursion is one level deep.
        StmtKind::Mutable(decl) => stmt_kids(decl.kind, out),
        StmtKind::Return(mut es) => out.append(&mut es),
        StmtKind::Function(f) | StmtKind::Method(Method { function: f, .. }) => {
            function_kids(f, out)
        }
        StmtKind::Struct(Struct { fields, .. }) => {
            out.extend(fields.into_iter().filter_map(|f| match f {
                Field::Typed { default, .. } => default,
                Field::Import { .. } => None,
            }))
        }
        StmtKind::Type(_) | StmtKind::Import(_) => {}
        // The declaration is not annotated again, so this recursion is one level deep.
        StmtKind::Annotated { annots, decl } => {
            for Annot {
                positional, named, ..
            } in annots
            {
                out.extend(positional);
                out.extend(named.into_iter().map(|(_, e)| e));
            }
            stmt_kids(decl.kind, out);
        }
    }
}

fn key_kids(keys: Vec<IndexKey>, out: &mut Vec<Expr>) {
    out.extend(keys.into_iter().map(|k| match k {
        IndexKey::In { set, .. } => set,
        IndexKey::At(e) => e,
    }));
}

fn boundary_kids(items: Vec<BoundaryItem>, out: &mut Vec<Expr>) {
    for b in items {
        key_kids(b.keys, out);
        out.push(b.value);
    }
}

fn function_kids(f: Function, out: &mut Vec<Expr>) {
    let Function {
        params,
        body,
        tests,
        ..
    } = f;
    param_kids(params, out);
    out.push(body);
    for (a, b) in tests {
        out.extend([a, b]);
    }
}

fn param_kids(params: Vec<Param>, out: &mut Vec<Expr>) {
    out.extend(params.into_iter().filter_map(|p| p.default));
}

impl Drop for Type {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        type_kids(&mut self.kind, &mut stack);
        while let Some(mut t) = stack.pop() {
            type_kids(&mut t.kind, &mut stack);
        }
    }
}

/// Moves the types directly in `kind` to `out`, and leaves a leaf in its place.
fn type_kids(kind: &mut TypeKind, out: &mut Vec<Type>) {
    match mem::replace(kind, TypeKind::Name(String::new())) {
        TypeKind::Name(_) | TypeKind::Atom(_) => {}
        TypeKind::Tuple(mut ts) | TypeKind::Union(mut ts) | TypeKind::And(mut ts) => {
            out.append(&mut ts);
        }
        TypeKind::Diff(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TypeKind::Arrow { params, result, .. } => {
            out.extend(params.into_iter().map(|p| p.ty));
            out.push(*result);
        }
        TypeKind::Bounded {
            lower,
            upper,
            result,
        } => out.extend([*lower, *upper, *result]),
        TypeKind::Apply(_, params) | TypeKind::AtomApply(_, params) => {
            out.extend(params.into_iter().map(|p| p.ty));
        }
        TypeKind::Record(fields) => out.extend(fields.into_iter().map(|(_, t)| t)),
        TypeKind::Seq(t) => out.push(*t),
    }
}

impl Drop for Pattern {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        pattern_kids(self, &mut stack);
        while let Some(mut p) = stack.pop() {
            pattern_kids(&mut p, &mut stack);
        }
    }
}

/// Moves the patterns directly in `p` to `out`.
fn pattern_kids(p: &mut Pattern, out: &mut Vec<Pattern>) {
    match p {
        Pattern::Atom { fields, items, .. } => {
            out.append(items);
            out.extend(mem::take(fields).into_iter().filter_map(|(_, p)| p));
        }
        Pattern::Struct { fields, .. } => {
            out.extend(mem::take(fields).into_iter().filter_map(|(_, p)| p));
        }
        Pattern::Tuple(items, _) => out.append(items),
        // A type and an expression drop by their own work lists, and a range pattern holds
        // two literal patterns.
        Pattern::Name(..)
        | Pattern::Wild(_)
        | Pattern::Is { .. }
        | Pattern::Lit(_)
        | Pattern::Range { .. } => {}
    }
}
