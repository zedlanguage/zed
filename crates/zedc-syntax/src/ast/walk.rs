//! A walk over the expressions of a syntax tree that may change them: the children of each
//! node are pushed on a work list, so a tree of any depth is walked on the heap, not the
//! thread stack. The children listed are those [`super::drop`] moves out, so the two agree.

use super::{
    Annot, BoundaryItem, Expr, ExprKind, Field, Function, IndexKey, IndexedDef, Initial, Param,
    RangeEnd, Stmt, StmtKind, StrPart, Struct,
};

/// Pushes the expressions directly in `kind` to `out`.
pub fn expr_kids_mut<'a>(kind: &'a mut ExprKind, out: &mut Vec<&'a mut Expr>) {
    match kind {
        ExprKind::Int { .. }
        | ExprKind::Float { .. }
        | ExprKind::Rat(_)
        | ExprKind::Bool(_)
        | ExprKind::Atom(_)
        | ExprKind::Name(_)
        | ExprKind::This
        | ExprKind::Section(_) => {}
        ExprKind::Str(parts) => out.extend(parts.iter_mut().filter_map(|p| match p {
            StrPart::Hole(e) => Some(e),
            StrPart::Text(_) => None,
        })),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Member { of: a, .. }
        | ExprKind::Read { of: a, .. }
        | ExprKind::Loop { body: a, .. }
        | ExprKind::Break(a)
        | ExprKind::Spread { of: a, .. } => out.push(a),
        ExprKind::SortKey { key, .. } => out.extend(key.as_deref_mut()),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::In { of: a, set: b, .. }
        | ExprKind::Reduce { of: a, op: b }
        | ExprKind::Else {
            of: a, default: b, ..
        } => out.extend([&mut **a, &mut **b]),
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } => {
            out.push(callee);
            out.extend(positional.iter_mut());
            out.extend(named.iter_mut().map(|(_, e)| e));
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => out.extend(es.iter_mut()),
        ExprKind::Map(entries) => {
            for (k, v) in entries {
                out.extend([k, v]);
            }
        }
        ExprKind::Range(from, to) => {
            out.push(from);
            match to {
                RangeEnd::Below(b) | RangeEnd::Through(b) => out.push(b),
                RangeEnd::Open => {}
            }
        }
        ExprKind::For {
            source,
            guard,
            body,
            ..
        } => {
            out.push(source);
            out.extend(guard.as_deref_mut());
            out.push(body);
        }
        ExprKind::Lambda { params, body } => {
            param_kids(params, out);
            out.push(body);
        }
        ExprKind::Block(stmts) => stmts_exprs_mut(stmts, out),
        ExprKind::Match { of, arms } => {
            out.push(of);
            for a in arms {
                out.extend(a.guard.as_mut());
                out.push(&mut a.body);
            }
        }
        ExprKind::Record(fields) => out.extend(fields.iter_mut().map(|(_, e)| e)),
        ExprKind::With { of, updates } => {
            out.push(of);
            out.extend(updates.iter_mut().map(|u| &mut u.value));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => out.extend([&mut **cond, &mut **then, &mut **otherwise]),
    }
}

/// Pushes the expressions directly in the statements `stmts` to `out`.
pub fn stmts_exprs_mut<'a>(stmts: &'a mut [Stmt], out: &mut Vec<&'a mut Expr>) {
    for s in stmts {
        stmt_kids(&mut s.kind, out);
    }
}

/// Pushes the expressions directly in the statement `kind` to `out`.
fn stmt_kids<'a>(mut kind: &'a mut StmtKind, out: &mut Vec<&'a mut Expr>) {
    // `local` and an annotation wrap one declaration each; they are unwrapped in this loop, so
    // a chain of them takes no stack. Every other statement ends it.
    loop {
        match kind {
            StmtKind::Local(decl) => kind = &mut decl.kind,
            StmtKind::Annotated { annots, decl } => {
                annots.iter_mut().for_each(|a| annot_kids(a, out));
                kind = &mut decl.kind;
            }
            leaf => return leaf_kids(leaf, out),
        }
    }
}

/// Pushes the expressions directly in the statement `kind`, which is neither `local` nor
/// annotated, to `out`.
fn leaf_kids<'a>(kind: &'a mut StmtKind, out: &mut Vec<&'a mut Expr>) {
    match kind {
        // Unwrapped by `stmt_kids`; a wrapper reached here is walked as it does.
        StmtKind::Local(_) | StmtKind::Annotated { .. } => stmt_kids(kind, out),
        StmtKind::Initial(i) => {
            let Initial { keys, value, .. } = &mut **i;
            key_kids(keys, out);
            out.push(value);
        }
        StmtKind::Bind { value, .. }
        | StmtKind::Push { value, .. }
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
            for BoundaryItem { keys, value, .. } in boundary {
                key_kids(keys, out);
                out.push(value);
            }
        }
        StmtKind::Return(es) => out.extend(es.iter_mut()),
        StmtKind::Function(f) => function_kids(f, out),
        StmtKind::Method(m) => function_kids(&mut m.function, out),
        StmtKind::Struct(Struct { fields, .. }) => {
            out.extend(fields.iter_mut().filter_map(|f| match f {
                Field::Typed { default, .. } => default.as_mut(),
                Field::Import { .. } => None,
            }))
        }
        StmtKind::Type(_) | StmtKind::Import(_) => {}
        StmtKind::UnitAnnot(a) => annot_kids(a, out),
    }
}

fn function_kids<'a>(f: &'a mut Function, out: &mut Vec<&'a mut Expr>) {
    let Function {
        params,
        body,
        tests,
        given,
        ..
    } = f;
    param_kids(params, out);
    out.push(body);
    for (a, b) in tests {
        out.extend([a, b]);
    }
    out.extend(
        given
            .iter_mut()
            .flat_map(|t| &mut t.ports)
            .map(|p| &mut p.value),
    );
}

fn annot_kids<'a>(a: &'a mut Annot, out: &mut Vec<&'a mut Expr>) {
    out.extend(a.positional.iter_mut());
    out.extend(a.named.iter_mut().map(|(_, e)| e));
}

fn key_kids<'a>(keys: &'a mut [IndexKey], out: &mut Vec<&'a mut Expr>) {
    out.extend(keys.iter_mut().map(|k| match k {
        IndexKey::In { set, .. } => set,
        IndexKey::At(e) => e,
    }));
}

fn param_kids<'a>(params: &'a mut [Param], out: &mut Vec<&'a mut Expr>) {
    out.extend(params.iter_mut().filter_map(|p| p.default.as_mut()));
}
