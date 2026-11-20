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
        | ExprKind::Section(..) => {}
        ExprKind::Str(parts) => out.extend(parts.iter_mut().filter_map(|p| match p {
            StrPart::Hole(e) => Some(e),
            StrPart::Text(_) => None,
        })),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Member { of: a, .. }
        | ExprKind::Read { of: a, .. }
        | ExprKind::Loop { body: a, .. }
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
        ExprKind::Remap { of, levels, .. } => {
            out.push(of);
            for l in levels.iter_mut().flatten() {
                out.extend(l.key.as_mut());
                out.extend(l.reduce.as_mut());
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

/// What [`expr_kids`] gives for a block `{ … }`: each caller says which it wants, since a
/// block is the one expression whose children are statements, not expressions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blocks {
    /// Nothing: the caller walks a block's statements itself, because what a statement
    /// means differs from one reader to the next (the checker's `blocking` walk records each
    /// `<-` with the function that runs it, and pushes a block's statements as statements).
    Skip,
    /// The expressions directly in the block's statements, as [`stmts_exprs`] lists them: for
    /// a caller that asks a question of every expression below a node, such as whether it
    /// reads a name (the checker's remap `mentions`), and that would miss a read written
    /// only inside `{ … }` if blocks were skipped (FAIL-remap-mentions).
    Enter,
}

/// Gives `push` the expressions directly in `kind`, in the order [`expr_kids_mut`] lists
/// them; for a block, those of its statements with [`Blocks::Enter`], none with
/// [`Blocks::Skip`]. The read-only twin of [`expr_kids_mut`]: Rust gives no one body for `&`
/// and `&mut`, so the two sit side by side and a test (`ast/walk/tests.rs`) checks that they
/// list the same expressions, blocks included, with [`Blocks::Enter`].
pub fn expr_kids<'a>(kind: &'a ExprKind, blocks: Blocks, push: &mut impl FnMut(&'a Expr)) {
    match kind {
        ExprKind::Int { .. }
        | ExprKind::Float { .. }
        | ExprKind::Rat(_)
        | ExprKind::Bool(_)
        | ExprKind::Atom(_)
        | ExprKind::Name(_)
        | ExprKind::This
        | ExprKind::Section(..) => {}
        ExprKind::Block(stmts) => match blocks {
            Blocks::Skip => {}
            Blocks::Enter => stmts_exprs(stmts, push),
        },
        ExprKind::Str(parts) => (parts.iter()).for_each(|p| match p {
            StrPart::Hole(e) => push(e),
            StrPart::Text(_) => {}
        }),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Member { of: a, .. }
        | ExprKind::Read { of: a, .. }
        | ExprKind::Loop { body: a, .. }
        | ExprKind::Spread { of: a, .. } => push(a),
        ExprKind::SortKey { key, .. } => key.as_deref().into_iter().for_each(push),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::In { of: a, set: b, .. }
        | ExprKind::Reduce { of: a, op: b }
        | ExprKind::Else {
            of: a, default: b, ..
        } => {
            push(a);
            push(b);
        }
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } => {
            push(callee);
            positional.iter().for_each(&mut *push);
            named.iter().for_each(|(_, e)| push(e));
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => es.iter().for_each(push),
        ExprKind::Map(entries) => entries.iter().for_each(|(k, v)| {
            push(k);
            push(v);
        }),
        ExprKind::Range(from, to) => {
            push(from);
            match to {
                RangeEnd::Below(b) | RangeEnd::Through(b) => push(b),
                RangeEnd::Open => {}
            }
        }
        ExprKind::Remap { of, levels, .. } => {
            push(of);
            for l in levels.iter().flatten() {
                l.key.iter().chain(&l.reduce).for_each(&mut *push);
            }
        }
        ExprKind::For {
            source,
            guard,
            body,
            ..
        } => {
            push(source);
            guard.as_deref().into_iter().for_each(&mut *push);
            push(body);
        }
        ExprKind::Lambda { params, body } => {
            params
                .iter()
                .filter_map(|p| p.default.as_ref())
                .for_each(&mut *push);
            push(body);
        }
        ExprKind::Match { of, arms } => {
            push(of);
            for a in arms {
                a.guard.iter().for_each(&mut *push);
                push(&a.body);
            }
        }
        ExprKind::Record(fields) => fields.iter().for_each(|(_, e)| push(e)),
        ExprKind::With { of, updates } => {
            push(of);
            updates.iter().for_each(|u| push(&u.value));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            push(cond);
            push(then);
            push(otherwise);
        }
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
        StmtKind::Type(_) | StmtKind::Import(_) | StmtKind::Break => {}
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

/// Gives `push` the expressions directly in the statements `stmts`, in the order
/// [`stmts_exprs_mut`] lists them: its read-only twin, with the private twins below of
/// `stmt_kids`, `leaf_kids` and the rest, checked against them by a test
/// (`ast/walk/tests.rs`).
pub fn stmts_exprs<'a>(stmts: &'a [Stmt], push: &mut impl FnMut(&'a Expr)) {
    for s in stmts {
        stmt_kids_ref(&s.kind, push);
    }
}

/// The read-only twin of `stmt_kids`.
fn stmt_kids_ref<'a>(mut kind: &'a StmtKind, push: &mut impl FnMut(&'a Expr)) {
    loop {
        match kind {
            StmtKind::Local(decl) => kind = &decl.kind,
            StmtKind::Annotated { annots, decl } => {
                annots.iter().for_each(|a| annot_kids_ref(a, push));
                kind = &decl.kind;
            }
            leaf => return leaf_kids_ref(leaf, push),
        }
    }
}

/// The read-only twin of `leaf_kids`.
fn leaf_kids_ref<'a>(kind: &'a StmtKind, push: &mut impl FnMut(&'a Expr)) {
    match kind {
        StmtKind::Local(_) | StmtKind::Annotated { .. } => stmt_kids_ref(kind, push),
        StmtKind::Initial(i) => {
            key_kids_ref(&i.keys, push);
            push(&i.value);
        }
        StmtKind::Bind { value, .. }
        | StmtKind::Push { value, .. }
        | StmtKind::While(value)
        | StmtKind::Until(value)
        | StmtKind::Expr(value) => push(value),
        StmtKind::IndexedDef(IndexedDef {
            keys,
            value,
            boundary,
            ..
        }) => {
            key_kids_ref(keys, push);
            push(value);
            for BoundaryItem { keys, value, .. } in boundary {
                key_kids_ref(keys, push);
                push(value);
            }
        }
        StmtKind::Return(es) => es.iter().for_each(&mut *push),
        StmtKind::Function(f) => function_kids_ref(f, push),
        StmtKind::Method(m) => function_kids_ref(&m.function, push),
        StmtKind::Struct(Struct { fields, .. }) => {
            for f in fields {
                if let Field::Typed {
                    default: Some(d), ..
                } = f
                {
                    push(d);
                }
            }
        }
        StmtKind::Type(_) | StmtKind::Import(_) | StmtKind::Break => {}
        StmtKind::UnitAnnot(a) => annot_kids_ref(a, push),
    }
}

/// The read-only twin of `function_kids`.
fn function_kids_ref<'a>(f: &'a Function, push: &mut impl FnMut(&'a Expr)) {
    (f.params.iter()).for_each(|p| p.default.iter().for_each(&mut *push));
    push(&f.body);
    for (a, b) in &f.tests {
        push(a);
        push(b);
    }
    (f.given.iter())
        .flat_map(|t| &t.ports)
        .for_each(|p| push(&p.value));
}

/// The read-only twin of `annot_kids`.
fn annot_kids_ref<'a>(a: &'a Annot, push: &mut impl FnMut(&'a Expr)) {
    a.positional.iter().for_each(&mut *push);
    a.named.iter().for_each(|(_, e)| push(e));
}

/// The read-only twin of `key_kids`.
fn key_kids_ref<'a>(keys: &'a [IndexKey], push: &mut impl FnMut(&'a Expr)) {
    for k in keys {
        match k {
            IndexKey::In { set, .. } => push(set),
            IndexKey::At(e) => push(e),
        }
    }
}

#[cfg(test)]
mod tests;
