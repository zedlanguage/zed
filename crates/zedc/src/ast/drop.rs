//! Dropping the syntax tree. Each child is moved to a work list before its parent goes, so a
//! tree of any depth is dropped on the heap, not the thread stack.

use std::mem;

use super::{
    Annot, Expr, ExprKind, Field, Function, Method, Param, Pattern, Stmt, StmtKind, StrPart,
    Struct, Type, TypeKind,
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
        | ExprKind::This => {}
        ExprKind::Str(parts) => out.extend(parts.into_iter().filter_map(|p| match p {
            StrPart::Hole(e) => Some(e),
            StrPart::Text(_) => None,
        })),
        ExprKind::Unary(_, a) | ExprKind::Is { of: a, .. } | ExprKind::Member { of: a, .. } => {
            out.push(*a)
        }
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
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
        ExprKind::Tuple(mut es) => out.append(&mut es),
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
        StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => out.push(value),
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
        TypeKind::Apply(_, params) | TypeKind::AtomApply(_, params) => {
            out.extend(params.into_iter().map(|p| p.ty));
        }
        TypeKind::Record(fields) => out.extend(fields.into_iter().map(|(_, t)| t)),
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
        // A type and an expression drop by their own work lists.
        Pattern::Name(..) | Pattern::Wild(_) | Pattern::Is { .. } | Pattern::Lit(_) => {}
    }
}
