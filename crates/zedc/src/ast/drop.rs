//! Dropping the syntax tree. Each child is moved to a work list before its parent goes, so a
//! tree of any depth is dropped on the heap, not the thread stack.

use std::mem;

use super::{Expr, ExprKind, Function, Param, Pattern, Stmt, StmtKind, StrPart, Type, TypeKind};

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
        | ExprKind::Name(_) => {}
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
                match kind {
                    StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => out.push(value),
                    StmtKind::Return(mut es) => out.append(&mut es),
                    StmtKind::Function(Function {
                        params,
                        body,
                        tests,
                        ..
                    }) => {
                        param_kids(params, out);
                        out.push(body);
                        for (a, b) in tests {
                            out.extend([a, b]);
                        }
                    }
                }
            }
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => out.extend([*cond, *then, *otherwise]),
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
    let Pattern::Atom { fields, items, .. } = p;
    out.append(items);
    out.extend(mem::take(fields).into_iter().filter_map(|(_, p)| p));
}
