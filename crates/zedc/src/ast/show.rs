//! The s-expression text of the syntax tree. Nesting costs heap, not thread stack: a job writes
//! its text or pushes what it is made of, and a tree of any depth prints.

use std::fmt;

use super::{
    Annot, BoundaryItem, Expr, ExprKind, Field, Function, ImportKind, IndexKey, Param, Pattern, Stmt,
    StmtKind, StrPart, Target, Type, TypeKind, TypeParam,
};

/// What is left to write.
enum Show<'a> {
    Text(&'a str),
    Owned(String),
    Quoted(&'a str),
    Expr(&'a Expr),
    Stmt(&'a Stmt),
    Type(&'a Type),
    Param(&'a Param),
    Pattern(&'a Pattern),
}

use Show::Text;

/// Writes `first` and all it is made of. Each job pushes its parts in written order, and they
/// are turned around to run in that order.
fn write(f: &mut fmt::Formatter<'_>, first: Show<'_>) -> fmt::Result {
    let mut stack = vec![first];
    while let Some(job) = stack.pop() {
        let mark = stack.len();
        match job {
            Text(s) => f.write_str(s)?,
            Show::Owned(s) => f.write_str(&s)?,
            Show::Quoted(s) => write!(f, "{s:?}")?,
            Show::Expr(e) => expr(e, &mut stack),
            Show::Stmt(s) => stmt(s, &mut stack),
            Show::Type(t) => ty(t, &mut stack),
            Show::Param(p) => param(p, &mut stack),
            Show::Pattern(p) => pattern(p, &mut stack),
        }
        stack[mark..].reverse();
    }
    Ok(())
}

/// Pushes each part after a space.
fn each<'a, T: 'a>(
    out: &mut Vec<Show<'a>>,
    items: impl IntoIterator<Item = &'a T>,
    show: impl Fn(&'a T) -> Show<'a>,
) {
    for x in items {
        out.extend([Text(" "), show(x)]);
    }
}

/// An s-expression: `(call f 1 (x: 2) ...)`, `(index m k)`, `(. p x)`, `(?. p x)`, `(+ a b)`,
/// `(tuple a b)`, `(fn (x (y: int)) e)`, `(is e T)`, `(else e #a d)`, `(record (x: 1))`,
/// `(with p (= c.x 1))`, `(match x (-> p e) (-> q (where c) f))`; from layer L3 `(..< a b)`,
/// `(.. a)`, `(in x s)`, `(not in x s)`, `(>< m op)`, `(:: xs len)`, `(section +)`, `(array a b)`,
/// `(set a b)`, `(map (-> k v))`, and `(for (k v) m (where c) body)`; from layer L6 `(loop t body)`,
/// `(break e)` and `(*. c m)`.
fn expr<'a>(e: &'a Expr, out: &mut Vec<Show<'a>>) {
    let at = |e: &'a Expr| Show::Expr(e);
    match &e.kind {
        ExprKind::Int { radix, digits } => {
            let prefix = match radix {
                2 => "0b",
                8 => "0o",
                16 => "0x",
                _ => "",
            };
            out.extend([Text(prefix), Text(digits)]);
        }
        ExprKind::Float(s) => out.push(Text(s)),
        ExprKind::Rat(s) => out.extend([Text(s), Text("r")]),
        ExprKind::Str(parts) => {
            out.push(Text("(str"));
            each(out, parts, |p| match p {
                StrPart::Text(t) => Show::Quoted(t),
                StrPart::Hole(e) => Show::Expr(e),
            });
            out.push(Text(")"));
        }
        ExprKind::Bool(b) => out.push(Text(if *b { "true" } else { "false" })),
        ExprKind::Atom(a) => out.extend([Text("#"), Text(a)]),
        ExprKind::Name(n) => out.push(Text(n)),
        ExprKind::Unary(op, e) => out.extend([Text("("), Text(op), Text(" "), at(e), Text(")")]),
        ExprKind::Binary(op, a, b) => out.extend([
            Text("("),
            Text(op),
            Text(" "),
            at(a),
            Text(" "),
            at(b),
            Text(")"),
        ]),
        ExprKind::Call {
            callee,
            positional,
            named,
            curry,
        } => {
            out.extend([Text("(call "), at(callee)]);
            each(out, positional, Show::Expr);
            for (n, a) in named {
                out.extend([Text(" ("), Text(n), Text(": "), Show::Expr(a), Text(")")]);
            }
            out.push(Text(if *curry { " ...)" } else { ")" }));
        }
        ExprKind::Index(e, k) => {
            out.extend([Text("(index "), at(e), Text(" "), at(k), Text(")")]);
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => out.extend([
            Text("(if "),
            at(cond),
            Text(" "),
            at(then),
            Text(" "),
            at(otherwise),
            Text(")"),
        ]),
        ExprKind::Block(stmts) => {
            out.push(Text("(block"));
            each(out, stmts, Show::Stmt);
            out.push(Text(")"));
        }
        ExprKind::Tuple(es) => {
            out.push(Text("(tuple"));
            each(out, es, Show::Expr);
            out.push(Text(")"));
        }
        ExprKind::Lambda { params, body } => {
            out.push(Text("(fn ("));
            params_spaced(params, out);
            out.extend([Text(") "), at(body), Text(")")]);
        }
        ExprKind::Is { of, ty, negated } => out.extend([
            Text(if *negated { "(is not " } else { "(is " }),
            at(of),
            Text(" "),
            Show::Type(ty),
            Text(")"),
        ]),
        ExprKind::Else {
            of,
            pattern,
            default,
        } => {
            out.extend([Text("(else "), at(of), Text(" ")]);
            if let Some(p) = pattern {
                out.extend([Show::Pattern(p), Text(" ")]);
            }
            out.extend([at(default), Text(")")]);
        }
        ExprKind::Member { of, name, safe } => out.extend([
            Text(if *safe { "(?. " } else { "(. " }),
            at(of),
            Text(" "),
            Text(name),
            Text(")"),
        ]),
        ExprKind::Record(fields) => {
            out.push(Text("(record"));
            for (n, v) in fields {
                out.extend([Text(" ("), Text(n), Text(": "), at(v), Text(")")]);
            }
            out.push(Text(")"));
        }
        ExprKind::With { of, updates } => {
            out.extend([Text("(with "), at(of)]);
            for u in updates {
                out.push(Text(" (= "));
                let mut sep = "";
                for p in &u.path {
                    out.extend([Text(sep), Text(p)]);
                    sep = ".";
                }
                out.extend([Text(" "), at(&u.value), Text(")")]);
            }
            out.push(Text(")"));
        }
        ExprKind::This => out.push(Text("this")),
        ExprKind::Match { of, arms } => {
            out.extend([Text("(match "), at(of)]);
            for a in arms {
                out.extend([Text(" (-> "), Show::Pattern(&a.pattern), Text(" ")]);
                if let Some(g) = &a.guard {
                    out.extend([Text("(where "), at(g), Text(") ")]);
                }
                out.extend([at(&a.body), Text(")")]);
            }
            out.push(Text(")"));
        }
        ExprKind::Range(from, to) => {
            out.extend([Text("("), Text(to.op()), Text(" "), at(from)]);
            if let Some(b) = to.bound() {
                out.extend([Text(" "), at(b)]);
            }
            out.push(Text(")"));
        }
        ExprKind::In { of, set, negated } => out.extend([
            Text(if *negated { "(not in " } else { "(in " }),
            at(of),
            Text(" "),
            at(set),
            Text(")"),
        ]),
        ExprKind::Reduce { of, op } => {
            out.extend([Text("(>< "), at(of), Text(" "), at(op), Text(")")]);
        }
        ExprKind::Read { of, name } => {
            out.extend([Text("(:: "), at(of), Text(" "), Text(name), Text(")")]);
        }
        ExprKind::Section(op) => out.extend([Text("(section "), Text(op), Text(")")]),
        ExprKind::Array(es) => {
            out.push(Text("(array"));
            each(out, es, Show::Expr);
            out.push(Text(")"));
        }
        ExprKind::Set(es) => {
            out.push(Text("(set"));
            each(out, es, Show::Expr);
            out.push(Text(")"));
        }
        ExprKind::Map(entries) => {
            out.push(Text("(map"));
            for (k, v) in entries {
                out.extend([Text(" (-> "), at(k), Text(" "), at(v), Text(")")]);
            }
            out.push(Text(")"));
        }
        ExprKind::For {
            binders,
            source,
            guard,
            body,
        } => {
            out.push(Text("(for ("));
            let mut sep = "";
            for b in binders {
                out.extend([Text(sep), Text(target(b))]);
                sep = " ";
            }
            out.extend([Text(") "), at(source), Text(" ")]);
            if let Some(g) = guard {
                out.extend([Text("(where "), at(g), Text(") ")]);
            }
            out.extend([at(body), Text(")")]);
        }
        ExprKind::Loop { label, body } => {
            out.push(Text("(loop "));
            if let Some(l) = label {
                out.extend([Text(l), Text(" ")]);
            }
            out.extend([at(body), Text(")")]);
        }
        ExprKind::Break(e) => out.extend([Text("(break "), at(e), Text(")")]),
        ExprKind::Spread { of, name } => {
            out.extend([Text("(*. "), at(of), Text(" "), Text(name), Text(")")]);
        }
        ExprKind::SortKey { desc, key } => {
            let word = if *desc { "(desc " } else { "(asc " };
            out.extend([Text(word), at(key), Text(")")]);
        }
    }
}

fn target(t: &Target) -> &str {
    match t {
        Target::Name(n) => n,
        Target::Wild => "_",
    }
}

/// The keys of an indexed definition or a boundary value: `((in i s) (at k))`.
fn keys<'a>(keys: &'a [IndexKey], out: &mut Vec<Show<'a>>) {
    out.push(Text("("));
    let mut sep = "";
    for k in keys {
        match k {
            IndexKey::In { name, set } => {
                out.extend([Text(sep), Text("(in "), Text(name), Text(" ")]);
                out.extend([Show::Expr(set), Text(")")]);
            }
            IndexKey::At(e) => out.extend([Text(sep), Text("(at "), Show::Expr(e), Text(")")]),
        }
        sep = " ";
    }
    out.push(Text(")"));
}

/// ` (with (= x e) (= x ((at k)) e))` for boundary values, nothing for none.
fn boundary_items<'a>(items: &'a [BoundaryItem], out: &mut Vec<Show<'a>>) {
    if items.is_empty() {
        return;
    }
    out.push(Text(" (with"));
    for b in items {
        out.extend([Text(" (= "), Text(&b.name), Text(" ")]);
        if !b.keys.is_empty() {
            keys(&b.keys, out);
            out.push(Text(" "));
        }
        out.extend([Show::Expr(&b.value), Text(")")]);
    }
    out.push(Text(")"));
}

fn params_spaced<'a>(params: &'a [Param], out: &mut Vec<Show<'a>>) {
    let mut sep = "";
    for p in params {
        out.extend([Text(sep), Show::Param(p)]);
        sep = " ";
    }
}

/// `(= (a b) e)`, `(= (_) e)`, `(return a b)`, `(<- p e)`, a function
/// `(def f (x (y: int)) (-> (stdout: Lines)) = e (test (a b) …))`, the `=` for an equation,
/// a method `(method T.m (k) = e)`, or `(method T.m = e)` without parentheses, a struct
/// `(struct P (x: f64) (y: f64 = 0.0) (import a.B))`, a type `(type T (A) (| A #b))`, an import
/// `(import a.b)`, `(import a.b as c)` or `(import a.b (x y) @hash(…))`, and an annotated
/// declaration `(annotated @log (@cost n (k: 1)) (def …))`, a bare annotation without
/// parentheses; from layer L6, a binding with boundary values
/// `(= (x') e (with (= x 0)))`, `(mutable (= (c) e))`, an indexed definition
/// `(indexed x ((in i s) (at k)) e (with (= x ((at -1)) 0)))`, `(while c)`, `(until c)`, and an
/// expression statement `(do e)`.
fn stmt<'a>(s: &'a Stmt, out: &mut Vec<Show<'a>>) {
    match &s.kind {
        StmtKind::Bind {
            targets,
            value,
            boundary,
        } => {
            out.push(Text("(= ("));
            let mut sep = "";
            for t in targets {
                out.extend([Text(sep), Text(target(t))]);
                sep = " ";
            }
            out.extend([Text(") "), Show::Expr(value)]);
            boundary_items(boundary, out);
            out.push(Text(")"));
        }
        StmtKind::Mutable(decl) => out.extend([Text("(mutable "), Show::Stmt(decl), Text(")")]),
        StmtKind::IndexedDef(d) => {
            out.extend([Text("(indexed "), Text(&d.name), Text(" ")]);
            keys(&d.keys, out);
            out.extend([Text(" "), Show::Expr(&d.value)]);
            boundary_items(&d.boundary, out);
            out.push(Text(")"));
        }
        StmtKind::While(c) => out.extend([Text("(while "), Show::Expr(c), Text(")")]),
        StmtKind::Until(c) => out.extend([Text("(until "), Show::Expr(c), Text(")")]),
        StmtKind::Expr(e) => out.extend([Text("(do "), Show::Expr(e), Text(")")]),
        StmtKind::Return(es) => {
            out.push(Text("(return"));
            each(out, es, Show::Expr);
            out.push(Text(")"));
        }
        StmtKind::Push { port, value } => out.extend([
            Text("(<- "),
            Text(port),
            Text(" "),
            Show::Expr(value),
            Text(")"),
        ]),
        StmtKind::Function(func) => {
            out.extend([Text("(def "), Text(&func.name), Text(" (")]);
            params_spaced(&func.params, out);
            out.push(Text(")"));
            function(func, out);
        }
        StmtKind::Method(m) => {
            let func = &m.function;
            out.extend([
                Text("(method "),
                Text(&m.receiver),
                Text("."),
                Text(&func.name),
            ]);
            if m.called {
                out.push(Text(" ("));
                params_spaced(&func.params, out);
                out.push(Text(")"));
            }
            function(func, out);
        }
        StmtKind::Struct(st) => {
            out.extend([Text("(struct "), Text(&st.name)]);
            for f in &st.fields {
                match f {
                    Field::Typed {
                        name, ty, default, ..
                    } => {
                        out.extend([Text(" ("), Text(name), Text(": "), Show::Type(ty)]);
                        if let Some(d) = default {
                            out.extend([Text(" = "), Show::Expr(d)]);
                        }
                        out.push(Text(")"));
                    }
                    Field::Import { path, .. } => {
                        out.extend([Text(" (import "), Text(path), Text(")")]);
                    }
                }
            }
            out.push(Text(")"));
        }
        StmtKind::Type(t) => {
            out.extend([Text("(type "), Text(&t.name)]);
            if !t.params.is_empty() {
                out.push(Text(" ("));
                let mut sep = "";
                for p in &t.params {
                    out.extend([Text(sep), Text(p)]);
                    sep = " ";
                }
                out.push(Text(")"));
            }
            out.extend([Text(" "), Show::Type(&t.ty), Text(")")]);
        }
        StmtKind::Import(i) => {
            out.extend([Text("(import "), Text(&i.path)]);
            match &i.kind {
                ImportKind::Qualified => {}
                ImportKind::Alias(a) => out.extend([Text(" as "), Text(a)]),
                ImportKind::Selective(names) => {
                    out.push(Text(" ("));
                    let mut sep = "";
                    for n in names {
                        out.extend([Text(sep), Text(n)]);
                        sep = " ";
                    }
                    out.push(Text(")"));
                }
            }
            if let Some(pin) = &i.pin {
                out.push(Show::Owned(format!(" @hash({pin})")));
            }
            out.push(Text(")"));
        }
        StmtKind::Annotated { annots, decl } => {
            out.push(Text("(annotated"));
            for a in annots {
                annot(a, out);
            }
            out.extend([Text(" "), Show::Stmt(decl), Text(")")]);
        }
        StmtKind::UnitAnnot(a) => {
            out.push(Text("(unit"));
            annot(a, out);
            out.push(Text(")"));
        }
    }
}

/// The annotation `a`, after a space: `@name`, or `(@name args)` when parentheses follow it.
fn annot<'a>(a: &'a Annot, out: &mut Vec<Show<'a>>) {
    if !a.called {
        out.extend([Text(" @"), Text(&a.name)]);
        return;
    }
    out.extend([Text(" (@"), Text(&a.name)]);
    each(out, &a.positional, Show::Expr);
    for (n, e) in &a.named {
        out.extend([Text(" ("), Text(n), Text(": "), Show::Expr(e), Text(")")]);
    }
    out.push(Text(")"));
}

/// The rest of a function after its parameters: its ports, body and tests, and the `)`.
fn function<'a>(func: &'a Function, out: &mut Vec<Show<'a>>) {
    if let Some(ports) = &func.ports {
        out.push(Text(" (->"));
        for p in ports {
            out.extend([
                Text(" ("),
                Text(&p.name),
                Text(": "),
                Show::Type(&p.ty),
                Text(")"),
            ]);
        }
        out.push(Text(")"));
    }
    out.extend([
        Text(if func.equation { " = " } else { " " }),
        Show::Expr(&func.body),
    ]);
    if !func.tests.is_empty() {
        out.push(Text(" (test"));
        for (a, b) in &func.tests {
            out.extend([
                Text(" ("),
                Show::Expr(a),
                Text(" "),
                Show::Expr(b),
                Text(")"),
            ]);
        }
        out.push(Text(")"));
    }
    out.push(Text(")"));
}

/// `int`, `#none`, `(tuple A B)`, `(| A B)`, `(& A B)`, `(\ A B)`, `(-> (A (x: B)) R)`,
/// `(Tree T)`, `(#node (l: T))`, `(record (x: int))`, `(array T)`.
fn ty<'a>(t: &'a Type, out: &mut Vec<Show<'a>>) {
    let mut list = |head, ts: &'a [Type]| {
        out.push(Text(head));
        each(out, ts, Show::Type);
        out.push(Text(")"));
    };
    match &t.kind {
        TypeKind::Name(n) => out.push(Text(n)),
        TypeKind::Atom(a) => out.extend([Text("#"), Text(a)]),
        TypeKind::Tuple(ts) => list("(tuple", ts),
        TypeKind::Union(ts) => list("(|", ts),
        TypeKind::And(ts) => list("(&", ts),
        TypeKind::Diff(a, b) => out.extend([
            Text("(\\ "),
            Show::Type(a),
            Text(" "),
            Show::Type(b),
            Text(")"),
        ]),
        TypeKind::Arrow {
            params,
            partial,
            result,
        } => {
            out.push(Text(if *partial { "(->? (" } else { "(-> (" }));
            type_params(params, "", out);
            out.extend([Text(") "), Show::Type(result), Text(")")]);
        }
        TypeKind::Bounded {
            lower,
            upper,
            result,
        } => out.extend([
            Text("(.. "),
            Show::Type(lower),
            Text(" "),
            Show::Type(upper),
            Text(" "),
            Show::Type(result),
            Text(")"),
        ]),
        TypeKind::Apply(name, params) => {
            out.extend([Text("("), Text(name)]);
            type_params(params, " ", out);
            out.push(Text(")"));
        }
        TypeKind::AtomApply(name, params) => {
            out.extend([Text("(#"), Text(name)]);
            type_params(params, " ", out);
            out.push(Text(")"));
        }
        TypeKind::Array(t) => out.extend([Text("(array "), Show::Type(t), Text(")")]),
        TypeKind::Record(fields) => {
            out.push(Text("(record"));
            for (n, t) in fields {
                out.extend([Text(" ("), Text(n), Text(": "), Show::Type(t), Text(")")]);
            }
            out.push(Text(")"));
        }
    }
}

/// The parameters of a function type or the arguments of an applied type, each after `first`
/// or a space.
fn type_params<'a>(params: &'a [TypeParam], first: &'a str, out: &mut Vec<Show<'a>>) {
    let mut sep = first;
    for p in params {
        out.push(Text(sep));
        sep = " ";
        match (&p.name, p.positional) {
            (Some(n), true) => out.extend([
                Text("(positional "),
                Text(n),
                Text(": "),
                Show::Type(&p.ty),
                Text(")"),
            ]),
            (Some(n), false) => {
                out.extend([Text("("), Text(n), Text(": "), Show::Type(&p.ty), Text(")")])
            }
            (None, _) => out.push(Show::Type(&p.ty)),
        }
    }
}

/// `x`, or `(positional x: int = 0)` with what is written.
fn param<'a>(p: &'a Param, out: &mut Vec<Show<'a>>) {
    // A tuple-destructuring parameter is positional by its form, and its name is `(a, b)`.
    let positional = p.positional && p.tuple.is_none();
    if !positional && p.ty.is_none() && p.default.is_none() {
        out.push(Text(&p.name));
        return;
    }
    out.push(Text("("));
    if positional {
        out.push(Text("positional "));
    }
    out.push(Text(&p.name));
    if let Some(t) = &p.ty {
        out.extend([Text(": "), Show::Type(t)]);
    }
    if let Some(d) = &p.default {
        out.extend([Text(" = "), Show::Expr(d)]);
    }
    out.push(Text(")"));
}

/// `#name`, `#name(f: p, g:)`, `#name(p, q)`, `Point(x:, y: b)`, `n`, `_`, `(p, q)` as written;
/// a type pattern `(is n T)` or `(is T)`, a literal as an expression is shown, and a range
/// pattern `(..< 0 10)` or `(.. 0)`.
fn pattern<'a>(p: &'a Pattern, out: &mut Vec<Show<'a>>) {
    let (fields, items) = match p {
        Pattern::Atom {
            name,
            fields,
            items,
            ..
        } => {
            out.extend([Text("#"), Text(name)]);
            if fields.is_empty() && items.is_empty() {
                return;
            }
            (&fields[..], &items[..])
        }
        Pattern::Struct { name, fields, .. } => {
            out.push(Text(name));
            (&fields[..], &[][..])
        }
        Pattern::Name(n, _) => return out.push(Text(n)),
        Pattern::Wild(_) => return out.push(Text("_")),
        Pattern::Tuple(items, _) => (&[][..], &items[..]),
        Pattern::Is { name, ty, .. } => {
            out.push(Text("(is "));
            if let Some(n) = name {
                out.extend([Text(n), Text(" ")]);
            }
            return out.extend([Show::Type(ty), Text(")")]);
        }
        Pattern::Lit(e) => return out.push(Show::Expr(e)),
        Pattern::Range { from, to, .. } => {
            out.extend([Text("("), Text(to.op()), Text(" "), Show::Pattern(from)]);
            if let Some(b) = to.bound() {
                out.extend([Text(" "), Show::Pattern(b)]);
            }
            return out.push(Text(")"));
        }
    };
    out.push(Text("("));
    let mut sep = "";
    for (n, p) in fields {
        out.extend([Text(sep), Text(n)]);
        match p {
            Some(p) => out.extend([Text(": "), Show::Pattern(p)]),
            None => out.push(Text(":")),
        }
        sep = ", ";
    }
    for p in items {
        out.extend([Text(sep), Show::Pattern(p)]);
        sep = ", ";
    }
    out.push(Text(")"));
}

macro_rules! shown {
    ($($t:ident)*) => {
        $(impl fmt::Display for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write(f, Show::$t(self))
            }
        })*
    };
}

shown!(Expr Stmt Type Param Pattern);

/// The same text as `Display`: a derived `Debug` would recurse.
macro_rules! debug_as_shown {
    ($($t:ident)*) => {
        $(impl fmt::Debug for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(self, f)
            }
        })*
    };
}

debug_as_shown!(Expr Type Pattern);
