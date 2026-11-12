//! The `initial` statement (DESIGN.md sec:generations, step L6.1a): where it may stand, which
//! names it may give a value, what its value may read, and one sentinel value for each
//! variable. Each check is one of the rows of sec:diagnostics: "An `initial` statement outside
//! a loop, or under `local`", "An `initial` statement for a name the loop does not update",
//! "An `initial` value that reads a name of its own loop", "Two sentinel values for one
//! variable", and, for an entry written as a bare statement, "A boundary entry of a loop
//! written without `initial`". The forms the parser stops at, `with x = e`, `with initial x =
//! e` and `with x[-2] = e` on a statement of a loop, are found by the parser
//! (`crate::parse`).

use std::collections::HashSet;

use num_bigint::BigInt;

use super::builder::Builder;
use super::sentinel::{End, Entry, Keys, Sentinels, keys_of};
use super::{
    Error, Expr, ExprKind, Field, IndexKey, Initial, Note, Pattern, RangeEnd, Stmt, StmtKind,
    StrPart, Target,
};
use crate::lex::Span;
use zedc_base::rejection::Row;

/// The `initial` statement `s` is, through the annotations written before it.
fn initial_of(mut s: &Stmt) -> Option<&Initial> {
    loop {
        match &s.kind {
            StmtKind::Initial(i) => return Some(i),
            StmtKind::Annotated { decl, .. } => s = decl,
            _ => return None,
        }
    }
}

/// The declaration under the `local`, `mutable` and annotations that wrap `s`, and whether a
/// `local` and a `mutable` wrap it.
fn unwrapped(mut s: &Stmt) -> (&Stmt, bool, bool) {
    let (mut local, mut mutable) = (false, false);
    loop {
        match &s.kind {
            StmtKind::Local(d) => {
                local = true;
                s = d;
            }
            StmtKind::Mutable(d) => {
                mutable = true;
                s = d;
            }
            StmtKind::Annotated { decl, .. } => s = decl,
            _ => return (s, local, mutable),
        }
    }
}

/// `x` for `x'`, and `x` itself for a name with no prime.
fn unprimed(name: &str) -> &str {
    name.strip_suffix('\'').unwrap_or(name)
}

/// Whether `e` is a negative integer literal, `-2`.
fn negative_literal(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Unary("-", x) if matches!(x.kind, ExprKind::Int { .. }))
}

/// Whether the key `k` lies below index 0 by its text: `-2`, or `i in -3..<0`.
fn below_zero(k: &IndexKey) -> bool {
    match k {
        IndexKey::At(e) => negative_literal(e),
        IndexKey::In { set, .. } => {
            matches!(&set.kind, ExprKind::Range(lo, _) if negative_literal(lo))
        }
    }
}

/// The entries each sentinel site among `stmts` gives, in written order: `mutable x = e;`,
/// `initial x = e;` and `initial a, b = e;` give the frame `x[-1]` of each name, and an
/// `initial` statement with keys the entries its keys give. A site whose literal range holds
/// no key, `initial x[i in -1..<-1] = 0;`, gives none.
fn entries_of<'s>(stmts: &'s [Stmt]) -> Vec<Entry<'s>> {
    let mut out = Vec::new();
    for (stmt, s) in stmts.iter().enumerate() {
        let (d, _, is_mutable) = unwrapped(s);
        let frame = |name: &'s str| Entry {
            name,
            line: None,
            lo: BigInt::from(-1),
            end: End::At(BigInt::from(-1)),
            inner: Vec::new(),
            stmt,
        };
        if is_mutable && let StmtKind::Bind { targets, .. } = &d.kind {
            for t in targets {
                if let Target::Name(n, _) = t {
                    out.push(frame(n));
                }
            }
        }
        let Some(i) = initial_of(d) else {
            continue;
        };
        let Some((first, later)) = i.keys.split_first() else {
            out.extend(i.names.iter().map(|(n, _)| frame(n)));
            continue;
        };
        let Some(first) = keys_of(first) else {
            continue;
        };
        let Some(inner) = later.iter().map(keys_of).collect::<Option<Vec<_>>>() else {
            continue;
        };
        let (line, lo, end) = match first {
            Keys::Ints(lo, end) => (None, lo, end),
            Keys::Written(k) => (Some(k), BigInt::ZERO, End::At(BigInt::ZERO)),
        };
        out.push(Entry {
            name: &i.names[0].0,
            line,
            lo,
            end,
            inner,
            stmt,
        });
    }
    out
}

/// The names a pattern binds, added to `out`.
fn pattern_names<'e>(p: &'e Pattern, out: &mut HashSet<&'e str>) {
    let mut stack = vec![p];
    while let Some(p) = stack.pop() {
        match p {
            Pattern::Name(n, _) => {
                out.insert(n);
            }
            Pattern::Is { name, .. } => out.extend(name.as_deref()),
            Pattern::Struct { fields, .. } => {
                for (f, p) in fields {
                    match p {
                        Some(p) => stack.push(p),
                        None => {
                            out.insert(f);
                        }
                    }
                }
            }
            Pattern::Atom { fields, items, .. } => {
                stack.extend(items);
                for (f, p) in fields {
                    match p {
                        Some(p) => stack.push(p),
                        None => {
                            out.insert(f);
                        }
                    }
                }
            }
            Pattern::Tuple(items, _) => stack.extend(items),
            Pattern::Wild(_) | Pattern::Lit(_) | Pattern::Range { .. } => {}
        }
    }
}

/// A sentinel site, an `initial` statement or a `mutable` declaration: the target of each
/// component, `None` for `_`, with its span; the value; and the value's parts when it is a
/// tuple written out with one part for each of several targets.
struct Site<'s> {
    targets: Vec<Option<(&'s str, Span)>>,
    value: &'s Expr,
    parts: Option<&'s [Expr]>,
}

/// What a walk of expressions finds: the names read, each with its span, in the order met; the
/// names bound inside the walked code; and the receivers of `x*.m` calls.
#[derive(Default)]
struct Found<'e> {
    reads: Vec<(&'e str, Span)>,
    bound: HashSet<&'e str>,
    spread: Vec<&'e str>,
}

/// Walks `roots` and the statements `stmts`, without entering the body of a nested `loop`,
/// whose names are its own. One visit of each node, by a work list, so the depth of the code
/// costs no stack.
fn walk<'e>(roots: &[&'e Expr], stmts: &'e [Stmt]) -> Found<'e> {
    let mut found = Found::default();
    let mut exprs: Vec<&'e Expr> = roots.to_vec();
    let mut todo: Vec<&'e Stmt> = stmts.iter().collect();
    loop {
        if let Some(s) = todo.pop() {
            stmt_kids(s, &mut exprs, &mut todo, &mut found.bound);
            continue;
        }
        let Some(e) = exprs.pop() else {
            return found;
        };
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_)
            | ExprKind::This
            | ExprKind::Section(_)
            | ExprKind::Loop { .. } => {}
            ExprKind::Name(n) => found.reads.push((n, e.span)),
            ExprKind::Str(parts) => exprs.extend(parts.iter().filter_map(|p| match p {
                StrPart::Hole(e) => Some(e),
                StrPart::Text(_) => None,
            })),
            ExprKind::Spread { of, .. } => {
                if let ExprKind::Name(n) = &of.kind {
                    found.spread.push(unprimed(n));
                }
                exprs.push(of);
            }
            ExprKind::Unary(_, a)
            | ExprKind::Is { of: a, .. }
            | ExprKind::Member { of: a, .. }
            | ExprKind::Read { of: a, .. }
            | ExprKind::Break(a) => exprs.push(a),
            ExprKind::SortKey { key, .. } => exprs.extend(key.as_deref()),
            ExprKind::Binary(_, a, b)
            | ExprKind::Index(a, b)
            | ExprKind::In { of: a, set: b, .. }
            | ExprKind::Reduce { of: a, op: b } => exprs.extend([&**a, &**b]),
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                if let Some(p) = pattern {
                    pattern_names(p, &mut found.bound);
                }
                exprs.extend([&**of, &**default]);
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                exprs.push(callee);
                exprs.extend(positional);
                exprs.extend(named.iter().map(|(_, e)| e));
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => exprs.extend(es),
            ExprKind::Map(entries) => {
                for (k, v) in entries {
                    exprs.extend([k, v]);
                }
            }
            ExprKind::Range(from, to) => {
                exprs.push(from);
                match to {
                    RangeEnd::Below(b) | RangeEnd::Through(b) => exprs.push(b),
                    RangeEnd::Open => {}
                }
            }
            ExprKind::For {
                binders,
                source,
                guard,
                body,
            } => {
                for t in binders {
                    if let Target::Name(n, _) = t {
                        found.bound.insert(n);
                    }
                }
                exprs.push(source);
                exprs.extend(guard.as_deref());
                exprs.push(body);
            }
            ExprKind::Lambda { params, body } => {
                for p in params {
                    found.bound.insert(&p.name);
                    for t in p.tuple.iter().flatten() {
                        if let Target::Name(n, _) = t {
                            found.bound.insert(n);
                        }
                    }
                    exprs.extend(p.default.as_ref());
                }
                exprs.push(body);
            }
            ExprKind::Block(stmts) => todo.extend(stmts),
            ExprKind::Match { of, arms } => {
                exprs.push(of);
                for a in arms {
                    pattern_names(&a.pattern, &mut found.bound);
                    exprs.extend(a.guard.as_ref());
                    exprs.push(&a.body);
                }
            }
            ExprKind::Record(fields) => exprs.extend(fields.iter().map(|(_, e)| e)),
            ExprKind::With { of, updates } => {
                exprs.push(of);
                exprs.extend(updates.iter().map(|u| &u.value));
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => exprs.extend([&**cond, &**then, &**otherwise]),
        }
    }
}

/// Moves the expressions and statements directly in `s` to the work lists, and adds the names
/// it binds to `bound`.
fn stmt_kids<'e>(
    s: &'e Stmt,
    exprs: &mut Vec<&'e Expr>,
    todo: &mut Vec<&'e Stmt>,
    bound: &mut HashSet<&'e str>,
) {
    let keys = |keys: &'e [IndexKey], exprs: &mut Vec<&'e Expr>, bound: &mut HashSet<&'e str>| {
        for k in keys {
            match k {
                IndexKey::In { name, set } => {
                    bound.insert(name);
                    exprs.push(set);
                }
                IndexKey::At(e) => exprs.push(e),
            }
        }
    };
    match &s.kind {
        StmtKind::Bind { targets, value } => {
            for t in targets {
                if let Target::Name(n, _) = t {
                    bound.insert(n);
                }
            }
            exprs.push(value);
        }
        StmtKind::Initial(i) => {
            bound.extend(i.names.iter().map(|(n, _)| n.as_str()));
            keys(&i.keys, exprs, bound);
            exprs.push(&i.value);
        }
        StmtKind::IndexedDef(d) => {
            bound.insert(&d.name);
            keys(&d.keys, exprs, bound);
            exprs.push(&d.value);
            for b in &d.boundary {
                keys(&b.keys, exprs, bound);
                exprs.push(&b.value);
            }
        }
        StmtKind::Push { value, .. }
        | StmtKind::While(value)
        | StmtKind::Until(value)
        | StmtKind::Expr(value) => exprs.push(value),
        StmtKind::Mutable(d) | StmtKind::Local(d) => todo.push(d),
        StmtKind::Annotated { annots, decl } => {
            for a in annots {
                exprs.extend(&a.positional);
                exprs.extend(a.named.iter().map(|(_, e)| e));
            }
            todo.push(decl);
        }
        StmtKind::UnitAnnot(a) => {
            exprs.extend(&a.positional);
            exprs.extend(a.named.iter().map(|(_, e)| e));
        }
        StmtKind::Return(es) => exprs.extend(es),
        StmtKind::Function(f) => {
            bound.insert(&f.name);
            for p in &f.params {
                bound.insert(&p.name);
                exprs.extend(p.default.as_ref());
            }
            exprs.push(&f.body);
            for (a, b) in &f.tests {
                exprs.extend([a, b]);
            }
        }
        StmtKind::Method(m) => {
            for p in &m.function.params {
                bound.insert(&p.name);
                exprs.extend(p.default.as_ref());
            }
            exprs.push(&m.function.body);
        }
        StmtKind::Struct(st) => exprs.extend(st.fields.iter().filter_map(|f| match f {
            Field::Typed { default, .. } => default.as_ref(),
            Field::Import { .. } => None,
        })),
        StmtKind::Type(_) | StmtKind::Import(_) => {}
    }
}

/// What a name of a loop is, for the message of an `initial` value that reads it.
enum LoopName {
    /// A variable the loop updates or declares `mutable`.
    Generation,
    /// A value the body defines on each step.
    StepLocal,
    /// The step index of `loop t`.
    Index,
}

impl Builder<'_, '_> {
    fn text_of(&self, span: Span) -> &str {
        &self.text[span.start..span.end]
    }

    /// The text of the `initial` statement `s` without its `initial`: `x = 0;` for `initial x =
    /// 0;`, a plain binding, or `p[-2] = -1;`, a plain indexed definition.
    fn without_initial(&self, s: &Stmt, i: &Initial) -> String {
        self.text[i.names[0].1.start..s.span.end].to_string()
    }

    /// The error for an `initial` statement among `stmts`, the statements of the block `block`
    /// in written order (`None` for the top level of a unit), that stands outside the body of a
    /// loop or under `local` (row "An `initial` statement outside a loop, or under `local`").
    /// One pass over the statements; the parent table is listed only when an `initial` statement
    /// is met.
    pub(super) fn initials_placed(
        &self,
        block: Option<usize>,
        stmts: &[Stmt],
    ) -> Result<(), Error> {
        let mut in_loop = None;
        for s in stmts {
            let (d, local, _) = unwrapped(s);
            let Some(i) = initial_of(d) else {
                continue;
            };
            if local {
                return Err(self.initial_under_local(s, i, stmts));
            }
            let inside = *in_loop.get_or_insert_with(|| {
                block.is_some_and(|n| self.parent(n).is_some_and(|p| self.tree.name(p) == "Loop"))
            });
            if !inside {
                return Err(self.initial_outside(block, s, i, stmts));
            }
        }
        Ok(())
    }

    fn initial_outside(
        &self,
        block: Option<usize>,
        s: &Stmt,
        i: &Initial,
        stmts: &[Stmt],
    ) -> Error {
        let written = self.text_of(s.span);
        let name = &i.names[0].0;
        let mut notes = Vec::new();
        let place = match block {
            None => "at the top level of the unit".to_string(),
            Some(n) => {
                let span = self.span(n);
                let mut p = self.parent(n);
                while let Some(k) = p.filter(|&k| self.tree.name(k) != "Loop") {
                    p = self.parent(k);
                }
                match p {
                    Some(l) => {
                        notes.push(Note {
                            span,
                            text: "the block it stands in, inside the body of the loop".into(),
                        });
                        notes.push(Note {
                            span: self.span(l),
                            text: "the loop, whose body's own statements may include it".into(),
                        });
                        "in a block inside the body of a `loop`, not among the statements of \
                         the loop's body itself"
                            .to_string()
                    }
                    None => {
                        notes.push(Note {
                            span,
                            text: "the block it stands in, which is not the body of a `loop`"
                                .into(),
                        });
                        "in a block that is not the body of a `loop`".to_string()
                    }
                }
            }
        };
        let plain = self.without_initial(s, i);
        let repair = if i.keys.is_empty() {
            format!("repair: `{plain}`, a plain binding")
        } else {
            let entry = self.text[i.names[0].1.start..i.value.span.end].to_string();
            let def = stmts.iter().find_map(|t| match &unwrapped(t).0.kind {
                StmtKind::IndexedDef(d) if d.name == *name => Some((t, d)),
                _ => None,
            });
            match def {
                Some((t, d)) => {
                    let head = self.text_of(t.span).trim_end_matches(';').trim_end();
                    let joint = if d.boundary.is_empty() { " with" } else { "," };
                    format!(
                        "repair: `{head}{joint} {entry};`, the entry given with its key in the \
                         `with` clause of the definition of `{name}`, and `{written}` deleted"
                    )
                }
                None => format!("repair: `{plain}`, a plain definition of the entry"),
            }
        };
        notes.push(Note {
            span: s.span,
            text: repair,
        });
        Error {
            row: Some(Row::InitialOutsideLoop),
            menu: String::new(),
            span: s.span,
            message: format!(
                "`{written}` stands {place}. An `initial` statement gives the value of `{name}` \
                 before step 0 of a loop that updates `{name}`, so it is written among the \
                 statements of that loop's body, and it has no meaning where no loop updates \
                 `{name}`."
            ),
            notes,
        }
    }

    fn initial_under_local(&self, s: &Stmt, i: &Initial, stmts: &[Stmt]) -> Error {
        let written = self.text_of(s.span);
        let name = &i.names[0].0;
        let start = self.text_of(Span {
            start: i.names[0].1.start - "initial ".len().min(i.names[0].1.start),
            end: s.span.end,
        });
        let start = if start.starts_with("initial ") {
            start.to_string()
        } else {
            format!("initial {}", self.without_initial(s, i))
        };
        let primed = format!("{name}'");
        let update = stmts.iter().find(|t| {
            matches!(&unwrapped(t).0.kind, StmtKind::Bind { targets, .. }
                if targets.iter().any(|x| matches!(x, Target::Name(n, _) if *n == primed)))
        });
        let repair = match update {
            Some(u) if unwrapped(u).1 => format!(
                "repair: `{start}`, `local` deleted; the update `{}` already carries it",
                self.text_of(u.span)
            ),
            Some(u) => format!(
                "repair: `{start}` and `local {}`, `local` moved to the update",
                self.text_of(u.span)
            ),
            None => format!(
                "repair: `{start}`, `local` deleted, and `local` written on the update of \
                 `{name}`, `local {primed} = …;`"
            ),
        };
        Error {
            row: Some(Row::InitialOutsideLoop),
            menu: String::new(),
            span: s.span,
            message: format!(
                "`{written}` writes `local` on an `initial` statement. `local` is written on the \
                 update of `{name}`, `local {primed} = …;`, which is what keeps `{name}` out of the \
                 loop's result; an `initial` statement only gives `{name}` its value before step \
                 0, and puts nothing in the result."
            ),
            notes: vec![Note {
                span: s.span,
                text: repair,
            }],
        }
    }

    /// The checks of the `initial` statements of the body of a loop (`label` its step index,
    /// `at` its text): each names a variable the loop updates, reads no name of the loop, and
    /// gives a sentinel value no other statement or `mutable` declaration gives; and an entry
    /// below generation 0 is not written as a bare statement. One walk of the body lists what it
    /// updates and defines, then one pass over its statements, which checks the entries each
    /// site gives against those of the sites before it by the values of their keys
    /// (`Sentinels`): O(n + k log k) for a body of n nodes and k sites, where comparing each
    /// pair of sites would be O(k^2).
    pub(super) fn loop_initials(
        &self,
        label: Option<&str>,
        at: Span,
        body: &Expr,
    ) -> Result<(), Error> {
        let ExprKind::Block(stmts) = &body.kind else {
            return Ok(());
        };
        if !stmts.iter().any(|s| {
            let d = unwrapped(s).0;
            initial_of(d).is_some() || matches!(d.kind, StmtKind::IndexedDef(_))
        }) {
            return Ok(());
        }
        // What the body updates, declares `mutable`, and defines on each step.
        let mut updated: HashSet<&str> = HashSet::new();
        let mut mutable: HashSet<&str> = HashSet::new();
        let mut locals: HashSet<&str> = HashSet::new();
        for s in stmts {
            let (d, _, is_mutable) = unwrapped(s);
            match &d.kind {
                StmtKind::Bind { targets, .. } => {
                    for t in targets {
                        let Target::Name(n, _) = t else { continue };
                        if is_mutable {
                            mutable.insert(n);
                        } else if n.ends_with('\'') {
                            updated.insert(unprimed(n));
                        } else {
                            locals.insert(n);
                        }
                    }
                }
                StmtKind::Push { port, .. } if port.ends_with('\'') => {
                    updated.insert(unprimed(port));
                }
                // `d'[v in nodes] = …` updates `d` key by key.
                StmtKind::IndexedDef(x) if x.name.ends_with('\'') => {
                    updated.insert(unprimed(&x.name));
                }
                StmtKind::IndexedDef(x) => {
                    locals.insert(&x.name);
                }
                StmtKind::Function(f) => {
                    locals.insert(&f.name);
                }
                _ => {}
            }
        }
        updated.extend(walk(&[], stmts).spread);
        let generation = |n: &str| updated.contains(n) || mutable.contains(n);
        // The entries each site gives, compared by the values of their keys.
        let mut sentinels = Sentinels::new(entries_of(stmts));
        let mut next = 0;
        for (k, s) in stmts.iter().enumerate() {
            let d = unwrapped(s).0;
            if let StmtKind::IndexedDef(x) = &d.kind
                && updated.contains(x.name.as_str())
                && x.keys.iter().all(below_zero)
            {
                return Err(self.bare_entry(s, &x.name, at));
            }
            if let Some(i) = initial_of(d) {
                for (n, _) in &i.names {
                    if !generation(n) {
                        return Err(self.not_updated(s, n, at));
                    }
                }
                let found = walk(&[&i.value], &[]);
                for &(n, span) in &found.reads {
                    if found.bound.contains(n) {
                        continue;
                    }
                    let base = unprimed(n);
                    let what = if Some(n) == label {
                        LoopName::Index
                    } else if generation(base) {
                        LoopName::Generation
                    } else if locals.contains(n) {
                        LoopName::StepLocal
                    } else {
                        continue;
                    };
                    return Err(self.reads_loop(s, i, n, span, what, stmts, at));
                }
            }
            while sentinels.entries().get(next).is_some_and(|e| e.stmt == k) {
                if let Some(first) = sentinels.check(next) {
                    let (a, b) = (&sentinels.entries()[first], &sentinels.entries()[next]);
                    return Err(self.two_sentinels(a, b, stmts));
                }
                next += 1;
            }
        }
        Ok(())
    }

    /// Row "A boundary entry of a loop written without `initial`", for the bare statement `s`
    /// that defines an entry of `name` below generation 0.
    fn bare_entry(&self, s: &Stmt, name: &str, at: Span) -> Error {
        let written = self.text_of(s.span);
        Error {
            row: Some(Row::BareLoopEntry),
            menu: String::new(),
            span: s.span,
            message: format!(
                "`{written}` defines an entry of `{name}` below generation 0 in the body of a \
                 loop that updates `{name}`. An entry below generation 0 is a sentinel value, \
                 given once, before the first step, while a statement of the body without \
                 `initial` reads as a definition made on every step. Write it as an `initial` \
                 statement."
            ),
            notes: vec![
                Note {
                    span: at,
                    text: format!("the loop, which updates `{name}`"),
                },
                Note {
                    span: s.span,
                    text: format!(
                        "repair: `initial {written}`, the entry given once, before the first step"
                    ),
                },
            ],
        }
    }

    /// Row "An `initial` statement for a name the loop does not update".
    fn not_updated(&self, s: &Stmt, name: &str, at: Span) -> Error {
        let written = self.text_of(s.span);
        let value = initial_of(unwrapped(s).0).map_or("…", |i| self.text_of(i.value.span));
        Error {
            row: Some(Row::InitialNotUpdated),
            menu: String::new(),
            span: s.span,
            message: format!(
                "`{written}` gives `{name}` a value before step 0, and no statement of this loop \
                 updates `{name}`: none writes `{name}' = …`, `{name}' <- e` or `{name}*.m(…)`. An \
                 `initial` statement gives a value before the first step only, so `{name}` would \
                 have no value at any later step."
            ),
            notes: vec![
                Note {
                    span: at,
                    text: format!("the loop, none of whose statements updates `{name}`"),
                },
                Note {
                    span: s.span,
                    text: format!(
                        "repair: add the update the loop is meant to make, `{name}' = …;`, to \
                         its body"
                    ),
                },
                Note {
                    span: s.span,
                    text: format!(
                        "repair: `mutable {name} = {value};` in place of `{written}`, for a \
                         variable that keeps its value at a step that does not assign it"
                    ),
                },
                Note {
                    span: at,
                    text: format!(
                        "repair: `{name} = {value};` written before the loop, and `{written}` \
                         deleted, for a value that does not change"
                    ),
                },
            ],
        }
    }

    /// Row "An `initial` value that reads a name of its own loop", for the read of `n` at
    /// `span` in the value of the `initial` statement `s`.
    #[allow(clippy::too_many_arguments)]
    fn reads_loop(
        &self,
        s: &Stmt,
        i: &Initial,
        n: &str,
        span: Span,
        what: LoopName,
        stmts: &[Stmt],
        at: Span,
    ) -> Error {
        let written = self.text_of(s.span);
        let name = &i.names[0].0;
        let base = unprimed(n);
        let what: String = match what {
            LoopName::Generation => "a variable the loop updates".into(),
            LoopName::StepLocal => "a value the loop's body defines on each step".into(),
            LoopName::Index => "the step index of the loop".into(),
        };
        let mut notes = vec![
            Note {
                span,
                text: format!("the read of `{n}`, {what}"),
            },
            Note {
                span: at,
                text: "the loop".into(),
            },
            Note {
                span: s.span,
                text: format!(
                    "repair: compute the start value before the loop, `{name}0 = …;` above it, \
                     and write `initial {name} = {name}0;`"
                ),
            },
        ];
        // The start value of the variable read, when an `initial` statement or a `mutable`
        // declaration of this body gives one, written in place of the read.
        let start = stmts.iter().find_map(|t| {
            let (d, _, m) = unwrapped(t);
            match &d.kind {
                StmtKind::Initial(j) if j.keys.is_empty() && j.names.len() == 1 => {
                    (j.names[0].0 == base).then_some(&j.value)
                }
                StmtKind::Bind { targets, value } if m && targets.len() == 1 => {
                    matches!(&targets[0], Target::Name(x, _) if x == base).then_some(value)
                }
                _ => None,
            }
        });
        if let Some(v) = start.filter(|v| walk(&[v], &[]).reads.is_empty()) {
            let v = self.text_of(v.span);
            let value = &self.text[i.value.span.start..span.start];
            let rest = &self.text[span.end..i.value.span.end];
            notes.push(Note {
                span: s.span,
                text: format!(
                    "repair: `{}{value}{v}{rest};`, the start value of `{base}` written in place \
                     of `{n}`",
                    &self.text[s.span.start..i.value.span.start]
                ),
            });
        }
        Error {
            row: Some(Row::InitialReadsLoop),
            menu: String::new(),
            span,
            message: format!(
                "the value of `{written}` reads `{n}`, {what}. The value of an `initial` \
                 statement is computed once, before the first step, when no name of the loop has \
                 a value yet, so it reads only names given a value before the loop."
            ),
            notes,
        }
    }

    /// The sentinel site `s`, an `initial` statement or a `mutable` declaration, read as a
    /// [`Site`].
    fn site<'s>(&self, s: &'s Stmt) -> Site<'s> {
        let d = unwrapped(s).0;
        let (targets, value): (Vec<Option<(&str, Span)>>, &Expr) = match (initial_of(d), &d.kind) {
            (Some(i), _) => (
                i.names
                    .iter()
                    .map(|(n, sp)| Some((n.as_str(), *sp)))
                    .collect(),
                &i.value,
            ),
            (None, StmtKind::Bind { targets, value }) => (
                targets
                    .iter()
                    .map(|t| match t {
                        Target::Name(n, sp) => Some((n.as_str(), *sp)),
                        Target::Wild => None,
                    })
                    .collect(),
                value,
            ),
            _ => {
                unreachable!("a sentinel site is an `initial` statement or a `mutable` declaration")
            }
        };
        let parts = match &value.kind {
            ExprKind::Tuple(es) if targets.len() > 1 && es.len() == targets.len() => Some(&es[..]),
            _ => None,
        };
        Site {
            targets,
            value,
            parts,
        }
    }

    /// The span of the value the site `s` gives `name` alone: the whole value for one target,
    /// the part for `name` when the value is a tuple written out, and none otherwise.
    fn value_for(&self, s: &Stmt, name: &str) -> Option<Span> {
        let Site {
            targets,
            value,
            parts,
        } = self.site(s);
        if targets.len() == 1 {
            return Some(value.span);
        }
        let k = targets
            .iter()
            .position(|t| t.is_some_and(|(n, _)| n == name))?;
        parts.map(|ps| ps[k].span)
    }

    /// What the site `s` gives `name`, as the note on the site says it: `` `x` the value `0` ``;
    /// for an entry written with its keys, the entry as written, `` `x[i in -3..<0]` the value
    /// `0` ``; or, for several targets whose value is not written out as a tuple, `` `a, b` the
    /// value `f(0)` ``.
    fn gives(&self, s: &Stmt, name: &str) -> String {
        if let Some(i) = initial_of(unwrapped(s).0)
            && !i.keys.is_empty()
        {
            return format!(
                "`{}` the value `{}`",
                self.entry_written(i),
                self.text_of(i.value.span)
            );
        }
        match self.value_for(s, name) {
            Some(v) => format!("`{name}` the value `{}`", self.text_of(v)),
            None => {
                let Site { targets, value, .. } = self.site(s);
                let names: Vec<&str> = targets.iter().map(|t| t.map_or("_", |(n, _)| n)).collect();
                format!(
                    "`{}` the value `{}`",
                    names.join(", "),
                    self.text_of(value.span)
                )
            }
        }
    }

    /// The repair that takes `name` out of the site `s`, called `this` in its text ("this
    /// one", "the first"): the whole statement deleted when `name` is its one target, the
    /// statement rewritten without `name` when its value is a tuple written out, and otherwise
    /// the statement without `name` with `…` for the value of the other targets.
    fn drop_name(&self, s: &Stmt, name: &str, this: &str) -> String {
        let whole = self.text_of(s.span);
        let Site {
            targets,
            value,
            parts,
        } = self.site(s);
        if targets.len() == 1 {
            return format!("delete {this}, `{whole}`");
        }
        let Some((_, first)) = targets.iter().flatten().next() else {
            unreachable!("a site with no name gives no sentinel value");
        };
        let head = &self.text[s.span.start..first.start];
        let rest: Vec<(&str, Option<&Expr>)> = targets
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.is_some_and(|(n, _)| n == name))
            .map(|(k, t)| (t.map_or("_", |(n, _)| n), parts.map(|ps| &ps[k])))
            .collect();
        let names: Vec<&str> = rest.iter().map(|r| r.0).collect();
        let names = names.join(", ");
        // A declared type stands between the targets and the value: the rewriting keeps it only
        // by copying, which a rewritten target list cannot do, so it is not offered.
        let typed = self.text[first.start..value.span.start].contains(':');
        match parts {
            Some(_) if !typed => {
                let vals: Vec<&str> = rest
                    .iter()
                    .filter_map(|r| r.1.map(|e| self.text_of(e.span)))
                    .collect();
                let v = if vals.len() == 1 {
                    vals[0].to_string()
                } else {
                    format!("({})", vals.join(", "))
                };
                format!("write {this} without `{name}`: `{head}{names} = {v};`")
            }
            _ => format!(
                "write {this} without `{name}`: `{head}{names} = …;`, with the value of `{names}` \
                 alone in place of `…`"
            ),
        }
    }

    /// The entry an `initial` statement with keys gives, as written: `x[i in -3..<0]`.
    fn entry_written(&self, i: &Initial) -> &str {
        self.text[i.names[0].1.start..i.value.span.start]
            .trim_end()
            .trim_end_matches('=')
            .trim_end()
    }

    /// The brackets after the first of the entry an `initial` statement gives, as written:
    /// `[j in 0..<2]` for `initial g[-1][j in 0..<2] = j;`. One scan of the entry's text,
    /// counting brackets.
    fn later_brackets(&self, i: &Initial) -> &str {
        let entry = &self.entry_written(i)[i.names[0].0.len()..];
        let mut depth = 0usize;
        for (k, c) in entry.char_indices() {
            match c {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        return entry[k + 1..].trim_start();
                    }
                }
                _ => {}
            }
        }
        ""
    }

    /// The first key of an `initial` statement with keys, as written: `-2`, or `i in -3..<0`.
    fn first_key(&self, i: &Initial) -> String {
        match &i.keys[0] {
            IndexKey::At(e) => self.text_of(e.span).to_string(),
            IndexKey::In { name, set } => format!("{name} in {}", self.text_of(set.span)),
        }
    }

    /// The entries the sites `a` and `b` both give, as the message names them: `` the entry
    /// `x[-2]` ``, `` the entries `x[-3]` to `x[-1]` ``, `` the entries from `x[-3]` up ``; with
    /// later brackets, those written on the site that has them, `` the entries `g[-1][j in
    /// 0..<2]` ``.
    fn shared(&self, a: &Entry, b: &Entry, stmts: &[Stmt]) -> String {
        let name = b.name;
        let keyed =
            |e: &Entry| initial_of(unwrapped(&stmts[e.stmt]).0).filter(|i| !i.keys.is_empty());
        // Whether a bracket gives one key.
        let single = |k: &Keys| match k {
            Keys::Ints(lo, End::At(h)) => lo == h,
            Keys::Ints(_, End::Above) => false,
            Keys::Written(k) => !k.starts_with("in "),
        };
        let word = |one: bool| if one { "entry" } else { "entries" };
        if b.line.is_some() {
            let i = keyed(b).expect("a key the text does not fix is written on an `initial`");
            let one = matches!(i.keys[0], IndexKey::At(_)) && b.inner.iter().all(single);
            return format!(
                "the {} `{name}[{}]{}`",
                word(one),
                self.first_key(i),
                self.later_brackets(i)
            );
        }
        let (later, inner_one) = [b, a]
            .into_iter()
            .find(|e| !e.inner.is_empty())
            .and_then(|e| Some((self.later_brackets(keyed(e)?), e.inner.iter().all(single))))
            .unwrap_or(("", true));
        let lo = (&a.lo).max(&b.lo);
        match (&a.end).min(&b.end) {
            End::At(h) if h == lo => format!("the {} `{name}[{lo}]{later}`", word(inner_one)),
            End::At(h) => format!("the entries `{name}[{lo}]{later}` to `{name}[{h}]{later}`"),
            End::Above => format!("the entries from `{name}[{lo}]{later}` up"),
        }
    }

    /// The repair that narrows the range of the entry `e`, written `initial x[i in lo..<hi] =
    /// v;`, to leave out the keys of `other`: the statement rewritten with the keys that are
    /// left, or two statements when they lie on both sides; none when the range is not written
    /// with integer literals or every key of it is left out.
    fn narrowed(&self, e: &Entry, other: &Entry, s: &Stmt) -> Option<String> {
        let i = initial_of(unwrapped(s).0)?;
        let IndexKey::In { set, .. } = i.keys.first()? else {
            return None;
        };
        let ExprKind::Range(_, kind) = &set.kind else {
            return None;
        };
        // Only where the other gives whole frames, or the same later brackets, does it give
        // every entry of the keys it shares with this one.
        if e.line.is_some() || !(other.inner.is_empty() || other.inner == e.inner) {
            return None;
        }
        let one = BigInt::from(1);
        let mut runs = Vec::new();
        if e.lo < other.lo {
            runs.push((e.lo.clone(), End::At(&other.lo - &one)));
        }
        if let End::At(h) = &other.end
            && e.end.reaches(&(h + &one))
        {
            runs.push((h + &one, e.end.clone()));
        }
        let range = |(lo, end): &(BigInt, End)| match (end, kind) {
            (End::Above, _) => format!("{lo}.."),
            (End::At(h), RangeEnd::Through(_)) => format!("{lo}..={h}"),
            (End::At(h), _) => format!("{lo}..<{}", h + &one),
        };
        let (before, after) = (
            &self.text[s.span.start..set.span.start],
            &self.text[set.span.end..s.span.end],
        );
        let rewritten: Vec<String> = runs
            .iter()
            .map(|r| format!("{before}{}{after}", range(r)))
            .collect();
        match &rewritten[..] {
            [] => None,
            [one] => Some(format!(
                "narrow this one to the keys the other does not give: `{one}`"
            )),
            [low, high] => Some(format!(
                "split this one into two, around the keys the other gives: `{low}` and `{high}`"
            )),
            _ => unreachable!("a run less another run leaves at most two runs"),
        }
    }

    /// Row "Two sentinel values for one variable": the entries `a` and `b`, `b` the later in
    /// the text, which both give some entry of one variable.
    fn two_sentinels(&self, ea: &Entry, eb: &Entry, stmts: &[Stmt]) -> Error {
        let name = eb.name;
        let (a, b) = (&stmts[ea.stmt], &stmts[eb.stmt]);
        let (aw, bw) = (self.text_of(a.span), self.text_of(b.span));
        let mutable = |s: &Stmt| unwrapped(s).2;
        // Whether the entry gives the frame `x[-1]` alone, as `initial x = e;` does.
        let frame = |e: &Entry| {
            e.line.is_none()
                && e.inner.is_empty()
                && e.lo == BigInt::from(-1)
                && e.end == End::At(BigInt::from(-1))
        };
        let mut notes = vec![
            Note {
                span: a.span,
                text: format!("the first site, which gives {}", self.gives(a, name)),
            },
            Note {
                span: b.span,
                text: format!("the second site, which gives {}", self.gives(b, name)),
            },
        ];
        match (mutable(a), mutable(b)) {
            // A `mutable` declaration and an `initial` statement: the declaration stays, and
            // the `initial` statement's value may move into it when it gives `x[-1]` alone.
            (true, false) | (false, true) => {
                let (m, i, mw, ei) = if mutable(a) {
                    (a, b, aw, eb)
                } else {
                    (b, a, bw, ea)
                };
                notes.push(Note {
                    span: i.span,
                    text: format!(
                        "repair: keep `{mw}` and {}",
                        self.drop_name(i, name, "this statement")
                    ),
                });
                if frame(ei)
                    && let (Some(iv), Some(mv)) = (self.value_for(i, name), self.value_for(m, name))
                {
                    let moved = format!(
                        "{}{}{}",
                        &self.text[m.span.start..mv.start],
                        self.text_of(iv),
                        &self.text[mv.end..m.span.end]
                    );
                    notes.push(Note {
                        span: i.span,
                        text: format!(
                            "repair: {}, and write its value of `{name}` in the declaration: \
                             `{moved}`",
                            self.drop_name(i, name, "this statement")
                        ),
                    });
                }
            }
            _ => {
                notes.push(Note {
                    span: b.span,
                    text: format!(
                        "repair: keep the first, `{aw}`, and {}",
                        self.drop_name(b, name, "this one")
                    ),
                });
                notes.push(Note {
                    span: a.span,
                    text: format!(
                        "repair: keep the second, `{bw}`, and {}",
                        self.drop_name(a, name, "this one")
                    ),
                });
            }
        }
        for (e, other, s) in [(eb, ea, b), (ea, eb, a)] {
            if let Some(text) = self.narrowed(e, other, s) {
                notes.push(Note {
                    span: s.span,
                    text: format!("repair: {text}"),
                });
            }
        }
        let message = if frame(ea) && frame(eb) {
            format!(
                "`{name}` is given its sentinel value, its value before step 0, twice in this \
                 loop: first by `{aw}`, then by `{bw}`. The statements of a loop's body run in \
                 the order their data dependencies fix, not the order they are written, so one \
                 statement gives the sentinel value wherever it stands, and a second one is a \
                 second writer of the same entry, even where the two values agree. Keep one of \
                 the two."
            )
        } else {
            let unkeyed = [a, b]
                .iter()
                .any(|s| initial_of(unwrapped(s).0).is_none_or(|i| i.keys.is_empty()));
            let frame_rule = if unkeyed {
                format!(
                    " `initial {name} = e;` and `mutable {name} = e;` give the entry `{name}[-1]`."
                )
            } else {
                String::new()
            };
            format!(
                "`{name}` is given {} twice in this loop: first by `{aw}`, then by `{bw}`.\
                 {frame_rule} The statements of a loop's body run in the order their data \
                 dependencies fix, not the order they are written, so one statement gives a \
                 sentinel value wherever it stands, and a second one is a second writer of the \
                 same entry, even where the two values agree. Give each entry once.",
                self.shared(ea, eb, stmts)
            )
        };
        Error {
            row: Some(Row::TwoSentinels),
            menu: String::new(),
            span: b.span,
            message,
            notes,
        }
    }
}
