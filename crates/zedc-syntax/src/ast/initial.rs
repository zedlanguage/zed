//! The `initial` statement (DESIGN.md sec:generations, step L6.1a): where it may stand, which
//! names it may give a value, what its value may read, and one sentinel value for each
//! variable. Each check is one of the rows of sec:diagnostics: "An `initial` statement outside
//! a loop, or under `local`", "An `initial` statement for a name the loop does not update",
//! "An `initial` value that reads a name of its own loop", "Two sentinel values for one
//! variable", "`with carryForward` on a keyed boundary entry", "A loop variable not updated on
//! every path of a step", and, for an entry written as a bare statement, "A boundary entry of a
//! loop written without `initial`". The forms the parser stops at, `with x = e`, `with initial x
//! = e` and `with x[-2] = e` on a statement of a loop, and the removed form `mutable x = e;`,
//! are found by the parser (`crate::parse`).

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;

use super::builder::{Builder, Level};
use super::sentinel::{End, Entry, Keys, Sentinels, keys_of};
use super::{
    BinaryOp, CARRY_FORWARD, Error, Expr, ExprKind, Field, IndexKey, Initial, Note, Pattern,
    RangeEnd, Stmt, StmtKind, StrPart, Target, TypeKind, UnaryOp,
};
use crate::lex::{Span, Tok, Token};
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

/// The declaration under the `local` and annotations that wrap `s`, and whether a `local` wraps
/// it.
fn unwrapped(mut s: &Stmt) -> (&Stmt, bool) {
    let mut local = false;
    loop {
        match &s.kind {
            StmtKind::Local(d) => {
                local = true;
                s = d;
            }
            StmtKind::Annotated { decl, .. } => s = decl,
            _ => return (s, local),
        }
    }
}

/// `x` for `x'`, and `x` itself for a name with no prime.
fn unprimed(name: &str) -> &str {
    name.strip_suffix('\'').unwrap_or(name)
}

/// Whether `e` is a negative integer literal, `-2`.
fn negative_literal(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Unary(UnaryOp::Neg, x) if matches!(x.kind, ExprKind::Int { .. }))
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

/// The entries each sentinel site among `stmts` gives, in written order: `initial x = e;` and
/// `initial a, b = e;` give the frame `x[-1]` of each name, and an `initial` statement with
/// keys the entries its keys give. A site whose literal range holds no key, `initial x[i in
/// -1..<-1] = 0;`, gives none.
fn entries_of<'s>(stmts: &'s [Stmt]) -> Vec<Entry<'s>> {
    let mut out = Vec::new();
    for (stmt, s) in stmts.iter().enumerate() {
        let d = unwrapped(s).0;
        let frame = |name: &'s str| Entry {
            name,
            line: None,
            lo: BigInt::from(-1),
            end: End::At(BigInt::from(-1)),
            inner: Vec::new(),
            stmt,
        };
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

/// A sentinel site, an `initial` statement: the name of each component with its span; the
/// value; and the value's parts when it is a tuple written out with one part for each of
/// several names.
struct Site<'s> {
    targets: &'s [(String, Span)],
    value: &'s Expr,
    parts: Option<&'s [Expr]>,
}

/// What a walk of expressions finds: the names read, each with its span, in the order met; and
/// the names bound inside the walked code.
#[derive(Default)]
struct Found<'e> {
    reads: Vec<(&'e str, Span)>,
    bound: HashSet<&'e str>,
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
            ExprKind::Spread { of, .. } => exprs.push(of),
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
        StmtKind::Local(d) => todo.push(d),
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

/// A construct of a step whose parts run on some paths only (DESIGN.md sec:generations,
/// "Recurrences and `with carryForward`").
#[derive(Clone, Copy)]
enum Construct {
    If,
    Match,
    Else,
    And,
    Or,
    For,
    Lambda,
    Indexed,
}

impl Construct {
    /// The construct as a message names it: "`if`".
    fn name(self) -> &'static str {
        match self {
            Construct::If => "`if`",
            Construct::Match => "`match`",
            Construct::Else => "`else`",
            Construct::And => "`&&`",
            Construct::Or => "`||`",
            Construct::For => "`for`",
            Construct::Lambda => "lambda",
            Construct::Indexed => "indexed definition",
        }
    }

    /// The part of it that runs on some paths only: "a branch of the `if`".
    fn part(self) -> &'static str {
        match self {
            Construct::If => "a branch of the `if`",
            Construct::Match => "an arm of the `match`",
            Construct::Else => "the default of the `else`",
            Construct::And => "the right side of the `&&`",
            Construct::Or => "the right side of the `||`",
            Construct::For => "the body of the `for`",
            Construct::Lambda => "the body of the lambda",
            Construct::Indexed => "the value of the indexed definition",
        }
    }
}

/// The innermost construct whose part holds a node, and that construct's span.
#[derive(Clone, Copy)]
struct Branch {
    span: Span,
    what: Construct,
}

/// An update of a variable: the variable; the span of the update, the statement for `x' = …`,
/// `x' <- e` and `x'[k] = …`, and `x*.m` or `x[i]*.m` for a `*.` call; and the innermost construct whose part
/// holds it (none when it runs on every path of the step).
struct Update<'e> {
    name: &'e str,
    span: Span,
    branch: Option<Branch>,
}

/// A `.` call on a variable or a path into it, `c.bump(3)`, `grid[i].relax()` or `p.pos.m()`, or a `.` read
/// of a member, `c.tick` (a method declared without parentheses is called so): an update when
/// written with `*.`, when its method writes the next receiver. The variable; the span of the
/// call; where the receiver ends, before the `.`; whether the receiver is the variable itself; the
/// innermost construct whose part holds it;
/// the statement whose whole value it is, if any; and whether its value is dropped, as the value
/// of an expression statement or a branch, arm or export of one is.
struct DotCall<'e> {
    name: &'e str,
    method: &'e str,
    span: Span,
    of_end: usize,
    bare: bool,
    branch: Option<Branch>,
    stmt: Option<&'e Stmt>,
    dropped: bool,
}

/// The repair of a [`DotCall`] whose method writes the next receiver: the call as written,
/// `c.bump(3)`; the call written with `*.`, `c*.bump(3)`; and the text the repair replaces, the
/// whole statement when the call is one's whole value, with what replaces it (`_ = c*.bump(3);`
/// in place of `c.bump(3);`, since a statement drops no declared result).
struct Fix {
    span: Span,
    branch: Option<Branch>,
    call: String,
    star: String,
    replaced: String,
    code: String,
}

/// `items` joined as a sentence lists them: `a`, `a and b`, `a, b and c`.
fn and_list(items: impl IntoIterator<Item = String>) -> String {
    let mut items: Vec<String> = items.into_iter().collect();
    match items.pop() {
        None => String::new(),
        Some(last) if items.is_empty() => last,
        Some(last) => format!("{} and {last}", items.join(", ")),
    }
}

/// That the `.` calls of `fixes` do not update `name`: "`c.bump(3)` does not update `c`".
fn not_updating(name: &str, fixes: &[Fix]) -> String {
    let verb = if fixes.len() == 1 { "does" } else { "do" };
    let calls = and_list(fixes.iter().map(|f| format!("`{}`", f.call)));
    format!("{calls} {verb} not update `{name}`")
}

/// The repair note of the `.` calls of `fixes`, at the first: each call written with `*.` in
/// place of what it replaces, and `carry`, the `initial` statement with `with carryForward` in
/// place of the statement as written, when the calls run on some paths only.
fn dot_repair(fixes: &[Fix], carry: Option<(&str, &str)>) -> Note {
    let mut parts: Vec<String> = fixes
        .iter()
        .map(|f| format!("`{}` in place of `{}`", f.code, f.replaced))
        .collect();
    parts.extend(carry.map(|(code, written)| format!("`{code}` in place of `{written}`")));
    Note {
        span: fixes[0].span,
        text: format!("repair: {}", and_list(parts)),
    }
}

/// What [`every_path`] finds in a step.
struct Walk<'e> {
    must: Must<'e>,
    updates: Vec<Update<'e>>,
    dots: Vec<DotCall<'e>>,
}

/// The variables every path through a node updates: all of them when every path ends in
/// `break`, and otherwise a set.
enum Must<'e> {
    All,
    Names(HashSet<&'e str>),
}

impl<'e> Must<'e> {
    fn none() -> Self {
        Must::Names(HashSet::new())
    }

    /// The variables updated by a node that runs both parts, one after the other. The smaller
    /// set is added to the larger, so a variable moves O(log n) times over a walk of n nodes.
    fn union(self, other: Self) -> Self {
        match (self, other) {
            (Must::All, _) | (_, Must::All) => Must::All,
            (Must::Names(a), Must::Names(b)) => {
                let (mut big, small) = if a.len() >= b.len() { (a, b) } else { (b, a) };
                big.extend(small);
                Must::Names(big)
            }
        }
    }

    /// The variables updated by a node that runs one part or the other. The smaller set keeps
    /// its members the larger holds: O(min) for the two sizes.
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Must::All, m) | (m, Must::All) => m,
            (Must::Names(a), Must::Names(b)) => {
                let (big, mut small) = if a.len() >= b.len() { (a, b) } else { (b, a) };
                small.retain(|n| big.contains(n));
                Must::Names(small)
            }
        }
    }
}

/// The variable a `*.` call on `of` updates, and whether an index lies on the path to it: the
/// name the path starts at, `c` in `c*.m`, `grid` in `grid[i]*.m` and `grid[i][j]*.m`, `p` in
/// `p.pos*.m`, and the root variable of a path of both, `p` in `p.items[i]*.m` and `grid` in
/// `grid[i].pos*.m`. A name written right before a `.` that the text only uses as the
/// qualifier of an imported unit, `shapes` in `shapes.origin*.reset()` after `import
/// geometry.shapes;`, is no variable and is not a receiver ([`qualifiers`]). Each step moves
/// down one index or field of the receiver, a node no other call's receiver holds, so the
/// calls of a step cost O(n) together.
fn receiver<'e>(mut of: &'e Expr, qualifiers: &HashSet<&str>) -> Option<(&'e str, bool)> {
    let mut indexed = false;
    let mut field = false;
    loop {
        match &of.kind {
            ExprKind::Name(n) if field && qualifiers.contains(n.as_str()) => return None,
            ExprKind::Name(n) => return Some((unprimed(n), indexed)),
            ExprKind::Index(a, _) => {
                (of, indexed, field) = (a, true, false);
            }
            ExprKind::Member { of: a, .. } => {
                (of, field) = (a, true);
            }
            _ => return None,
        }
    }
}

/// The names an `import` of `levels`, the token lists of a text and its string holes, binds to
/// a unit, `shapes` in `import geometry.shapes;` and `g` in `import geometry.shapes as g;`, that
/// the text writes nowhere else but right before a `.` or right after a `.`, `?.`, `*.` or
/// `::`. Such a name can only be a qualifier: a variable is written at its binder, which is
/// never right before or after a `.`, and an `import a.{x}` that binds `x` writes it between
/// braces. A word in a comment is not a token and does not count; a name of a string hole
/// does.
// Complexity tradeoff: the receiver of a `*.` call on a field path is its leftmost name when
// name resolution makes that name a variable, and the builder, which runs before resolution,
// has no scopes. Finding the binder of each such receiver by walking up its enclosing scopes
// costs O(depth) per call and needs the binders of every scope, a second resolver. Here one
// pass over the tokens lists the imports, O(n) with no allocation when there is none, and a
// second pass, run only when an import binds a unit, removes the names written in any other
// place: each receiver is then one hash lookup. What is given up: a spelling that a text both
// imports as a unit and binds as a variable, by a binder written right before a `.`, which no
// form of the grammar has, would be taken for the qualifier. A name that is never bound and is
// taken for a variable is a program the resolver refuses anyway (COMPLEXITY.md row
// CHK-update-field-receiver; test `the_must_assign_check_scales`).
pub(super) fn qualifiers<'s>(text: &'s str, levels: &[Level]) -> HashSet<&'s str> {
    let word = |t: &Token| &text[t.span.start..t.span.end];
    fn tok(ts: &[Token], i: usize) -> Option<&Tok> {
        ts.get(i).map(|t| &t.tok)
    }
    let mut out = HashSet::new();
    for l in levels {
        let ts = l.tokens;
        for i in 0..ts.len() {
            if !matches!(ts[i].tok, Tok::Keyword("import")) {
                continue;
            }
            let mut k = i + 1;
            while let Some(Tok::Name(_) | Tok::Op(".")) = tok(ts, k) {
                k += 1;
            }
            match tok(ts, k) {
                Some(Tok::Keyword("as")) => {
                    if let Some(Tok::Name(_)) = tok(ts, k + 1) {
                        out.insert(word(&ts[k + 1]));
                    }
                }
                Some(Tok::Op("{")) => {}
                _ => {
                    if k > i + 1
                        && let Tok::Name(_) = ts[k - 1].tok
                    {
                        out.insert(word(&ts[k - 1]));
                    }
                }
            }
        }
    }
    if out.is_empty() {
        return out;
    }
    for l in levels {
        let ts = l.tokens;
        let mut import = false;
        for (i, t) in ts.iter().enumerate() {
            match &t.tok {
                Tok::Keyword("import") => import = true,
                Tok::Op(";" | "{") => import = false,
                Tok::Name(_) if !import => {
                    let before = i.checked_sub(1).and_then(|j| tok(ts, j));
                    let after = matches!(tok(ts, i + 1), Some(Tok::Op(".")));
                    if !after && !matches!(before, Some(Tok::Op("." | "?." | "*." | "::"))) {
                        out.remove(unprimed(word(t)));
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// How a part of a node combines into the node's [`Must`]: run on every path through the node,
/// one of several alternatives of which a path runs exactly one, or run on some paths only.
#[derive(Clone, Copy)]
enum Role {
    Always,
    Alt,
    Some,
}

/// A step of the walk of [`every_path`]: an expression or statement to visit, with the branch
/// it stands in and its role in its parent; or the combination of the last `kids` results into
/// one, with what the node itself updates.
enum Task<'e> {
    Expr(&'e Expr, Option<Branch>, Role),
    Stmt(&'e Stmt, Option<Branch>, Role),
    Join {
        kids: usize,
        own: Must<'e>,
        role: Role,
    },
}

/// The variables that every path of a step through `stmts`, the statements of a loop's body,
/// updates, and each update of a variable with the branch it stands in (DESIGN.md
/// sec:generations, *must-assign*). An update is `x' = …`, `x' <- e`, `x'[k] = …` or a `*.`
/// call on `x`, an entry of it or a field of either, `x[i]*.m(…)`, `x.pos*.m(…)` or
/// `x[i].pos*.m(…)` ([`receiver`]), wherever it is written in the step, a nested block
/// included: one in a nested block counts on the paths through that block. Top-level
/// statements run on every path; a branch of an `if`, an arm of a `match`, the default of an
/// `else`, the right side of `&&` and `||`, the body of a `for`, the body of a lambda and the
/// value of an indexed definition (computed once for each key) run on some paths only, except
/// that a value that is a `*.` call on a path through an entry, `old[i in cells] =
/// grid[i]*.relax()` or `grid[i].pos*.relax()`, updates `grid` key by key, as `grid'[i in
/// cells] = …` does, on every path through it; a path that ends in `break` needs no update,
/// and `return`, a block's export, ends no path. Nested loops, whose names are their own, are
/// not entered, nor are the values of `initial` statements, computed once before the first
/// step, or the bodies of functions and methods, which are not part of a step.
///
/// The walk also lists each `.` call on a variable ([`DotCall`]), which updates nothing; one
/// whose span is in `counted` is taken as an update, as it would be written with `*.`, to ask
/// whether rewriting those calls would complete every path (empty but on a rejection).
///
/// One visit of each node, by a work list with a stack of results, so the depth of the code
/// costs no stack. A node's result is the union of its parts that always run with the meet of
/// its alternatives.
// Complexity tradeoff: the naive walk copies the sets of a node's parts into a new set at each
// node, O(n^2) for n variables each updated on its own paths (31 times the bytes at 8n, row
// MUTABLE-to-initial-facet); here a union adds the smaller set to the larger, and a meet keeps
// the smaller set's members the larger holds, so each costs at most the number of updates in
// the part with fewer of them, and an update is in that part O(log n) times: O(n log n)
// expected for a step of n nodes, O(n) when no node joins two parts that both hold updates. A
// strictly linear method, a check per variable over the tree of its updates' common ancestors
// with constant-time ancestor queries, was weighed and not used: it needs an ancestor index of
// the step and a second pass, for at most a log factor (CHK-update-every-path-cases).
fn every_path<'e>(
    stmts: &'e [Stmt],
    qualifiers: &HashSet<&str>,
    counted: &HashSet<Span>,
) -> Walk<'e> {
    let mut updates = Vec::new();
    let mut dots: Vec<DotCall<'e>> = Vec::new();
    // The statements whose whole value is a call or a member read, by the span of the value.
    let mut whole: HashMap<Span, &'e Stmt> = HashMap::new();
    // The expressions whose value is dropped: the value of an expression statement, and each
    // branch, arm and export of one whose value is dropped.
    let mut dropped: HashSet<Span> = HashSet::new();
    let mut results: Vec<(Role, Must<'e>)> = Vec::new();
    let mut tasks: Vec<Task<'e>> = vec![Task::Join {
        kids: stmts.len(),
        own: Must::none(),
        role: Role::Always,
    }];
    tasks.extend(stmts.iter().map(|s| Task::Stmt(s, None, Role::Always)));
    while let Some(task) = tasks.pop() {
        match task {
            Task::Join { kids, own, role } => {
                let mut acc = own;
                let mut alt: Option<Must> = None;
                for _ in 0..kids {
                    let Some((r, m)) = results.pop() else {
                        unreachable!("each kid of a node leaves one result");
                    };
                    match r {
                        Role::Always => acc = acc.union(m),
                        Role::Alt => {
                            alt = Some(match alt {
                                Some(a) => a.meet(m),
                                None => m,
                            })
                        }
                        Role::Some => {}
                    }
                }
                if let Some(a) = alt {
                    acc = acc.union(a);
                }
                results.push((role, acc));
            }
            Task::Stmt(s, branch, role) => {
                // The variables the statement itself updates, and its parts.
                let mut own: HashSet<&'e str> = HashSet::new();
                let mut kids: Vec<Task<'e>> = Vec::new();
                if let StmtKind::Bind { value: v, .. } | StmtKind::Expr(v) = &s.kind
                    && matches!(v.kind, ExprKind::Call { .. } | ExprKind::Member { .. })
                {
                    whole.insert(v.span, s);
                }
                if let StmtKind::Expr(v) = &s.kind {
                    dropped.insert(v.span);
                }
                let mut always = |x: &'e Expr| kids.push(Task::Expr(x, branch, Role::Always));
                match &s.kind {
                    StmtKind::Bind { targets, value } => {
                        for t in targets {
                            if let Target::Name(n, _) = t
                                && n.ends_with('\'')
                            {
                                own.insert(unprimed(n));
                            }
                        }
                        always(value);
                    }
                    StmtKind::Push { port, value } => {
                        if port.ends_with('\'') {
                            own.insert(unprimed(port));
                        }
                        always(value);
                    }
                    StmtKind::While(value) | StmtKind::Until(value) | StmtKind::Expr(value) => {
                        always(value)
                    }
                    StmtKind::Return(es) => es.iter().for_each(&mut always),
                    // `d'[v in nodes] = …` updates `d` key by key, and so does `old[i in cells] =
                    // grid[i]*.relax()`, which writes `grid'[i]` for each key, and so does a call on
                    // any path with an index on it, `grid[i].pos*.relax()`. The domains and the
                    // boundary entries are computed once on a step; the value once for each key.
                    StmtKind::IndexedDef(d) => {
                        if d.name.ends_with('\'') {
                            own.insert(unprimed(&d.name));
                        }
                        let call = match &d.value.kind {
                            ExprKind::Call { callee, .. } => callee,
                            _ => &d.value,
                        };
                        if let ExprKind::Spread { of, .. } = &call.kind
                            && let Some((n, true)) = receiver(of, qualifiers)
                        {
                            own.insert(n);
                        }
                        for k in d.keys.iter().chain(d.boundary.iter().flat_map(|b| &b.keys)) {
                            match k {
                                IndexKey::In { set, .. } => always(set),
                                IndexKey::At(e) => always(e),
                            }
                        }
                        d.boundary.iter().for_each(|b| always(&b.value));
                        let b = Some(Branch {
                            span: s.span,
                            what: Construct::Indexed,
                        });
                        kids.push(Task::Expr(&d.value, b, Role::Some));
                    }
                    StmtKind::Local(d) | StmtKind::Annotated { decl: d, .. } => {
                        tasks.push(Task::Stmt(d, branch, role));
                        continue;
                    }
                    StmtKind::Initial(_)
                    | StmtKind::Function(_)
                    | StmtKind::Method(_)
                    | StmtKind::Struct(_)
                    | StmtKind::Type(_)
                    | StmtKind::Import(_)
                    | StmtKind::UnitAnnot(_) => {}
                }
                updates.extend(own.iter().map(|&name| Update {
                    name,
                    span: s.span,
                    branch,
                }));
                let own = Must::Names(own);
                if kids.is_empty() {
                    results.push((role, own));
                } else {
                    tasks.push(Task::Join {
                        kids: kids.len(),
                        own,
                        role,
                    });
                    tasks.append(&mut kids);
                }
            }
            Task::Expr(e, branch, role) => {
                let gone = dropped.contains(&e.span);
                let inside = |what| Some(Branch { span: e.span, what });
                let mut own = Must::none();
                let mut kids: Vec<Task<'e>> = Vec::new();
                let mut always = |x: &'e Expr| kids.push(Task::Expr(x, branch, Role::Always));
                match &e.kind {
                    ExprKind::Int { .. }
                    | ExprKind::Float { .. }
                    | ExprKind::Rat(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Atom(_)
                    | ExprKind::This
                    | ExprKind::Section(_)
                    | ExprKind::Name(_)
                    | ExprKind::Loop { .. } => {}
                    ExprKind::Str(parts) => {
                        for p in parts {
                            if let StrPart::Hole(x) = p {
                                always(x);
                            }
                        }
                    }
                    ExprKind::Spread { of, .. } => {
                        if let Some((n, _)) = receiver(of, qualifiers) {
                            own = Must::Names(HashSet::from([n]));
                            updates.push(Update {
                                name: n,
                                span: e.span,
                                branch,
                            });
                        }
                        always(of);
                    }
                    ExprKind::Break(a) => {
                        own = Must::All;
                        always(a);
                    }
                    ExprKind::Member {
                        of,
                        name: method,
                        safe: false,
                    } if receiver(of, qualifiers).is_some() => {
                        let (name, _) = receiver(of, qualifiers).expect("matched by the guard");
                        if counted.contains(&e.span) {
                            own = Must::Names(HashSet::from([name]));
                        }
                        dots.push(DotCall {
                            name,
                            method,
                            span: e.span,
                            of_end: of.span.end,
                            bare: matches!(of.kind, ExprKind::Name(_)),
                            branch,
                            stmt: whole.get(&e.span).copied(),
                            dropped: gone,
                        });
                        always(of);
                    }
                    ExprKind::Unary(_, a)
                    | ExprKind::Is { of: a, .. }
                    | ExprKind::Member { of: a, .. }
                    | ExprKind::Read { of: a, .. } => always(a),
                    ExprKind::SortKey { key, .. } => {
                        if let Some(k) = key {
                            always(k);
                        }
                    }
                    ExprKind::Binary(op @ (BinaryOp::And | BinaryOp::Or), a, b) => {
                        let what = if *op == BinaryOp::And {
                            Construct::And
                        } else {
                            Construct::Or
                        };
                        always(a);
                        kids.push(Task::Expr(b, inside(what), Role::Some));
                    }
                    ExprKind::Binary(_, a, b)
                    | ExprKind::Index(a, b)
                    | ExprKind::In { of: a, set: b, .. }
                    | ExprKind::Reduce { of: a, op: b } => {
                        always(a);
                        always(b);
                    }
                    ExprKind::Else { of, default, .. } => {
                        always(of);
                        kids.push(Task::Expr(default, inside(Construct::Else), Role::Some));
                    }
                    ExprKind::Call {
                        callee,
                        positional,
                        named,
                        ..
                    } => {
                        // A `.` call is recorded with the span of the whole call, its arguments
                        // included; its member read, the callee, is not recorded again.
                        match &callee.kind {
                            ExprKind::Member {
                                of,
                                name: method,
                                safe: false,
                            } if receiver(of, qualifiers).is_some() => {
                                let (name, _) =
                                    receiver(of, qualifiers).expect("matched by the guard");
                                if counted.contains(&e.span) {
                                    own = Must::Names(HashSet::from([name]));
                                }
                                dots.push(DotCall {
                                    name,
                                    method,
                                    span: e.span,
                                    of_end: of.span.end,
                                    bare: matches!(of.kind, ExprKind::Name(_)),
                                    branch,
                                    stmt: whole.get(&e.span).copied(),
                                    dropped: gone,
                                });
                                always(of);
                            }
                            _ => always(callee),
                        }
                        positional.iter().for_each(&mut always);
                        named.iter().for_each(|(_, x)| always(x));
                    }
                    ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => {
                        es.iter().for_each(&mut always);
                    }
                    ExprKind::Map(entries) => {
                        for (k, v) in entries {
                            always(k);
                            always(v);
                        }
                    }
                    ExprKind::Range(from, to) => {
                        always(from);
                        match to {
                            RangeEnd::Below(b) | RangeEnd::Through(b) => always(b),
                            RangeEnd::Open => {}
                        }
                    }
                    ExprKind::For {
                        source,
                        guard,
                        body,
                        ..
                    } => {
                        always(source);
                        let b = inside(Construct::For);
                        kids.extend(guard.iter().map(|g| Task::Expr(g, b, Role::Some)));
                        kids.push(Task::Expr(body, b, Role::Some));
                    }
                    ExprKind::Lambda { params, body } => {
                        let b = inside(Construct::Lambda);
                        kids.extend(
                            params
                                .iter()
                                .filter_map(|p| p.default.as_ref())
                                .map(|d| Task::Expr(d, b, Role::Some)),
                        );
                        kids.push(Task::Expr(body, b, Role::Some));
                    }
                    ExprKind::Block(stmts) => {
                        if gone
                            && let Some(Stmt {
                                kind: StmtKind::Return(es),
                                ..
                            }) = stmts.last()
                            && let [x] = &es[..]
                        {
                            dropped.insert(x.span);
                        }
                        kids.extend(stmts.iter().map(|s| Task::Stmt(s, branch, Role::Always)));
                    }
                    ExprKind::Match { of, arms } => {
                        always(of);
                        let b = inside(Construct::Match);
                        for a in arms {
                            if gone {
                                dropped.insert(a.body.span);
                            }
                            kids.extend(a.guard.iter().map(|g| Task::Expr(g, b, Role::Some)));
                            kids.push(Task::Expr(&a.body, b, Role::Alt));
                        }
                    }
                    ExprKind::Record(fields) => fields.iter().for_each(|(_, x)| always(x)),
                    ExprKind::With { of, updates } => {
                        always(of);
                        updates.iter().for_each(|u| always(&u.value));
                    }
                    ExprKind::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        always(cond);
                        if gone {
                            dropped.extend([then.span, otherwise.span]);
                        }
                        let b = inside(Construct::If);
                        kids.push(Task::Expr(then, b, Role::Alt));
                        kids.push(Task::Expr(otherwise, b, Role::Alt));
                    }
                }
                if kids.is_empty() {
                    results.push((role, own));
                } else {
                    tasks.push(Task::Join {
                        kids: kids.len(),
                        own,
                        role,
                    });
                    tasks.append(&mut kids);
                }
            }
        }
    }
    let Some((_, must)) = results.pop() else {
        unreachable!("the walk of a body leaves one result");
    };
    Walk {
        must,
        updates,
        dots,
    }
}

/// What a name of a loop is, for the message of an `initial` value that reads it.
enum LoopName {
    /// A variable the loop updates.
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
            let (d, local) = unwrapped(s);
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

    /// The checks of the body of a loop (`label` its step index, `at` its text). Each `initial`
    /// statement names a variable the loop updates, reads no name of the loop, gives a sentinel
    /// value no other statement gives, and has `with carryForward` only when it has no keys; an
    /// entry below generation 0 is not written as a bare statement; and every variable the loop
    /// updates is updated on every path of a step, unless it is carried (*must-assign*,
    /// sec:generations). One pass over the body's statements lists what they define and carry,
    /// one walk of the step lists what it updates and which updates every path makes
    /// ([`every_path`]), then one pass over the statements checks the entries each site gives
    /// against those of the sites before it by the values of their keys (`Sentinels`): O(n log n
    /// plus k log k) for a body of n nodes and k sites, where comparing each pair of sites would
    /// be O(k^2).
    pub(super) fn loop_initials(
        &self,
        label: Option<&str>,
        at: Span,
        body: &Expr,
    ) -> Result<(), Error> {
        let ExprKind::Block(stmts) = &body.kind else {
            return Ok(());
        };
        // What the body's own statements define on each step, and the names carried forward.
        let mut locals: HashSet<&str> = HashSet::new();
        let mut carried: HashSet<&str> = HashSet::new();
        let mut sites = false;
        for s in stmts {
            let d = unwrapped(s).0;
            match &d.kind {
                StmtKind::Bind { targets, .. } => {
                    for t in targets {
                        if let Target::Name(n, _) = t
                            && !n.ends_with('\'')
                        {
                            locals.insert(n);
                        }
                    }
                }
                StmtKind::IndexedDef(x) => {
                    sites = true;
                    if !x.name.ends_with('\'') {
                        locals.insert(&x.name);
                    }
                }
                StmtKind::Function(f) => {
                    locals.insert(&f.name);
                }
                _ => {}
            }
            if let Some(i) = initial_of(d) {
                sites = true;
                if i.carry && i.keys.is_empty() {
                    carried.extend(i.names.iter().map(|(n, _)| n.as_str()));
                }
            }
        }
        // What the step updates, on any path; a variable not carried must be updated on every
        // path.
        let Walk {
            must,
            mut updates,
            dots,
        } = every_path(stmts, self.qualifiers, &HashSet::new());
        let updated: HashSet<&str> = updates.iter().map(|u| u.name).collect();
        if sites {
            self.initial_sites(label, at, stmts, &updated, &locals, &dots)?;
        }
        let Must::Names(must) = must else {
            return Ok(());
        };
        updates.sort_by_key(|u| u.span.start);
        match (updates.iter()).find(|u| !must.contains(u.name) && !carried.contains(u.name)) {
            Some(first) => {
                let name = first.name;
                let of_name: Vec<&Update> = updates.iter().filter(|u| u.name == name).collect();
                Err(self.not_every_path(name, &of_name, stmts, at, &dots))
            }
            None => Ok(()),
        }
    }

    /// The checks of [`Self::loop_initials`] on the `initial` statements and indexed definitions
    /// among `stmts`, given what the body updates and defines on each step, and its `.` calls on
    /// variables.
    fn initial_sites(
        &self,
        label: Option<&str>,
        at: Span,
        stmts: &[Stmt],
        updated: &HashSet<&str>,
        locals: &HashSet<&str>,
        dots: &[DotCall],
    ) -> Result<(), Error> {
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
                if i.carry && !i.keys.is_empty() {
                    return Err(self.carry_on_keyed(s, i, stmts));
                }
                for (n, _) in &i.names {
                    if !updated.contains(n.as_str()) {
                        return Err(self.not_updated(s, n, at, stmts, dots));
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
                    } else if updated.contains(base) {
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

    /// Row "`with carryForward` on a keyed boundary entry", for the `initial` statement `s`.
    fn carry_on_keyed(&self, s: &Stmt, i: &Initial, stmts: &[Stmt]) -> Error {
        let written = self.text_of(s.span);
        let name = &i.names[0].0;
        let value = self.text_of(i.value.span);
        let bare = format!("{};", &self.text[s.span.start..i.value.span.end]);
        // The statement without keys that gives `name` its frame `name[-1]`, if there is one.
        let keyless = stmts.iter().find(|t| {
            initial_of(unwrapped(t).0)
                .is_some_and(|j| j.keys.is_empty() && j.names.iter().any(|(n, _)| n == name))
        });
        // Whether this statement gives the entry `name[-1]` alone.
        let frame = i.keys.len() == 1
            && matches!(keys_of(&i.keys[0]), Some(Keys::Ints(lo, End::At(hi)))
                if lo == BigInt::from(-1) && hi == lo);
        // The first repair, as the code that replaces the statement, and why it is one.
        let (code, why) = match keyless {
            Some(t) => {
                let tw = self.text_of(t.span);
                let head = tw.strip_suffix(';').unwrap_or(tw).trim_end();
                if initial_of(unwrapped(t).0).is_some_and(|j| j.carry) {
                    (
                        bare.clone(),
                        format!("since `{tw}` already carries `{name}` forward"),
                    )
                } else {
                    (
                        format!("{head} with {CARRY_FORWARD}; {bare}"),
                        format!("`with {CARRY_FORWARD}` moved to the statement without keys"),
                    )
                }
            }
            None if frame => (
                format!("initial {name} = {value} with {CARRY_FORWARD};"),
                format!("the statement without keys, which gives the entry `{name}[-1]`"),
            ),
            None => (
                format!("initial {name} = … with {CARRY_FORWARD}; {bare}"),
                format!("with the value of `{name}[-1]` in place of `…`"),
            ),
        };
        Error {
            row: Some(Row::CarryOnKeyedEntry),
            menu: String::new(),
            span: s.span,
            message: format!(
                "`with {CARRY_FORWARD}` on an `initial` statement with keys: `{written}`. Try \
                 `{code}` instead."
            ),
            notes: vec![
                Note {
                    span: s.span,
                    text: format!(
                        "`with {CARRY_FORWARD}` makes a step that does not update `{name}` keep \
                         `{name}[t-1]`, which at step 0 is the entry `{name}[-1]`; the `initial` \
                         statement without keys gives that entry, so `with {CARRY_FORWARD}` \
                         stands on it"
                    ),
                },
                Note {
                    span: s.span,
                    text: format!("repair: `{code}`, {why}"),
                },
            ],
        }
    }

    /// Row "A loop variable not updated on every path of a step", for `name`, whose updates are
    /// `updates`, in written order, among the `.` calls `dots` of the step.
    fn not_every_path(
        &self,
        name: &str,
        updates: &[&Update],
        stmts: &[Stmt],
        at: Span,
        dots: &[DotCall],
    ) -> Error {
        let branch = |u: &Update| {
            let Some(b) = u.branch else {
                unreachable!("an update on every path leaves no path without one")
            };
            b
        };
        let where_ = match updates {
            [one] => format!(
                "`{}` updates `{name}` only in {}",
                self.text_of(one.span),
                branch(one).what.part()
            ),
            [rest @ .., last] => {
                let calls: Vec<String> = rest
                    .iter()
                    .map(|u| format!("`{}`", self.text_of(u.span)))
                    .collect();
                format!(
                    "{} and `{}` update `{name}` only on some paths",
                    calls.join(", "),
                    self.text_of(last.span)
                )
            }
            [] => unreachable!("a variable updated on no path is not a candidate"),
        };
        // The `.` calls that, written with `*.`, would update `name`: when they complete every
        // path, they are the repair.
        let fixes = self.dot_fixes(name, dots, stmts);
        let covers = !fixes.is_empty() && self.covers(name, &fixes, stmts);
        let where_ = match covers {
            true => format!("{where_}, and {}", not_updating(name, &fixes)),
            false => where_,
        };
        let mut notes = vec![Note {
            span: at,
            text: format!(
                "the loop, which updates `{name}`: a variable a loop updates is a recurrence, \
                 defined on every frame, so each step updates it on every path; `with \
                 {CARRY_FORWARD}` on its `initial` statement keeps its value on a step that does \
                 not update it"
            ),
        }];
        for u in updates {
            let call = self.text_of(u.span);
            let b = branch(u);
            notes.push(Note {
                span: u.span,
                text: format!(
                    "`{call}` updates `{name}` only on the paths through {}",
                    b.what.part()
                ),
            });
            notes.push(Note {
                span: b.span,
                text: format!("the {} that `{call}` stands in", b.what.name()),
            });
        }
        notes.extend(self.dot_notes(name, &fixes));
        if covers {
            notes.push(dot_repair(&fixes, None));
        }
        let keyless = stmts.iter().find(|t| {
            initial_of(unwrapped(t).0)
                .is_some_and(|j| j.keys.is_empty() && j.names.iter().any(|(n, _)| n == name))
        });
        let (code, note) = match keyless {
            Some(t) => {
                let tw = self.text_of(t.span);
                let head = tw.strip_suffix(';').unwrap_or(tw).trim_end();
                let code = format!("{head} with {CARRY_FORWARD};");
                let text = format!(
                    "repair: `{code}` in place of `{tw}`, so a step that does not update \
                     `{name}` keeps its value"
                );
                (code, Note { span: t.span, text })
            }
            None => {
                let code = format!("initial {name} = … with {CARRY_FORWARD};");
                let text = format!(
                    "repair: `{code}` among the statements of the loop's body, with the value of \
                     `{name}` before step 0 in place of `…`, so a step that does not update \
                     `{name}` keeps its value"
                );
                (code, Note { span: at, text })
            }
        };
        notes.push(note);
        notes.push(Note {
            span: updates[0].span,
            text: format!(
                "repair: update `{name}` on every path, with the update written where the branch \
                 is chosen and `{name}` itself on the paths that leave it as it is: `{name}' = if \
                 … {{ … }} else {{ {name} }};`"
            ),
        });
        let try_ = match covers {
            true => and_list(fixes.iter().map(|f| format!("`{}`", f.code))),
            false => format!("`{code}`"),
        };
        Error {
            row: Some(Row::NotEveryPath),
            menu: String::new(),
            span: updates[0].span,
            message: format!("Not updated on every path of a step: {where_}. Try {try_} instead."),
            notes,
        }
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

    /// Row "An `initial` statement for a name the loop does not update", among the statements
    /// `stmts` of the loop's body, whose `.` calls on variables are `dots`. When `.` calls whose
    /// methods write the next receiver are all that leave `name` without an update, the message
    /// names them and offers them written with `*.`, and `with carryForward` beside them when
    /// they run on some paths only.
    fn not_updated(
        &self,
        s: &Stmt,
        name: &str,
        at: Span,
        stmts: &[Stmt],
        dots: &[DotCall],
    ) -> Error {
        let written = self.text_of(s.span);
        let i = initial_of(unwrapped(s).0);
        let value = i.map_or("…", |i| self.text_of(i.value.span));
        let carried = i.is_some_and(|i| i.carry);
        let fixes = self.dot_fixes(name, dots, stmts);
        let mut notes = vec![Note {
            span: at,
            text: format!("the loop, none of whose statements updates `{name}`"),
        }];
        notes.extend(self.dot_notes(name, &fixes));
        // The repair by the `.` calls: the calls written with `*.`, and when they leave some path
        // without an update, `with carryForward` on the statement, which needs it without keys.
        let carry = match fixes.is_empty() || carried || self.covers(name, &fixes, stmts) {
            true => Some(None),
            false => i.filter(|i| i.keys.is_empty()).map(|_| {
                let head = written.strip_suffix(';').unwrap_or(written).trim_end();
                Some((format!("{head} with {CARRY_FORWARD};"), written))
            }),
        };
        let message = match carry {
            Some(carry) if !fixes.is_empty() => {
                notes.push(dot_repair(
                    &fixes,
                    carry.as_ref().map(|(c, w)| (c.as_str(), *w)),
                ));
                let mut codes: Vec<String> =
                    fixes.iter().map(|f| format!("`{}`", f.code)).collect();
                codes.extend(carry.map(|(c, _)| format!("`{c}`")));
                format!(
                    "No statement of this loop updates `{name}`: {}. Try {} instead.",
                    not_updating(name, &fixes),
                    and_list(codes)
                )
            }
            _ => {
                // A carried variable is still one the loop updates: `with carryForward` keeps
                // its value on a step that does not update it, and makes no name a loop
                // variable by itself.
                let why = if carried {
                    format!(
                        "`with {CARRY_FORWARD}` keeps the value of a variable the loop updates on \
                         a step that does not update it, and does not make `{name}` a variable of \
                         the loop: a value no step changes is a constant, written as a binding \
                         before the loop."
                    )
                } else {
                    format!(
                        "An `initial` statement gives a value before the first step only, so \
                         `{name}` would have no value at any later step."
                    )
                };
                format!(
                    "`{written}` gives `{name}` a value before step 0, and no statement of this \
                     loop updates `{name}`: none writes `{name}' = …`, `{name}' <- e` or \
                     `{name}*.m(…)`. {why}"
                )
            }
        };
        notes.push(Note {
            span: s.span,
            text: format!(
                "repair: add the update the loop is meant to make, `{name}' = …;`, to its body"
            ),
        });
        notes.push(Note {
            span: at,
            text: format!(
                "repair: `{name} = {value};` written before the loop, and `{written}` deleted, for \
                 a value that does not change"
            ),
        });
        Error {
            row: Some(Row::InitialNotUpdated),
            menu: String::new(),
            span: s.span,
            message,
            notes,
        }
    }

    /// The `.` calls among `dots` on `name` whose method writes the next receiver, so that the
    /// call written with `*.` updates `name`, each with its repair ([`Fix`]). The method is the
    /// one declared on the type of `name` when its `initial` statement shows the type, as
    /// `initial c: Counter = …` or `initial c = Counter(…)`, and the call's receiver is `name`
    /// itself, not a path into it such as `c.pos`; otherwise every method of that name
    /// the source declares must agree on what it writes and on its declared result. A call on
    /// `name'`, a call whose method the source does not declare, and a call of a method with no
    /// declared result whose value is used, not dropped (`d = c.tick();` or `x' = if t > 1 {
    /// c.tick() } else { c };`, a new receiver the program reads, which with `*.` would be
    /// nothing), are left out.
    fn dot_fixes(&self, name: &str, dots: &[DotCall], stmts: &[Stmt]) -> Vec<Fix> {
        let ty = stmts
            .iter()
            .filter_map(|t| initial_of(unwrapped(t).0))
            .find(|i| i.keys.is_empty() && i.names.iter().any(|(n, _)| n == name))
            .and_then(|i| match (&i.ty, &i.value.kind) {
                (Some(t), _) => match &t.kind {
                    TypeKind::Name(t) => Some(t.as_str()),
                    _ => None,
                },
                (None, ExprKind::Call { callee, .. }) => match &callee.kind {
                    ExprKind::Name(t) => Some(t.as_str()),
                    _ => None,
                },
                _ => None,
            });
        let mut out = Vec::new();
        for d in dots.iter().filter(|d| d.name == name) {
            let infos = self.methods.named(d.method);
            // The type of `name` is the receiver's type only when the receiver is `name` itself.
            let of_type = ty
                .filter(|_| d.bare)
                .and_then(|t| infos.iter().find(|m| m.receiver == t));
            let info = of_type.or_else(|| match infos {
                [first, rest @ ..] => rest
                    .iter()
                    .all(|m| m.mutates == first.mutates && m.result == first.result)
                    .then_some(first),
                [] => None,
            });
            let Some(info) = info.filter(|m| m.mutates && (m.result || d.dropped)) else {
                continue;
            };
            let receiver = &self.text[d.span.start..d.of_end];
            if receiver
                .split(['[', '.'])
                .next()
                .unwrap_or("")
                .trim_end()
                .ends_with('\'')
            {
                continue;
            }
            let Some(rest) = self.text[d.of_end..d.span.end]
                .trim_start()
                .strip_prefix('.')
            else {
                continue;
            };
            let call = self.text_of(d.span).to_string();
            let star = format!("{receiver}*.{}", rest.trim_start());
            let (replaced, code) = match d.stmt.map(|s| (s, &s.kind)) {
                Some((s, StmtKind::Expr(_) | StmtKind::Bind { .. })) => {
                    let bind = matches!(s.kind, StmtKind::Bind { .. });
                    let before = &self.text[s.span.start..d.span.start];
                    let after = &self.text[d.span.end..s.span.end];
                    let discard = if info.result && !bind { "_ = " } else { "" };
                    (
                        self.text_of(s.span).to_string(),
                        format!("{discard}{before}{star}{after}"),
                    )
                }
                _ => (call.clone(), star.clone()),
            };
            out.push(Fix {
                span: d.span,
                branch: d.branch,
                call,
                star,
                replaced,
                code,
            });
        }
        // The walk visits calls in no fixed order; notes and repairs follow the source.
        out.sort_by_key(|f| f.span.start);
        out
    }

    /// Whether every path of a step through `stmts` updates `name` once the `.` calls of `fixes`
    /// are written with `*.`: one more walk of the step, O(n log n) as [`every_path`] is, made
    /// once, for the rejection.
    fn covers(&self, name: &str, fixes: &[Fix], stmts: &[Stmt]) -> bool {
        let counted: HashSet<Span> = fixes.iter().map(|f| f.span).collect();
        match every_path(stmts, self.qualifiers, &counted).must {
            Must::All => true,
            Must::Names(m) => m.contains(name),
        }
    }

    /// A note at each `.` call of `fixes`: that it does not update `name`, and the paths it runs
    /// on when they are not all of them.
    fn dot_notes(&self, name: &str, fixes: &[Fix]) -> Vec<Note> {
        fixes
            .iter()
            .map(|f| {
                let paths = match f.branch {
                    Some(b) => format!("; it runs only on the paths through {}", b.what.part()),
                    None => String::new(),
                };
                Note {
                    span: f.span,
                    text: format!(
                        "`{}` does not update `{name}`: a `.` call never updates its receiver, \
                         and `{}` does{paths}",
                        f.call, f.star
                    ),
                }
            })
            .collect()
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
        // The start value of the variable read, when an `initial` statement of this body gives
        // one, written in place of the read.
        let start = stmts.iter().find_map(|t| match initial_of(unwrapped(t).0) {
            Some(j) if j.keys.is_empty() && j.names.len() == 1 && j.names[0].0 == base => {
                Some(&j.value)
            }
            _ => None,
        });
        if let Some(v) = start.filter(|v| walk(&[v], &[]).reads.is_empty()) {
            let v = self.text_of(v.span);
            let value = &self.text[i.value.span.start..span.start];
            let rest = &self.text[span.end..s.span.end];
            notes.push(Note {
                span: s.span,
                text: format!(
                    "repair: `{}{value}{v}{rest}`, the start value of `{base}` written in place \
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

    /// The sentinel site `s`, an `initial` statement, read as a [`Site`].
    fn site<'s>(&self, s: &'s Stmt) -> Site<'s> {
        let Some(i) = initial_of(unwrapped(s).0) else {
            unreachable!("a sentinel site is an `initial` statement")
        };
        let parts = match &i.value.kind {
            ExprKind::Tuple(es) if i.names.len() > 1 && es.len() == i.names.len() => Some(&es[..]),
            _ => None,
        };
        Site {
            targets: &i.names,
            value: &i.value,
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
        let k = targets.iter().position(|(n, _)| n == name)?;
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
                let names: Vec<&str> = targets.iter().map(|(n, _)| n.as_str()).collect();
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
    /// the statement without `name` with `…` for the value of the other targets. A rewritten
    /// statement keeps what follows its value, ` with carryForward;` or `;`.
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
        let first = targets[0].1;
        let head = &self.text[s.span.start..first.start];
        let tail = &self.text[value.span.end..s.span.end];
        let rest: Vec<(&str, Option<&Expr>)> = targets
            .iter()
            .enumerate()
            .filter(|(_, (n, _))| n != name)
            .map(|(k, (n, _))| (n.as_str(), parts.map(|ps| &ps[k])))
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
                format!("write {this} without `{name}`: `{head}{names} = {v}{tail}`")
            }
            _ => format!(
                "write {this} without `{name}`: `{head}{names} = …{tail}`, with the value of \
                 `{names}` alone in place of `…`"
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
        // Where the statement deleted carries `name` forward and the one kept has no keys, the
        // kept one gets `with carryForward`, so `name` stays carried (row "Two sentinel values
        // for one variable").
        let kept = |keep: &Stmt, drop: &Stmt| -> String {
            let carried = |s: &Stmt| initial_of(unwrapped(s).0).is_some_and(|i| i.carry);
            let keyless = initial_of(unwrapped(keep).0).is_some_and(|i| i.keys.is_empty());
            let written = self.text_of(keep.span);
            if carried(drop) && !carried(keep) && keyless {
                let head = written.strip_suffix(';').unwrap_or(written).trim_end();
                format!("`{head} with {CARRY_FORWARD};`, which now carries `{name}` forward")
            } else {
                format!("`{written}`")
            }
        };
        notes.push(Note {
            span: b.span,
            text: format!(
                "repair: keep the first, {}, and {}",
                kept(a, b),
                self.drop_name(b, name, "this one")
            ),
        });
        notes.push(Note {
            span: a.span,
            text: format!(
                "repair: keep the second, {}, and {}",
                kept(b, a),
                self.drop_name(a, name, "this one")
            ),
        });
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
                format!(" `initial {name} = e;` gives the entry `{name}[-1]`.")
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
