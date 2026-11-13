//! The `initial` statement (DESIGN.md sec:generations, step L6.1a): where it may stand, which
//! names it may give a value, what its value may read, and one sentinel value for each
//! variable. Each check is one of the rows of sec:diagnostics: "An `initial` statement outside
//! a loop, or under `local`", "An `initial` statement for a name the loop does not update",
//! "An `initial` value that reads a name of its own loop", "Two sentinel values for one
//! variable", "`with carryForward` on a keyed boundary entry", "A loop variable not updated on
//! every path of a step", "Collision" for a write the value of an indexed definition makes once
//! for each of several keys, and, for an entry written as a bare statement, "A boundary entry of a
//! loop written without `initial`". The forms the parser stops at, `with x = e`, `with initial x
//! = e` and `with x[-2] = e` on a statement of a loop, and the removed form `mutable x = e;`,
//! are found by the parser (`crate::parse`).

use std::collections::{HashMap, HashSet, VecDeque};

use num_bigint::BigInt;

use super::builder::{Builder, Level};
use super::sentinel::{End, Entry, Keys, Sentinels, keys_in, keys_of};
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
            exprs.extend(f.given.iter().flat_map(|t| &t.ports).map(|p| &p.value));
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
#[derive(Clone, Copy, PartialEq, Eq)]
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
#[derive(Clone, Copy, PartialEq, Eq)]
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
    collide: Option<Several<'e>>,
}

/// The repair of a [`DotCall`] whose method writes the next receiver: the call as written,
/// `c.bump(3)`; the call written with `*.`, `c*.bump(3)`; and the text the repair replaces, the
/// whole statement when the call is one's whole value, with what replaces it (`_ = c*.bump(3);`
/// in place of `c.bump(3);`, since a statement drops no declared result); the text whose update
/// counts as the call's, for [`Builder::covers`]: the call, or the statement before which the
/// repair makes it once; and the notes on the call written with `*.` inside code run once for
/// each of several keys ([`DotCall`]).
struct Fix {
    span: Span,
    branch: Option<Branch>,
    call: String,
    star: String,
    replaced: String,
    code: String,
    counts: Span,
    notes: Vec<Note>,
}

/// The repair of a write that gives each key of the scopes around it its own entry: the entry
/// written, `c[i]*.a()`; the text of the outermost such scope, and that text rewritten; the keys
/// as the repair names them, outermost first; and a note on each binder the repair renames.
struct Keyed {
    entry: String,
    base: Span,
    whole: String,
    keys: Vec<String>,
    hides: Vec<Note>,
}

/// What the messages of a loop's body read from the walk of its step: the `.` calls on
/// variables, the scopes, and the loop's node, the text of whose definition a new name of a
/// repair avoids.
struct Step<'c, 'e> {
    dots: &'c [DotCall<'e>],
    scopes: &'c [Scope<'e>],
    node: usize,
}

/// The new names the repairs of one message have given, and for each base the next suffix to
/// try.
#[derive(Default)]
struct Taken {
    names: HashSet<String>,
    next: HashMap<String, usize>,
}

/// A name `base1`, `base2`, … that no name of `used` and none of `taken` spells, added to
/// `taken`; `base` itself when `bare` and it is free.
// Complexity tradeoff: trying the suffixes from 1 each time costs O(k^2) for k new names of one
// base, as for k nested binders of one name that hide a key. Here each base keeps the suffix
// after the last it gave, since the names taken only grow: each suffix is tried once per base
// unless it is free, so the k names cost O(k + u) for the u names of `used` and `taken` that
// spell a suffix of the base.
fn fresh(base: &str, bare: bool, used: &HashSet<&str>, taken: &mut Taken) -> String {
    let free = |r: &str, names: &HashSet<String>| !used.contains(r) && !names.contains(r);
    let name = match bare && free(base, &taken.names) {
        true => base.to_string(),
        false => {
            let next = taken.next.entry(base.to_string()).or_insert(1);
            let (i, name) = (*next..)
                .map(|i| (i, format!("{base}{i}")))
                .find(|(_, r)| free(r, &taken.names))
                .expect("some suffix is free");
            *next = i + 1;
            name
        }
    };
    taken.names.insert(name.clone());
    name
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

/// What [`every_path`] finds in a step: the variables every path updates, each update, each `.`
/// call on a variable, and each write made several times by the value of an indexed definition.
struct Walk<'e> {
    must: Must<'e>,
    updates: Vec<Update<'e>>,
    dots: Vec<DotCall<'e>>,
    several: Vec<Several<'e>>,
    scopes: Vec<Scope<'e>>,
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

/// The words of the source text `t` that could be names: runs of letters, digits and `_` that
/// do not start with a digit.
fn identifiers(t: &str) -> impl Iterator<Item = &str> {
    t.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|w| w.chars().next().is_some_and(|c| !c.is_ascii_digit()))
}

/// How a part of a node combines into the node's [`Must`]: run on every path through the node,
/// one of several alternatives of which a path runs exactly one, or run on some paths only.
#[derive(Clone, Copy)]
enum Role {
    Always,
    Alt,
    Some,
}

/// The statement a node of the walk stands in: its span, the innermost construct whose part
/// holds the statement, and the innermost [`Scope`] around it.
#[derive(Clone, Copy)]
struct StmtAt {
    span: Span,
    branch: Option<Branch>,
    scope: Option<usize>,
}

/// Where a node of the walk of [`every_path`] stands: the innermost construct whose part holds
/// it; the innermost scope whose code runs once for each of several keys around it, an index
/// into the walk's [`Scope`] list; the innermost scope of any kind around it; the write whose
/// target's keys hold it, an index into its [`Write`] list; for the callee of a call or the
/// value before a `.`, the outermost call or member of the chain it heads (`c*.a().b()` for
/// `c*.a`); and the innermost statement around it.
#[derive(Clone, Copy)]
struct Ctx {
    branch: Option<Branch>,
    per: Option<usize>,
    scope: Option<usize>,
    key_of: Option<usize>,
    top: Option<Span>,
    stmt: Option<StmtAt>,
}

/// What binds the names of a [`Scope`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    /// An indexed definition, `d[i in 0..<2] = …`: its domains bind keys for its value.
    Def,
    /// A `for`, `for i in 0..<t { … }`: its binders bind each pass of its body.
    For,
    /// A lambda's parameters, a match arm's or `else`'s pattern, or a binding of a block,
    /// which binds its name for the statements after it.
    Other,
}

/// A domain of a [`Scope`] that may hold more than one key: the name it binds, the domain
/// written, and whether the keys of that domain are the passes of the scope's code, as for an
/// indexed definition's domain and a `for` with one binder, `for i in 0..<t`, so that a message
/// can count them.
struct Dom<'e> {
    name: &'e str,
    set: &'e Expr,
    exact: bool,
}

/// Code of a step inside which names are bound: what binds them; the names; the domains whose
/// keys make the code run once for each key, when they may hold more than one; the text shown
/// for it, `d[i in 0..<2] =` or `for i in 0..<t`, followed by `…` in a message; the runs of text
/// in which its names are bound, which a new name of a binder rewrites (the domains of a
/// definition, the defaults of a lambda and the value of a binding, read from outside, are left
/// out); the text a message shows
/// for it as a whole; the construct around its code (`for`, indexed definition) and the one it
/// stands in; the statement it is part of, before which a repair computes a write once; and
/// the nearest enclosing scope with domains and the enclosing scope.
struct Scope<'e> {
    kind: ScopeKind,
    binds: Vec<&'e str>,
    many: Vec<Dom<'e>>,
    head: Span,
    pieces: Vec<Span>,
    shown: Span,
    inner: Option<Branch>,
    outer: Option<Branch>,
    stmt: Option<StmtAt>,
    up: Option<usize>,
    parent: Option<usize>,
}

/// Whether the domain `set` may hold more than one key: any domain but one written with integer
/// literals that holds one key or none, `0..<1`.
fn many_keys(set: &Expr) -> bool {
    match keys_in(set) {
        None => false,
        Some(Keys::Ints(lo, End::At(hi))) => hi != lo,
        Some(_) => true,
    }
}

/// How a write in code run once for each of several keys is written.
#[derive(Clone, Copy)]
enum WriteForm<'e> {
    /// A `*.` call on `of`, `c` in `c*.a()`, whose chain is the span; or a `.` call on `of`,
    /// which writes nothing but would write `c'` as the `*.` call that repairs it.
    Call(&'e Expr),
    /// `c' = …`.
    Bind,
    /// `c'[v in …] = …`.
    Def,
}

/// A write of a variable inside code that runs once for each of several keys: the variable;
/// the write as shown, the chain of a `*.` call or the statement; its form; where a key `[i]`
/// would go after the variable's name in it; the innermost scope with such keys around it;
/// the names its target's keys read, each with the scope that binds it there; whether a key
/// holds a `*.` call, which the disjointness check of step L6.3 judges, so this check passes
/// the write over; the innermost scope and construct around it; and whether it is a `.` call,
/// listed for the repair of the call.
struct Write<'e> {
    name: &'e str,
    span: Span,
    form: WriteForm<'e>,
    insert: Option<usize>,
    per: usize,
    names: Vec<(&'e str, Option<usize>)>,
    all: bool,
    scope: Option<usize>,
    branch: Option<Branch>,
    dot: bool,
}

/// A write that the scope `scope` makes once for each key of its domain `dom`, since no key of
/// the write's target names that domain's binder: several writers of one fact in one step
/// (DESIGN.md sec:tour_methods, "Two `*.` chains on one receiver in one step are two
/// writers"). `only` tells whether `scope` is the only scope with several keys around the
/// write.
struct Several<'e> {
    write: Write<'e>,
    scope: usize,
    dom: usize,
    only: bool,
}

/// The writes of `writes` that write one fact once for each key of a scope around them, given
/// the scopes `scopes`. A write is checked against each scope with several keys out from its
/// own, until a domain of one is not named by its target: a key of the target that reads the
/// domain's binder, resolved to that scope, names it; one of the same name bound nearer does
/// not.
// Complexity tradeoff: walking every write out through every enclosing scope and all its
// domains is O(w (d + k)) for w writes under d scopes with k domains in all, O(n^2) for a step
// of n nodes with a write at each level of a deep nesting. Here each scope keeps its domains that
// may hold more than one key, filtered once; each name a write's target reads is resolved to its
// binder as the walk meets it; a write's names go into a set once; a write whose key holds a
// `*.` call is passed over (step L6.3 judges it); and the walk stops at the first domain the
// write does not name. Each domain the walk passes is named by a distinct pair of a name and a
// scope in the set, so the walk passes at most as many domains as the write's target reads
// names, and a step of n nodes costs O(n) expected.
fn several<'e>(writes: Vec<Write<'e>>, scopes: &[Scope<'e>]) -> Vec<Several<'e>> {
    let mut out = Vec::new();
    for w in writes {
        if w.all {
            continue;
        }
        if let Some((scope, dom)) = first_miss(&w, scopes) {
            out.push(Several {
                only: scope == w.per && scopes[scope].up.is_none(),
                scope,
                dom,
                write: w,
            });
        }
    }
    out
}

/// The first domain, out from the write `w`, of a scope with several keys that `w`'s target
/// does not name, as the scope and the domain's index ([`several`]).
fn first_miss(w: &Write, scopes: &[Scope]) -> Option<(usize, usize)> {
    misses(w, scopes, true).into_iter().next()
}

/// The domains, out from the write `w`, of the scopes with several keys that `w`'s target does
/// not name: the first only when `first`, otherwise all of them, inner first.
fn misses(w: &Write, scopes: &[Scope], first: bool) -> Vec<(usize, usize)> {
    let names: HashSet<(&str, Option<usize>)> = w.names.iter().copied().collect();
    let mut out = Vec::new();
    let mut at = Some(w.per);
    while let Some(p) = at {
        for (d, dom) in scopes[p].many.iter().enumerate() {
            if !names.contains(&(dom.name, Some(p))) {
                out.push((p, d));
                if first {
                    return out;
                }
            }
        }
        at = scopes[p].up;
    }
    out
}

/// The scopes from `from` out to `to`, `to` left out, each by its index: those around a node
/// and inside the one around a statement it stands in.
fn scopes_between(scopes: &[Scope], from: Option<usize>, to: Option<usize>) -> Vec<usize> {
    let mut out = Vec::new();
    let mut at = from;
    while let Some(s) = at
        && Some(s) != to
    {
        out.push(s);
        at = scopes[s].parent;
    }
    out
}

/// New names of binders, for a repair: for each name, the texts in which a scope binds it anew,
/// as runs of the source in order that do not overlap, each with the new name the innermost
/// such scope gives it there.
#[derive(Default)]
struct Renames<'e> {
    of: HashMap<&'e str, Vec<(Span, String)>>,
}

impl<'e> Renames<'e> {
    /// The renames of `pieces`, each a text of a scope that binds a name, with the name and its
    /// new name. The texts of the scopes that bind one name are nested or apart, so a sweep in
    /// order of start, with a stack of the texts open at each point, cuts them into runs that
    /// do not overlap, the innermost text giving each run its name.
    // Complexity tradeoff: a lookup that scans every renaming text around a word costs O(d) a
    // word for d nested scopes that bind one name, O(n d) over the text of a repair; the sort
    // and sweep here cost O(m log m) once for m texts, and each word is then a binary search,
    // O(log m).
    fn new(pieces: Vec<(&'e str, Span, String)>) -> Self {
        let mut by: HashMap<&'e str, Vec<(Span, String)>> = HashMap::new();
        for (n, s, new) in pieces {
            by.entry(n).or_default().push((s, new));
        }
        let mut of = HashMap::new();
        for (n, mut list) in by {
            list.sort_by_key(|(s, _)| (s.start, std::cmp::Reverse(s.end)));
            let mut runs: Vec<(Span, String)> = Vec::new();
            let mut open: Vec<(Span, String)> = Vec::new();
            let mut at = 0;
            let cut = |runs: &mut Vec<(Span, String)>, from: usize, to: usize, new: &str| {
                if from < to {
                    runs.push((
                        Span {
                            start: from,
                            end: to,
                        },
                        new.to_string(),
                    ));
                }
            };
            for (s, new) in list {
                while let Some((t, m)) = open.last()
                    && t.end <= s.start
                {
                    cut(&mut runs, at, t.end, m);
                    at = at.max(t.end);
                    open.pop();
                }
                if let Some((_, m)) = open.last() {
                    cut(&mut runs, at, s.start, m);
                }
                at = s.start;
                open.push((s, new));
            }
            while let Some((t, m)) = open.pop() {
                cut(&mut runs, at, t.end, &m);
                at = at.max(t.end);
            }
            of.insert(n, runs);
        }
        Renames { of }
    }

    /// The word `w` at offset `at` of the source as the repair writes it: its new name in the
    /// run around `at`, found by a binary search, or `w` outside them.
    fn word<'w>(&'w self, w: &'w str, at: usize) -> &'w str {
        let Some(runs) = self.of.get(w) else {
            return w;
        };
        match runs.partition_point(|(r, _)| r.start <= at) {
            0 => w,
            k if at < runs[k - 1].0.end => &runs[k - 1].1,
            _ => w,
        }
    }

    /// The source `text` from `from` to `to`, offsets of the source, with each word that could
    /// be a name written as [`Renames::word`] gives it; a word right after `.` or `#`, a member
    /// or an atom, is no name of a binder and is kept. Inside the parentheses of a call, a
    /// struct or an atom pattern, `f(i: 1)` or `#e(code: i)`, a word before `:` names a field
    /// and is kept, except a field written alone, `#e(i:)`, which binds its name: it is written
    /// `#e(i: i1)`. `open` holds, for each bracket open at `from`, whether it is such a
    /// parenthesis, one right after a name, and is kept up to date for the text that follows.
    fn apply(&self, text: &str, from: usize, to: usize, out: &mut String, open: &mut Vec<bool>) {
        let word = |c: char| c.is_alphanumeric() || c == '_';
        let mut at = from;
        while at < to {
            let rest = &text[at..to];
            let len = rest.find(|c| !word(c)).unwrap_or(rest.len());
            let w = &rest[..len];
            let before = &text[..at];
            let after_dot =
                before.ends_with('#') || before.ends_with('.') && !before.ends_with("..");
            let named = !w.is_empty() && !w.starts_with(|c: char| c.is_ascii_digit());
            let colon = rest[len..]
                .trim_start()
                .strip_prefix(':')
                .filter(|r| !r.starts_with([':', '=']));
            // The new name of a field written alone, written after its `:`.
            let mut alone = None;
            match (named && !after_dot, colon) {
                (true, Some(r)) if open.last() == Some(&true) => {
                    out.push_str(w);
                    let new = self.word(w, at);
                    if new != w && r.trim_start().starts_with([')', ',']) {
                        alone = Some(new);
                    }
                }
                (true, _) => out.push_str(self.word(w, at)),
                (false, _) => out.push_str(w),
            }
            let gap = rest[len..].find(word).map_or(rest.len(), |g| len + g);
            for (k, c) in rest[len..gap].char_indices() {
                match c {
                    '(' => {
                        open.push(text[..at + len + k].ends_with(|p: char| word(p) || p == '\''))
                    }
                    '[' | '{' => open.push(false),
                    ')' | ']' | '}' => {
                        open.pop();
                    }
                    _ => {}
                }
            }
            let between = &rest[len..gap];
            match (alone, between.find(':')) {
                (Some(new), Some(c)) => {
                    out.push_str(&between[..=c]);
                    out.push(' ');
                    out.push_str(new);
                    out.push_str(&between[c + 1..]);
                }
                _ => out.push_str(between),
            }
            at += gap;
        }
    }
}

/// A step of the walk of [`every_path`]: an expression or statement to visit, with where it
/// stands and its role in its parent; the combination of the last `kids` results into one,
/// with what the node itself updates; or the names of a [`Scope`] coming into view, or leaving
/// it, around the walk of its code.
enum Task<'e> {
    Expr(&'e Expr, Ctx, Role),
    Stmt(&'e Stmt, Ctx, Role),
    Join {
        kids: usize,
        own: Must<'e>,
        role: Role,
    },
    Enter(usize),
    Leave(usize),
}

/// Adds to `kids` the tasks `inner`, the code of the scope `scope`, between the tasks that
/// bring its names into view and take them out, in the order the work list pops them.
fn scoped<'e>(kids: &mut Vec<Task<'e>>, scope: usize, inner: impl IntoIterator<Item = Task<'e>>) {
    kids.push(Task::Leave(scope));
    kids.extend(inner);
    kids.push(Task::Enter(scope));
}

/// The context inside the scope `scope`, of the construct `branch`, opened at `ctx`.
fn inside_scope(ctx: Ctx, scope: usize, many: bool, branch: Option<Branch>) -> Ctx {
    Ctx {
        branch,
        per: if many { Some(scope) } else { ctx.per },
        scope: Some(scope),
        top: None,
        ..ctx
    }
}

/// The tasks of the statements `stmts` of a block whose text ends at `end`, in the order the
/// work list pops them: written order, with a [`Scope`] for each statement that binds a name,
/// `i = 0;` or `d[k in …] = …`, which holds its names from that statement to the end of the
/// block (a name is declared before it is used, so no statement before it reads it).
fn block<'e>(
    stmts: &'e [Stmt],
    mut ctx: Ctx,
    end: usize,
    scopes: &mut Vec<Scope<'e>>,
) -> Vec<Task<'e>> {
    let mut seq = Vec::with_capacity(stmts.len());
    let mut opened = Vec::new();
    for s in stmts {
        seq.push(Task::Stmt(s, ctx, Role::Always));
        // The names bound, the text of each where it is bound, and the value, which reads the
        // names from before the statement.
        let d = unwrapped(s).0;
        let (bound, value): (Vec<(&str, Span)>, &Expr) = match &d.kind {
            StmtKind::Bind { targets, value } => (
                (targets.iter())
                    .filter_map(|t| match t {
                        Target::Name(n, at) if !n.ends_with('\'') => Some((n.as_str(), *at)),
                        _ => None,
                    })
                    .collect(),
                value,
            ),
            StmtKind::IndexedDef(x) if !x.name.ends_with('\'') => {
                let at = Span {
                    start: d.span.start,
                    end: d.span.start + x.name.len(),
                };
                (vec![(x.name.as_str(), at)], &x.value)
            }
            _ => continue,
        };
        let binds: Vec<&str> = bound.iter().map(|&(n, _)| n).collect();
        let mut pieces: Vec<Span> = bound.iter().map(|&(_, at)| at).collect();
        pieces.push(Span {
            start: s.span.end,
            end,
        });
        if binds.is_empty() {
            continue;
        }
        scopes.push(Scope {
            kind: ScopeKind::Other,
            binds,
            many: Vec::new(),
            head: Span {
                start: s.span.start,
                end: value.span.start,
            },
            pieces,
            shown: s.span,
            inner: ctx.branch,
            outer: ctx.branch,
            stmt: None,
            up: ctx.per,
            parent: ctx.scope,
        });
        let id = scopes.len() - 1;
        seq.push(Task::Enter(id));
        opened.push(id);
        ctx.scope = Some(id);
    }
    seq.extend(opened.into_iter().rev().map(Task::Leave));
    seq.reverse();
    seq
}

/// The number of tasks of `kids` that leave a result.
fn results_of(kids: &[Task]) -> usize {
    (kids.iter())
        .filter(|t| matches!(t, Task::Expr(..) | Task::Stmt(..)))
        .count()
}

/// Adds to `kids` the walk of the receiver `of` of a call: the keys on its path, as keys of the
/// write `keys.key_of`, and the value the path starts at, as any value.
fn receiver_kids<'e>(of: &'e Expr, keys: Ctx, plain: Ctx, kids: &mut Vec<Task<'e>>) {
    let mut base: &'e Expr = of;
    loop {
        match &base.kind {
            ExprKind::Index(a, k) => {
                kids.push(Task::Expr(k, keys, Role::Always));
                base = a;
            }
            ExprKind::Member { of: a, .. } => base = a,
            _ => break,
        }
    }
    kids.push(Task::Expr(base, plain, Role::Always));
}

/// Lists a `.` call `e` on the variable `name` through the receiver `of`, at `ctx`, inside code
/// run once for each of several keys, as the write its `*.` repair would make, with the keys on
/// its path; and adds to `kids` the walk of the receiver.
fn dot_write<'e>(
    writes: &mut Vec<Write<'e>>,
    e: &'e Expr,
    of: &'e Expr,
    name: &'e str,
    ctx: Ctx,
    kids: &mut Vec<Task<'e>>,
) {
    let plain = Ctx { top: None, ..ctx };
    let Some(per) = ctx.per else {
        kids.push(Task::Expr(of, plain, Role::Always));
        return;
    };
    let keys = Ctx {
        key_of: Some(writes.len()),
        ..plain
    };
    writes.push(Write {
        name,
        span: e.span,
        form: WriteForm::Call(of),
        insert: Some(key_place(of)),
        per,
        names: Vec::new(),
        all: false,
        scope: ctx.scope,
        branch: ctx.branch,
        dot: true,
    });
    receiver_kids(of, keys, plain, kids);
}

/// Where a key `[i]` for each key of a scope goes in the receiver `of`: after the path's last
/// index, or after its variable: `c[i]`, `grid[0][i]`, `p[i].pos`, `grid[j][i].pos`.
fn key_place(of: &Expr) -> usize {
    let mut end = of;
    while let ExprKind::Member { of: a, .. } = &end.kind {
        end = a;
    }
    end.span.end
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
/// whose span is in `counted` is taken as an update of the variable it maps to, as it would be
/// written with `*.`, and so is a statement whose span is in `counted`, as the call would be
/// computed once before it, to ask whether rewriting those calls would complete every path
/// (empty but on a rejection).
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
//
// The same walk lists the writes made inside code run once for each of several keys, the value
// of an indexed definition or the body of a `for`, with the names their targets' keys read,
// for [`several`]. Each name is resolved to its binder as the walk meets it: the walk keeps,
// for each name, the stack of scopes that bind it around the node, pushed on entering a scope
// and popped on leaving it, so a resolution is one hash lookup and each scope costs its names
// twice: O(n) for a step of n nodes. Resolving each name by walking out through the scopes
// around it would cost O(depth) a name, O(n^2) for a deep nesting (CHK-for-body-writers).
fn every_path<'e>(
    stmts: &'e [Stmt],
    qualifiers: &HashSet<&str>,
    counted: &HashMap<Span, &'e str>,
) -> Walk<'e> {
    let mut updates = Vec::new();
    let mut dots: Vec<DotCall<'e>> = Vec::new();
    // The statements whose whole value is a call or a member read, by the span of the value.
    let mut whole: HashMap<Span, &'e Stmt> = HashMap::new();
    // The expressions whose value is dropped: the value of an expression statement, and each
    // branch, arm and export of one whose value is dropped.
    let mut dropped: HashSet<Span> = HashSet::new();
    let mut scopes: Vec<Scope<'e>> = Vec::new();
    // For each name, the scopes around the node being walked that bind it, innermost last.
    let mut env: HashMap<&'e str, Vec<usize>> = HashMap::new();
    let mut writes: Vec<Write<'e>> = Vec::new();
    let mut results: Vec<(Role, Must<'e>)> = Vec::new();
    let start = Ctx {
        branch: None,
        per: None,
        scope: None,
        key_of: None,
        top: None,
        stmt: None,
    };
    let end = stmts.last().map_or(0, |s| s.span.end);
    let mut tasks: Vec<Task<'e>> = vec![Task::Join {
        kids: stmts.len(),
        own: Must::none(),
        role: Role::Always,
    }];
    tasks.extend(block(stmts, start, end, &mut scopes));
    while let Some(task) = tasks.pop() {
        match task {
            Task::Enter(s) => {
                for &n in &scopes[s].binds {
                    env.entry(n).or_default().push(s);
                }
            }
            Task::Leave(s) => {
                for &n in &scopes[s].binds {
                    if let Some(v) = env.get_mut(n) {
                        v.pop();
                    }
                }
            }
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
            Task::Stmt(s, ctx, role) => {
                // The variables the statement itself updates, and its parts.
                let mut own: HashSet<&'e str> = HashSet::new();
                let mut kids: Vec<Task<'e>> = Vec::new();
                if let Some(&n) = counted.get(&s.span) {
                    own.insert(n);
                }
                if let StmtKind::Bind { value: v, .. } | StmtKind::Expr(v) = &s.kind
                    && matches!(v.kind, ExprKind::Call { .. } | ExprKind::Member { .. })
                {
                    whole.insert(v.span, s);
                }
                if let StmtKind::Expr(v) = &s.kind {
                    dropped.insert(v.span);
                }
                let at = StmtAt {
                    span: s.span,
                    branch: ctx.branch,
                    scope: ctx.scope,
                };
                let plain = Ctx {
                    top: None,
                    stmt: Some(at),
                    ..ctx
                };
                let mut always = |x: &'e Expr| kids.push(Task::Expr(x, plain, Role::Always));
                match &s.kind {
                    StmtKind::Bind { targets, value } => {
                        for t in targets {
                            if let Target::Name(n, tat) = t
                                && n.ends_with('\'')
                            {
                                own.insert(unprimed(n));
                                if let Some(per) = ctx.per {
                                    writes.push(Write {
                                        name: unprimed(n),
                                        span: s.span,
                                        form: WriteForm::Bind,
                                        insert: Some(tat.end),
                                        per,
                                        names: Vec::new(),
                                        all: false,
                                        scope: ctx.scope,
                                        branch: ctx.branch,
                                        dot: false,
                                    });
                                }
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
                        let call = match &d.value.kind {
                            ExprKind::Call { callee, .. } => callee,
                            _ => &d.value,
                        };
                        if let ExprKind::Spread { of, .. } = &call.kind
                            && let Some((n, true)) = receiver(of, qualifiers)
                        {
                            own.insert(n);
                        }
                        for k in &d.keys {
                            if let IndexKey::In { set, .. } = k {
                                always(set);
                            }
                        }
                        for k in d.boundary.iter().flat_map(|b| &b.keys) {
                            match k {
                                IndexKey::In { set, .. } => always(set),
                                IndexKey::At(e) => always(e),
                            }
                        }
                        d.boundary.iter().for_each(|b| always(&b.value));
                        // The names the domains bind, for the value and the target's keys.
                        let binds: Vec<&'e str> = (d.keys.iter())
                            .filter_map(|k| match k {
                                IndexKey::In { name, .. } => Some(name.as_str()),
                                IndexKey::At(_) => None,
                            })
                            .collect();
                        let many: Vec<Dom<'e>> = (d.keys.iter())
                            .filter_map(|k| match k {
                                IndexKey::In { name, set } if many_keys(set) => Some(Dom {
                                    name,
                                    set,
                                    exact: true,
                                }),
                                _ => None,
                            })
                            .collect();
                        let has_many = !many.is_empty();
                        let indexed = Some(Branch {
                            span: s.span,
                            what: Construct::Indexed,
                        });
                        // The text where the domains bind their names: all but the domains.
                        let mut pieces = Vec::new();
                        let mut from = s.span.start;
                        for k in &d.keys {
                            if let IndexKey::In { set, .. } = k {
                                pieces.push(Span {
                                    start: from,
                                    end: set.span.start,
                                });
                                from = set.span.end;
                            }
                        }
                        pieces.push(Span {
                            start: from,
                            end: d.value.span.end,
                        });
                        let scope = (!binds.is_empty()).then(|| {
                            scopes.push(Scope {
                                kind: ScopeKind::Def,
                                binds: binds.clone(),
                                many,
                                head: Span {
                                    start: s.span.start,
                                    end: d.value.span.start,
                                },
                                pieces,
                                shown: s.span,
                                inner: indexed,
                                outer: ctx.branch,
                                stmt: Some(at),
                                up: ctx.per,
                                parent: ctx.scope,
                            });
                            scopes.len() - 1
                        });
                        // A definition of a primed name inside code run once for each of several
                        // keys writes one entry for each of its keys, which its target names:
                        // the names of its domains and those its written keys read.
                        let mut keys = plain;
                        if d.name.ends_with('\'') {
                            own.insert(unprimed(&d.name));
                            if let Some(per) = ctx.per {
                                keys.key_of = Some(writes.len());
                                writes.push(Write {
                                    name: unprimed(&d.name),
                                    span: s.span,
                                    form: WriteForm::Def,
                                    insert: None,
                                    per,
                                    names: binds.iter().map(|&n| (n, scope)).collect(),
                                    all: false,
                                    scope: scope.or(ctx.scope),
                                    branch: ctx.branch,
                                    dot: false,
                                });
                            }
                        }
                        // The written keys and the value read the names of the domains.
                        let at_keys = (d.keys.iter()).filter_map(|k| match k {
                            IndexKey::At(e) => Some(Task::Expr(e, keys, Role::Always)),
                            IndexKey::In { .. } => None,
                        });
                        match scope {
                            Some(sc) => {
                                let value = inside_scope(plain, sc, has_many, indexed);
                                let value = Task::Expr(&d.value, value, Role::Some);
                                scoped(&mut kids, sc, at_keys.chain([value]));
                            }
                            None => {
                                kids.extend(at_keys);
                                let value = Ctx {
                                    branch: indexed,
                                    ..plain
                                };
                                kids.push(Task::Expr(&d.value, value, Role::Some));
                            }
                        }
                    }
                    StmtKind::Local(d) | StmtKind::Annotated { decl: d, .. } => {
                        tasks.push(Task::Stmt(d, ctx, role));
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
                    branch: ctx.branch,
                }));
                let own = Must::Names(own);
                if kids.is_empty() {
                    results.push((role, own));
                } else {
                    tasks.push(Task::Join {
                        kids: results_of(&kids),
                        own,
                        role,
                    });
                    tasks.append(&mut kids);
                }
            }
            Task::Expr(e, ctx, role) => {
                let gone = dropped.contains(&e.span);
                let plain = Ctx { top: None, ..ctx };
                let inside = |what| Ctx {
                    branch: Some(Branch { span: e.span, what }),
                    ..plain
                };
                // The callee of a call and the value before a `.` stand in the chain of the
                // outermost call or member around them.
                let chain = Ctx {
                    top: ctx.top.or(Some(e.span)),
                    ..ctx
                };
                let mut own = Must::none();
                let mut kids: Vec<Task<'e>> = Vec::new();
                match &e.kind {
                    ExprKind::Int { .. }
                    | ExprKind::Float { .. }
                    | ExprKind::Rat(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Atom(_)
                    | ExprKind::This
                    | ExprKind::Section(_)
                    | ExprKind::Loop { .. } => {}
                    ExprKind::Name(n) => {
                        if let Some(w) = ctx.key_of {
                            let at = env.get(n.as_str()).and_then(|v| v.last().copied());
                            writes[w].names.push((n, at));
                        }
                    }
                    ExprKind::Str(parts) => {
                        for p in parts {
                            if let StrPart::Hole(x) = p {
                                kids.push(Task::Expr(x, plain, Role::Always));
                            }
                        }
                    }
                    ExprKind::Spread { of, .. } => {
                        if let Some(w) = ctx.key_of {
                            writes[w].all = true;
                        }
                        match (receiver(of, qualifiers), ctx.per) {
                            (Some((n, _)), per) => {
                                own = Must::Names(HashSet::from([n]));
                                updates.push(Update {
                                    name: n,
                                    span: e.span,
                                    branch: ctx.branch,
                                });
                                match per {
                                    // The keys on the path of the receiver are the keys of the
                                    // entry it writes; the variable is read as any value is.
                                    Some(per) => {
                                        let keys = Ctx {
                                            key_of: Some(writes.len()),
                                            ..plain
                                        };
                                        writes.push(Write {
                                            name: n,
                                            span: ctx.top.unwrap_or(e.span),
                                            form: WriteForm::Call(of),
                                            insert: Some(key_place(of)),
                                            per,
                                            names: Vec::new(),
                                            all: false,
                                            scope: ctx.scope,
                                            branch: ctx.branch,
                                            dot: false,
                                        });
                                        receiver_kids(of, keys, plain, &mut kids);
                                    }
                                    None => kids.push(Task::Expr(of, plain, Role::Always)),
                                }
                            }
                            (None, _) => kids.push(Task::Expr(of, plain, Role::Always)),
                        }
                    }
                    ExprKind::Break(a) => {
                        own = Must::All;
                        kids.push(Task::Expr(a, plain, Role::Always));
                    }
                    ExprKind::Member {
                        of,
                        name: method,
                        safe: false,
                    } if receiver(of, qualifiers).is_some() => {
                        let (name, _) = receiver(of, qualifiers).expect("matched by the guard");
                        if counted.get(&e.span) == Some(&name) {
                            own = Must::Names(HashSet::from([name]));
                        }
                        dots.push(DotCall {
                            name,
                            method,
                            span: e.span,
                            of_end: of.span.end,
                            bare: matches!(of.kind, ExprKind::Name(_)),
                            branch: ctx.branch,
                            stmt: whole.get(&e.span).copied(),
                            dropped: gone,
                            collide: None,
                        });
                        dot_write(&mut writes, e, of, name, ctx, &mut kids);
                    }
                    ExprKind::Member { of: a, .. } => {
                        kids.push(Task::Expr(a, chain, Role::Always));
                    }
                    ExprKind::Unary(_, a)
                    | ExprKind::Is { of: a, .. }
                    | ExprKind::Read { of: a, .. } => kids.push(Task::Expr(a, plain, Role::Always)),
                    ExprKind::SortKey { key, .. } => {
                        if let Some(k) = key {
                            kids.push(Task::Expr(k, plain, Role::Always));
                        }
                    }
                    ExprKind::Binary(op @ (BinaryOp::And | BinaryOp::Or), a, b) => {
                        let what = if *op == BinaryOp::And {
                            Construct::And
                        } else {
                            Construct::Or
                        };
                        kids.push(Task::Expr(a, plain, Role::Always));
                        kids.push(Task::Expr(b, inside(what), Role::Some));
                    }
                    ExprKind::Binary(_, a, b)
                    | ExprKind::Index(a, b)
                    | ExprKind::In { of: a, set: b, .. }
                    | ExprKind::Reduce { of: a, op: b } => {
                        kids.push(Task::Expr(a, plain, Role::Always));
                        kids.push(Task::Expr(b, plain, Role::Always));
                    }
                    ExprKind::Else {
                        of,
                        pattern,
                        default,
                    } => {
                        kids.push(Task::Expr(of, plain, Role::Always));
                        let b = inside(Construct::Else);
                        let mut binds = HashSet::new();
                        if let Some(p) = pattern {
                            pattern_names(p, &mut binds);
                        }
                        match pattern {
                            Some(p) if !binds.is_empty() => {
                                scopes.push(Scope {
                                    kind: ScopeKind::Other,
                                    binds: binds.into_iter().collect(),
                                    many: Vec::new(),
                                    head: Span {
                                        start: p.span().start,
                                        end: default.span.start,
                                    },
                                    pieces: vec![Span {
                                        start: p.span().start,
                                        end: default.span.end,
                                    }],
                                    shown: e.span,
                                    inner: b.branch,
                                    outer: ctx.branch,
                                    stmt: ctx.stmt,
                                    up: ctx.per,
                                    parent: ctx.scope,
                                });
                                let sc = scopes.len() - 1;
                                let ins = inside_scope(plain, sc, false, b.branch);
                                scoped(&mut kids, sc, [Task::Expr(default, ins, Role::Some)]);
                            }
                            _ => kids.push(Task::Expr(default, b, Role::Some)),
                        }
                    }
                    ExprKind::Call {
                        callee,
                        positional,
                        named,
                        ..
                    } => {
                        // A `.` call is recorded with the span of the whole call, its arguments
                        // included; its member read, the callee, is not recorded again, and its
                        // receiver is walked in its place.
                        for x in positional.iter().chain(named.iter().map(|(_, x)| x)) {
                            kids.push(Task::Expr(x, plain, Role::Always));
                        }
                        match &callee.kind {
                            ExprKind::Member {
                                of,
                                name: method,
                                safe: false,
                            } if receiver(of, qualifiers).is_some() => {
                                let (name, _) =
                                    receiver(of, qualifiers).expect("matched by the guard");
                                if counted.get(&e.span) == Some(&name) {
                                    own = Must::Names(HashSet::from([name]));
                                }
                                dots.push(DotCall {
                                    name,
                                    method,
                                    span: e.span,
                                    of_end: of.span.end,
                                    bare: matches!(of.kind, ExprKind::Name(_)),
                                    branch: ctx.branch,
                                    stmt: whole.get(&e.span).copied(),
                                    dropped: gone,
                                    collide: None,
                                });
                                dot_write(&mut writes, e, of, name, ctx, &mut kids);
                            }
                            _ => kids.push(Task::Expr(callee, chain, Role::Always)),
                        }
                    }
                    ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => {
                        kids.extend(es.iter().map(|x| Task::Expr(x, plain, Role::Always)));
                    }
                    ExprKind::Map(entries) => {
                        for (k, v) in entries {
                            kids.push(Task::Expr(k, plain, Role::Always));
                            kids.push(Task::Expr(v, plain, Role::Always));
                        }
                    }
                    ExprKind::Range(from, to) => {
                        kids.push(Task::Expr(from, plain, Role::Always));
                        match to {
                            RangeEnd::Below(b) | RangeEnd::Through(b) => {
                                kids.push(Task::Expr(b, plain, Role::Always))
                            }
                            RangeEnd::Open => {}
                        }
                    }
                    // The binders of a `for` bind each pass of its body: a bare name the value of
                    // the source, which for a range or a set is its key, and a deeper pattern each
                    // level's key and, last, the value (`for k -> v in m`).
                    ExprKind::For {
                        binders,
                        source,
                        guard,
                        body,
                    } => {
                        kids.push(Task::Expr(source, plain, Role::Always));
                        let b = inside(Construct::For);
                        let binds: Vec<&'e str> = (binders.iter())
                            .filter_map(|t| match t {
                                Target::Name(n, _) => Some(n.as_str()),
                                Target::Wild => None,
                            })
                            .collect();
                        let levels = match binders.len() {
                            1 => &binders[..],
                            k => &binders[..k - 1],
                        };
                        let many: Vec<Dom<'e>> = match levels {
                            [Target::Name(n, _)] if binders.len() == 1 => (many_keys(source))
                                .then_some(Dom {
                                    name: n,
                                    set: source,
                                    exact: true,
                                })
                                .into_iter()
                                .collect(),
                            _ => (levels.iter())
                                .filter_map(|t| match t {
                                    Target::Name(n, _) => Some(Dom {
                                        name: n,
                                        set: source,
                                        exact: false,
                                    }),
                                    Target::Wild => None,
                                })
                                .collect(),
                        };
                        let parts = guard.iter().map(|g| &**g).chain([&**body]);
                        if binds.is_empty() {
                            kids.extend(parts.map(|x| Task::Expr(x, b, Role::Some)));
                        } else {
                            let has_many = !many.is_empty();
                            scopes.push(Scope {
                                kind: ScopeKind::For,
                                binds,
                                many,
                                head: Span {
                                    start: e.span.start,
                                    end: body.span.start,
                                },
                                pieces: vec![
                                    Span {
                                        start: e.span.start,
                                        end: source.span.start,
                                    },
                                    Span {
                                        start: source.span.end,
                                        end: e.span.end,
                                    },
                                ],
                                shown: e.span,
                                inner: b.branch,
                                outer: ctx.branch,
                                stmt: ctx.stmt,
                                up: ctx.per,
                                parent: ctx.scope,
                            });
                            let sc = scopes.len() - 1;
                            let ins = inside_scope(plain, sc, has_many, b.branch);
                            let inner = parts.map(|x| Task::Expr(x, ins, Role::Some));
                            scoped(&mut kids, sc, inner);
                        }
                    }
                    ExprKind::Lambda { params, body } => {
                        let b = inside(Construct::Lambda);
                        kids.extend(
                            params
                                .iter()
                                .filter_map(|p| p.default.as_ref())
                                .map(|d| Task::Expr(d, b, Role::Some)),
                        );
                        // The parameters bind their names in all of the lambda's text but the
                        // defaults.
                        let mut pieces = Vec::new();
                        let mut from = e.span.start;
                        for d in params.iter().filter_map(|p| p.default.as_ref()) {
                            pieces.push(Span {
                                start: from,
                                end: d.span.start,
                            });
                            from = d.span.end;
                        }
                        pieces.push(Span {
                            start: from,
                            end: e.span.end,
                        });
                        let mut binds: Vec<&'e str> = Vec::new();
                        for p in params {
                            binds.push(&p.name);
                            for t in p.tuple.iter().flatten() {
                                if let Target::Name(n, _) = t {
                                    binds.push(n);
                                }
                            }
                        }
                        scopes.push(Scope {
                            kind: ScopeKind::Other,
                            binds,
                            many: Vec::new(),
                            head: Span {
                                start: e.span.start,
                                end: body.span.start,
                            },
                            pieces,
                            shown: e.span,
                            inner: b.branch,
                            outer: ctx.branch,
                            stmt: ctx.stmt,
                            up: ctx.per,
                            parent: ctx.scope,
                        });
                        let sc = scopes.len() - 1;
                        let ins = inside_scope(plain, sc, false, b.branch);
                        scoped(&mut kids, sc, [Task::Expr(body, ins, Role::Some)]);
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
                        kids.extend(block(stmts, plain, e.span.end, &mut scopes));
                    }
                    ExprKind::Match { of, arms } => {
                        kids.push(Task::Expr(of, plain, Role::Always));
                        let b = inside(Construct::Match);
                        for a in arms {
                            if gone {
                                dropped.insert(a.body.span);
                            }
                            let mut binds = HashSet::new();
                            pattern_names(&a.pattern, &mut binds);
                            let (ctx_a, sc) = if binds.is_empty() {
                                (b, None)
                            } else {
                                scopes.push(Scope {
                                    kind: ScopeKind::Other,
                                    binds: binds.into_iter().collect(),
                                    many: Vec::new(),
                                    head: Span {
                                        start: a.span.start,
                                        end: a.body.span.start,
                                    },
                                    pieces: vec![a.span],
                                    shown: a.span,
                                    inner: b.branch,
                                    outer: ctx.branch,
                                    stmt: ctx.stmt,
                                    up: ctx.per,
                                    parent: ctx.scope,
                                });
                                let sc = scopes.len() - 1;
                                (inside_scope(plain, sc, false, b.branch), Some(sc))
                            };
                            let mut inner: Vec<Task<'e>> = (a.guard.iter())
                                .map(|g| Task::Expr(g, ctx_a, Role::Some))
                                .collect();
                            inner.push(Task::Expr(&a.body, ctx_a, Role::Alt));
                            match sc {
                                Some(sc) => scoped(&mut kids, sc, inner),
                                None => kids.extend(inner),
                            }
                        }
                    }
                    ExprKind::Record(fields) => kids.extend(
                        fields
                            .iter()
                            .map(|(_, x)| Task::Expr(x, plain, Role::Always)),
                    ),
                    ExprKind::With { of, updates } => {
                        kids.push(Task::Expr(of, plain, Role::Always));
                        kids.extend(
                            (updates.iter()).map(|u| Task::Expr(&u.value, plain, Role::Always)),
                        );
                    }
                    ExprKind::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        kids.push(Task::Expr(cond, plain, Role::Always));
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
                        kids: results_of(&kids),
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
    // The writes of `.` calls go to the calls, for their repair; the others are the step's.
    let mut several_writes = Vec::new();
    let at: HashMap<Span, usize> = (dots.iter().enumerate())
        .map(|(i, d)| (d.span, i))
        .collect();
    for s in several(writes, &scopes) {
        if !s.write.dot {
            several_writes.push(s);
        } else if let Some(&i) = at.get(&s.write.span) {
            dots[i].collide = Some(s);
        }
    }
    Walk {
        must,
        updates,
        dots,
        several: several_writes,
        scopes,
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
        node: usize,
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
            several,
            scopes,
        } = every_path(stmts, self.qualifiers, &HashMap::new());
        let step = Step {
            dots: &dots,
            scopes: &scopes,
            node,
        };
        let updated: HashSet<&str> = updates.iter().map(|u| u.name).collect();
        if sites {
            self.initial_sites(label, at, stmts, &updated, &locals, &step)?;
        }
        // A write made once for each key of an indexed definition is several writers, whether
        // or not the variable is carried; it is reported before a path without an update.
        if let Some(first) = several.iter().min_by_key(|w| w.write.span.start) {
            return Err(self.several_writers(first, &step));
        }
        let Must::Names(must) = must else {
            return Ok(());
        };
        updates.sort_by_key(|u| u.span.start);
        match (updates.iter()).find(|u| !must.contains(u.name) && !carried.contains(u.name)) {
            Some(first) => {
                let name = first.name;
                let of_name: Vec<&Update> = updates.iter().filter(|u| u.name == name).collect();
                Err(self.not_every_path(name, &of_name, stmts, at, &step))
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
        step: &Step,
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
                        return Err(self.not_updated(s, n, at, stmts, step));
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

    /// The names written in the text of the item around the node `n`, the loop: a new name of a
    /// repair avoids them all, so it names nothing the loop's body or the code around it reads.
    /// One climb from `n` to the item and one pass over the item's text, O(n) for an item of n
    /// characters, made once for a rejection. A loop inside a string hole, whose tree is the
    /// hole's, takes the names of the whole text.
    fn names_around(&self, n: usize) -> HashSet<&str> {
        let root = self.tree.root;
        let mut k = n;
        let mut item = None;
        if self.tree.name(root) == "Unit" {
            while let Some(p) = self.parent(k) {
                if p == root {
                    item = Some(self.span(k));
                    break;
                }
                k = p;
            }
        }
        identifiers(item.map_or(self.text, |s| self.text_of(s))).collect()
    }

    /// The target of the write `w` as written, `c'`, or `grid'[0]` for an entry.
    fn written_target(&self, w: &Write) -> String {
        let name = w.name;
        match w.form {
            WriteForm::Call(of) => {
                let t = self.text_of(of.span);
                match t.strip_prefix(name) {
                    Some(rest) if !rest.starts_with('\'') => format!("{name}'{rest}"),
                    _ => t.to_string(),
                }
            }
            WriteForm::Bind | WriteForm::Def => format!("{name}'"),
        }
    }

    /// The text of `span` with the edits `edits`, each a run of the source replaced by a text,
    /// in order, that lie inside it, and each word between them written as `renames` gives it.
    fn rewrite(&self, span: Span, edits: &[(usize, usize, String)], renames: &Renames) -> String {
        let mut out = String::new();
        let mut open = Vec::new();
        let mut at = span.start;
        for (a, b, t) in edits
            .iter()
            .filter(|e| span.start <= e.0 && e.1 <= span.end)
        {
            renames.apply(self.text, at, *a, &mut out, &mut open);
            out.push_str(t);
            at = *b;
        }
        renames.apply(self.text, at, span.end, &mut out, &mut open);
        out
    }

    /// That the scope of `s` makes the write `subject` once for each key of its domain:
    /// "`c*.a()` writes `c'`, and `d[i in 0..<2] = …` computes its value once for each key of
    /// `i` in `0..<2`, so `c'` is written twice in one step".
    fn several_text(&self, s: &Several, scopes: &[Scope], subject: &str, would: bool) -> String {
        let sc = &scopes[s.scope];
        let dom = &sc.many[s.dom];
        let target = self.written_target(&s.write);
        let lhs = self.text_of(sc.head).trim_end();
        let runs = match sc.kind {
            ScopeKind::Def => "computes its value",
            _ => "runs its body",
        };
        let times = match keys_in(dom.set).filter(|_| dom.exact) {
            Some(Keys::Ints(lo, End::At(hi))) if hi.clone() - lo.clone() == BigInt::from(1) => {
                "twice".to_string()
            }
            Some(Keys::Ints(lo, End::At(hi))) => format!("{} times", hi - lo + 1),
            _ => "once for each key".to_string(),
        };
        let (writes, is) = match would {
            true => ("would write", "would be"),
            false => ("writes", "is"),
        };
        format!(
            "`{subject}` {writes} `{target}`, and `{lhs} …` {runs} once for each key of `{}` in \
             `{}`, so `{target}` {is} written {times} in one step",
            dom.name,
            self.text_of(dom.set.span)
        )
    }

    /// The repair of the write `w` that gives each key of the scopes around it that its target
    /// does not name its own entry: `c[i]*.a()`, `c'[i] = …`, `c'[i][v in …] = …`, with
    /// `extra` edits besides, in the text of the statement of the outermost such scope. A scope between the
    /// write and the one whose key it names that binds a name of that key hides it; the repair
    /// gives that scope's binder a new name, which avoids `used` and `taken`, and a note says so.
    // Complexity tradeoff: matching each binder of each scope on the way out against each key
    // still to come costs O(s k) for s scopes and k keys; here the keys still to come are kept
    // by name, each a queue in order out, so each binder is one lookup and the climb costs
    // O(s + k + b) for b binders, and the rewrite O(m log m) for the m runs it renames (row
    // CHK-for-body-writers).
    fn keyed(
        &self,
        w: &Write,
        scopes: &[Scope],
        used: &HashSet<&str>,
        taken: &mut Taken,
        extra: Vec<(usize, usize, String)>,
    ) -> Option<Keyed> {
        let at = match w.form {
            WriteForm::Def => {
                let primed = format!("{}'", w.name);
                (self.text_of(w.span).starts_with(&primed)).then(|| w.span.start + primed.len())
            }
            _ => w.insert,
        }?;
        let misses = misses(w, scopes, false);
        let outer = misses.last()?.0;
        // For each name, the keys further out that read it, as indices into `misses`.
        let mut pending: HashMap<&str, VecDeque<usize>> = HashMap::new();
        for (i, &(p, d)) in misses.iter().enumerate() {
            pending
                .entry(scopes[p].many[d].name)
                .or_default()
                .push_back(i);
        }
        let mut pieces = Vec::new();
        let mut new_of: HashMap<(usize, &str), String> = HashMap::new();
        let mut hides = Vec::new();
        let mut q = w.scope;
        while let Some(qi) = q {
            let sq = &scopes[qi];
            for (p, d) in misses.iter().filter(|m| m.0 == qi) {
                if let Some(v) = pending.get_mut(scopes[*p].many[*d].name) {
                    v.pop_front();
                }
            }
            for &n in &sq.binds {
                let Some(&i) = pending.get(n).and_then(|v| v.front()) else {
                    continue;
                };
                let new = fresh(n, false, used, taken);
                pieces.extend(sq.pieces.iter().map(|&r| (n, r, new.clone())));
                let far = self.text_of(scopes[misses[i].0].head).trim_end();
                hides.push(Note {
                    span: sq.shown,
                    text: format!(
                        "the `{n}` of `{} …` hides the `{n}` of `{far} …`, so the write names \
                         only the nearer one; the repair names it `{new}`",
                        self.text_of(sq.head).trim_end()
                    ),
                });
                new_of.insert((qi, n), new);
            }
            if qi == outer {
                break;
            }
            q = sq.parent;
        }
        let keys: Vec<String> = (misses.iter().rev())
            .map(|&(p, d)| {
                let n = scopes[p].many[d].name;
                new_of
                    .get(&(p, n))
                    .cloned()
                    .unwrap_or_else(|| n.to_string())
            })
            .collect();
        let mut edits = extra;
        edits.push((at, at, keys.iter().map(|k| format!("[{k}]")).collect()));
        edits.sort_by_key(|e| (e.0, e.1));
        let renames = Renames::new(pieces);
        let base = scopes[outer].stmt.map_or(scopes[outer].shown, |s| s.span);
        Some(Keyed {
            entry: self.rewrite(w.span, &edits, &renames),
            whole: self.rewrite(base, &edits, &renames),
            base,
            keys,
            hides,
        })
    }

    /// The statement before which the write of `s` can be made once, when it can: the write is
    /// a `*.` call inside the code of the only scope with several keys around it, on every pass
    /// of that code, the scope stands on every path of its statement, and the write reads no
    /// name bound between it and that statement.
    fn hoist_before(&self, s: &Several, scopes: &[Scope]) -> Option<StmtAt> {
        let w = &s.write;
        let sc = &scopes[s.scope];
        let st = sc.stmt?;
        let fits = s.only
            && matches!(w.form, WriteForm::Call(_))
            && w.branch == sc.inner
            && sc.outer == st.branch;
        if !fits {
            return None;
        }
        let bound: HashSet<&str> = (scopes_between(scopes, w.scope, st.scope).into_iter())
            .flat_map(|q| scopes[q].binds.iter().copied())
            .collect();
        (!identifiers(self.text_of(w.span)).any(|n| bound.contains(n))).then_some(st)
    }

    /// Row "Collision", for a write that code run once for each key of a domain, the value of
    /// an indexed definition or the body of a `for`, makes once for each key, since its target
    /// does not name that key (DESIGN.md sec:tour_methods, "Two `*.` chains on one receiver in
    /// one step are two writers of `c'`"). The repair computes the write once before the
    /// statement when it reads no key and no name bound around it there; otherwise it gives
    /// each key its own entry. A new name of the repair avoids the names of the item around
    /// the loop, `step.node`.
    fn several_writers(&self, s: &Several, step: &Step) -> Error {
        let scopes = step.scopes;
        let w = &s.write;
        let name = w.name;
        let sc = &scopes[s.scope];
        let write = self.text_of(w.span);
        let target = self.written_target(w);
        let shown = self.text_of(sc.shown);
        let shown = shown.strip_suffix(';').unwrap_or(shown).trim_end();
        let used = self.names_around(step.node);
        let mut taken = Taken::default();
        let mut notes = vec![
            Note {
                span: w.span,
                text: self.several_text(s, scopes, write, false),
            },
            Note {
                span: sc.shown,
                text: format!(
                    "a step writes `{target}` at most once, even where the values agree, with or \
                     without `with {CARRY_FORWARD}`"
                ),
            },
        ];
        let keyed = self.keyed(w, scopes, &used, &mut taken, Vec::new());
        // Or make the call once, before the statement, when it reads no key.
        let hoist = self.hoist_before(s, scopes).map(|st| {
            let r = fresh("r", true, &used, &mut taken);
            let then = format!(
                "{}{r}{}",
                &self.text[st.span.start..w.span.start],
                &self.text[w.span.end..st.span.end]
            );
            (st, format!("{r} = {write};"), then)
        });
        if let Some(k) = &keyed {
            notes.extend(k.hides.iter().cloned());
        }
        let code = match (&hoist, &keyed) {
            (Some((_, first, then)), _) => format!("{first} {then}"),
            (None, Some(k)) => k.whole.clone(),
            (None, None) => unreachable!("a write in code run for each key has a name to key"),
        };
        if let Some((st, first, _)) = &hoist {
            let what = match st.span == sc.shown {
                true => "definition",
                false => "statement",
            };
            notes.push(Note {
                span: st.span,
                text: format!(
                    "repair: `{first}` before the {what} writes `{target}` once on a step, and \
                     each key reads the result"
                ),
            });
        }
        if let Some(k) = &keyed {
            let keys = and_list(k.keys.iter().map(|k| format!("`{k}`")));
            notes.push(Note {
                span: w.span,
                text: format!(
                    "repair: `{}` writes one entry of `{name}` for each key of {keys}, when \
                     `{name}` has an entry for each",
                    k.entry
                ),
            });
        }
        Error {
            row: Some(Row::Collision),
            menu: String::new(),
            span: w.span,
            message: format!(
                "Several writers of `{target}` in one step: `{shown}`. Try `{code}` instead."
            ),
            notes,
        }
    }

    /// Row "A loop variable not updated on every path of a step", for `name`, whose updates are
    /// `updates`, in written order, among the `.` calls `dots` of the step.
    fn not_every_path<'e>(
        &self,
        name: &'e str,
        updates: &[&Update],
        stmts: &'e [Stmt],
        at: Span,
        step: &Step,
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
        let fixes = self.dot_fixes(name, step, stmts);
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
        // With the `*.` calls completing every path, they are the one repair: `with
        // carryForward` or an `if … else` update would leave the calls writing nothing.
        if covers {
            notes.push(dot_repair(&fixes, None));
            return Error {
                row: Some(Row::NotEveryPath),
                menu: String::new(),
                span: updates[0].span,
                message: format!(
                    "Not updated on every path of a step: {where_}. Try {} instead.",
                    and_list(fixes.iter().map(|f| format!("`{}`", f.code)))
                ),
                notes,
            };
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
        Error {
            row: Some(Row::NotEveryPath),
            menu: String::new(),
            span: updates[0].span,
            message: format!(
                "Not updated on every path of a step: {where_}. Try `{code}` instead."
            ),
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
    /// they run on some paths only; the error then stands at the first of those calls, and the
    /// repairs that would discard them (an update added to the body, a binding before the loop)
    /// are not offered. Otherwise the error stands at the `initial` statement with those repairs.
    fn not_updated<'e>(
        &self,
        s: &Stmt,
        name: &'e str,
        at: Span,
        stmts: &'e [Stmt],
        step: &Step,
    ) -> Error {
        let written = self.text_of(s.span);
        let i = initial_of(unwrapped(s).0);
        let value = i.map_or("…", |i| self.text_of(i.value.span));
        let carried = i.is_some_and(|i| i.carry);
        let fixes = self.dot_fixes(name, step, stmts);
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
        // With the `*.` repair the error stands at the first `.` call, the statement the program
        // meant to update `name`, and the older repairs (an update added to the body, a binding
        // before the loop) are left out: they would discard the calls the program wrote.
        // When some path is left without an update and the statement has keys, no `*.` repair
        // applies (`carry` is `None`) and the older message and repairs stand.
        if let Some(carry) = carry.filter(|_| !fixes.is_empty()) {
            notes.insert(
                1,
                Note {
                    span: s.span,
                    text: format!(
                        "the `initial` statement of `{name}`, which gives it a value before step \
                         0 only"
                    ),
                },
            );
            notes.push(dot_repair(
                &fixes,
                carry.as_ref().map(|(c, w)| (c.as_str(), *w)),
            ));
            let mut codes: Vec<String> = fixes.iter().map(|f| format!("`{}`", f.code)).collect();
            codes.extend(carry.map(|(c, _)| format!("`{c}`")));
            return Error {
                row: Some(Row::InitialNotUpdated),
                menu: String::new(),
                span: fixes[0].span,
                message: format!(
                    "No statement of this loop updates `{name}`: {}. Try {} instead.",
                    not_updating(name, &fixes),
                    and_list(codes)
                ),
                notes,
            };
        }
        // A carried variable is still one the loop updates: `with carryForward` keeps its value
        // on a step that does not update it, and makes no name a loop variable by itself.
        let why = if carried {
            format!(
                "`with {CARRY_FORWARD}` keeps the value of a variable the loop updates on a step \
                 that does not update it, and does not make `{name}` a variable of the loop: a \
                 value no step changes is a constant, written as a binding before the loop."
            )
        } else {
            format!(
                "An `initial` statement gives a value before the first step only, so `{name}` \
                 would have no value at any later step."
            )
        };
        let message = format!(
            "`{written}` gives `{name}` a value before step 0, and no statement of this loop \
             updates `{name}`: none writes `{name}' = …`, `{name}' <- e` or `{name}*.m(…)`. {why}"
        );
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

    /// The `.` calls of `step` on `name` whose method writes the next receiver, so that the
    /// call written with `*.` updates `name`, each with its repair ([`Fix`]). The method is the
    /// one declared on the type of `name` when its `initial` statement shows the type, as
    /// `initial c: Counter = …` or `initial c = Counter(…)`, and the call's receiver is `name`
    /// itself, not a path into it such as `c.pos`; otherwise every method of that name
    /// the source declares must agree on what it writes and on its declared result. A call on
    /// `name'`, a call whose method the source does not declare, and a call of a method with no
    /// declared result whose value is used, not dropped (`d = c.tick();` or `x' = if t > 1 {
    /// c.tick() } else { c };`, a new receiver the program reads, which with `*.` would be
    /// nothing), are left out. A call inside code run once for each of several keys, whose
    /// `*.` form would write `name` once for each key, is made once before the statement, or
    /// given a key, as [`Self::several_writers`] repairs a write.
    fn dot_fixes(&self, name: &str, step: &Step, stmts: &[Stmt]) -> Vec<Fix> {
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
        let scopes = step.scopes;
        // The names a new name of a repair avoids, listed on the first call that needs one.
        let mut used: Option<HashSet<&str>> = None;
        let mut taken = Taken::default();
        let mut out = Vec::new();
        for d in step.dots.iter().filter(|d| d.name == name) {
            let infos = self.methods.named(d.method); // The type of `name` is the receiver's type only when the receiver is `name` itself.
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
            // The call as the whole value of an expression statement, which drops a declared
            // result only through `_ = `.
            let expr_stmt = d
                .stmt
                .filter(|s| matches!(s.kind, StmtKind::Expr(_)))
                .map(|s| (s, if info.result { "_ = " } else { "" }));
            let (replaced, code, counts, notes) = match &d.collide {
                None => {
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
                    (replaced, code, d.span, Vec::new())
                }
                Some(c) => {
                    let used = used.get_or_insert_with(|| self.names_around(step.node));
                    let mut notes = vec![Note {
                        span: d.span,
                        text: self.several_text(c, scopes, &star, true),
                    }];
                    let hoist = self.hoist_before(c, scopes).and_then(|st| {
                        let then = |cut: Span, with: &str| {
                            format!(
                                "{}{with}{}",
                                &self.text[st.span.start..cut.start],
                                &self.text[cut.end..st.span.end]
                            )
                        };
                        match (expr_stmt, info.result) {
                            // The statement moves before the one around the code: `_ =
                            // c*.next(); d[i in 0..<2] = { 0 };`.
                            (Some((s, discard)), _) => {
                                let before = &self.text[s.span.start..d.span.start];
                                let after = &self.text[d.span.end..s.span.end];
                                let tail = &self.text[s.span.end..st.span.end];
                                let gap = tail.len() - tail.trim_start().len();
                                let cut = Span {
                                    start: s.span.start,
                                    end: s.span.end + gap,
                                };
                                Some((st, format!("{discard}{before}{star}{after}"), then(cut, "")))
                            }
                            // The call is made once, and its result read in its place: `r =
                            // c*.next(); d[i in 0..<2] = r;`.
                            (None, true) => {
                                let r = fresh("r", true, used, &mut taken);
                                Some((st, format!("{r} = {star};"), then(d.span, &r)))
                            }
                            (None, false) => None,
                        }
                    });
                    match hoist {
                        Some((st, first, then)) => (
                            self.text_of(st.span).to_string(),
                            format!("{first} {then}"),
                            st.span,
                            notes,
                        ),
                        None => {
                            let dot = d.of_end
                                + (self.text[d.of_end..].len()
                                    - self.text[d.of_end..].trim_start().len());
                            let mut extra = vec![(dot, dot + 1, "*.".to_string())];
                            if let Some((s, discard)) = expr_stmt
                                && !discard.is_empty()
                            {
                                extra.push((s.span.start, s.span.start, discard.to_string()));
                            }
                            let Some(k) = self.keyed(&c.write, scopes, used, &mut taken, extra)
                            else {
                                continue;
                            };
                            notes.extend(k.hides);
                            (self.text_of(k.base).to_string(), k.whole, d.span, notes)
                        }
                    }
                }
            };
            out.push(Fix {
                span: d.span,
                branch: d.branch,
                call,
                star,
                replaced,
                code,
                counts,
                notes,
            });
        }
        // The walk visits calls in no fixed order; notes and repairs follow the source.
        out.sort_by_key(|f| f.span.start);
        out
    }

    /// Whether every path of a step through `stmts` updates `name` once the `.` calls of `fixes`
    /// are written with `*.`, or made once before the statement around them: one more walk of
    /// the step, O(n log n) as [`every_path`] is, made once, for the rejection.
    fn covers<'e>(&self, name: &'e str, fixes: &[Fix], stmts: &'e [Stmt]) -> bool {
        let counted: HashMap<Span, &str> = fixes.iter().map(|f| (f.counts, name)).collect();
        match every_path(stmts, self.qualifiers, &counted).must {
            Must::All => true,
            Must::Names(m) => m.contains(name),
        }
    }

    /// A note at each `.` call of `fixes`: that it does not update `name`, and the paths it runs
    /// on when they are not all of them; and the notes of its repair.
    fn dot_notes(&self, name: &str, fixes: &[Fix]) -> Vec<Note> {
        let mut out = Vec::new();
        for f in fixes {
            let paths = match f.branch {
                Some(b) => format!("; it runs only on the paths through {}", b.what.part()),
                None => String::new(),
            };
            out.push(Note {
                span: f.span,
                text: format!(
                    "`{}` does not update `{name}`: a `.` call never updates its receiver, and \
                     `{}` does{paths}",
                    f.call, f.star
                ),
            });
            out.extend(f.notes.iter().cloned());
        }
        out
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
