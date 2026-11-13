//! The text form of ZIR (DESIGN.md sec:ir, "Dialect descent"): flat, sorted, line-oriented.
//!
//! ```text
//! zir 1
//! r region function (int; int)
//! r.0 prim + (r^0, r^1) -> (int)
//! r results (r.0^0)
//! ```
//!
//! Every region and node has a path: the root region is `r`, node `k` of region `R` is `R.k`,
//! and region `j` of node `N` is `N/j`. A line is a region's header (its kind and argument
//! edges), a node (its operation, inputs and output edges), or a region's results. `R^i` is
//! argument `i` of region `R`, `N^p` output `p` of node `N`, and any other input is a
//! constant, written as the kernel prints values. A value edge is its type in the kernel's
//! prefix syntax (`(| int String)`), then its facts when it has any: `in [0..=9]`,
//! `class 1 mod 3`, `set {1, 5}`, and each facet as `facet units "m"` or `hint name "x"`. A
//! state edge is `state out`.
//!
//! Lines are written sorted by path, a region's header before its nodes, each node followed by
//! its regions, and the results last; the reader accepts the lines in any order, so the form
//! can be sorted, diffed and merged line by line. A pattern is written as the kernel writes
//! one, except that a literal is `=v`, so a literal atom or tuple is not read as a pattern of
//! that shape, a type test is `(is T)` with `T` in the kernel's own type text, which this
//! form reads back, and a binder the compiler made is written with `$`, which no name contains:
//! the elaborator's binder `$k` as it is, and the canonical binder at de Bruijn level `k`
//! (canon/binders.rs) as `$$k`. A recursive type prints as its name, which this form cannot
//! read back: such types are declared from step L2, and their text form comes with the
//! declarations.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::Arc;

use zed_kernel::num::{Rat, TooLarge, bytes_of, read_f32_ieee, read_f64_ieee};
use zed_kernel::term::{Evidence, Grade, GuardPos, Pattern, Prim, Witness};
use zed_kernel::types::{Type, Universe};
use zed_kernel::value::Family;
use zed_kernel::value::Value;

use super::{Derived, Edge, Node, Op, Region, RegionKind, Src, ValueEdge, any_domain, kind_name};
use crate::canon::Facet;
use crate::canon::binders::level_of;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::{Congruence, FiniteSet, Lattice};
use zedc_syntax::lex;

/// The version of the text and binary forms.
pub const VERSION: u32 = 1;

/// Every primitive, in the order the binary form numbers them.
pub const PRIMS: [Prim; 66] = {
    use Prim::*;
    [
        Add,
        Sub,
        Mul,
        Div,
        IntDiv,
        Mod,
        Neg,
        Eq,
        Ne,
        Lt,
        Le,
        Gt,
        Ge,
        And,
        Or,
        Not,
        Min,
        Max,
        Get,
        Count,
        Union,
        Path,
        PathKey,
        PathLen,
        Tuple,
        TupleGet,
        Concat,
        Pow,
        Atom,
        Show,
        CastInt,
        CastRat,
        CastF64,
        Abs,
        Len,
        Lower,
        Upper,
        Trim,
        Sum,
        BitAnd,
        BitOr,
        BitXor,
        BitNot,
        Shl,
        Shr,
        PopCount,
        LeadingZeros,
        TrailingZeros,
        Rotl,
        Rotr,
        F64Bits,
        CodePoint,
        Scalar,
        Utf8,
        FromUtf8,
        MulHi,
        BitReverse,
        ByteSwap,
        Pdep,
        Pext,
        FunnelShl,
        FunnelShr,
        At,
        CastF32,
        Sqrt,
        Fma,
    ]
};

const GRADES: [(Grade, &str); 6] = [
    (Grade::Axiom, "axiom"),
    (Grade::CheckedExhaustive, "checkedExhaustive"),
    (Grade::Proved, "proved"),
    (Grade::Bounded, "bounded"),
    (Grade::Obligated, "obligated"),
    (Grade::Assumed, "assumed"),
];

const KINDS: [RegionKind; 5] = [
    RegionKind::Function,
    RegionKind::Match,
    RegionKind::Loop,
    RegionKind::Rec,
    RegionKind::Port,
];

// ---------------------------------------------------------------------------------------------
// Writing

/// The text form of the graph rooted at `root`.
pub fn print(root: &Region) -> String {
    let mut out = format!("zir {VERSION}\n");
    region_lines(root, &mut out);
    out
}

/// Writes the lines of the graph rooted at `root` from a stack of what is left to write: a
/// region's header, each node's line followed by its regions' lines, and the region's results.
/// One path buffer grows by a step on the way down and is cut back to the step a job starts
/// from, so a line costs the length of its own path.
fn region_lines(root: &Region, out: &mut String) {
    /// Each job holds the length of the path of the region or node it lies in.
    enum Job<'a> {
        /// Region `j` of the node, or the root.
        Region(&'a Region, usize, Option<usize>),
        /// Node `k` of the region.
        Node(&'a Node, usize, usize),
        Results(&'a Region, usize),
    }
    let mut path = String::from("r");
    let mut jobs = vec![Job::Region(root, path.len(), None)];
    while let Some(job) = jobs.pop() {
        match job {
            Job::Region(r, at, j) => {
                path.truncate(at);
                if let Some(j) = j {
                    let _ = write!(path, "/{j}");
                }
                let _ = writeln!(
                    out,
                    "{path} region {} ({})",
                    kind_name(r.kind),
                    edges(&r.args)
                );
                jobs.push(Job::Results(r, path.len()));
                let nodes = r.nodes.iter().enumerate().rev();
                jobs.extend(nodes.map(|(k, n)| Job::Node(n, path.len(), k)));
            }
            Job::Node(n, base, k) => {
                path.truncate(base);
                let _ = write!(path, ".{k}");
                let _ = writeln!(
                    out,
                    "{path} {} ({}) -> ({})",
                    op(&n.op),
                    srcs(&n.inputs, &path[..base]),
                    edges(&n.outputs)
                );
                let subs = n.regions.iter().enumerate().rev();
                jobs.extend(subs.map(|(j, sub)| Job::Region(sub, path.len(), Some(j))));
            }
            Job::Results(r, base) => {
                path.truncate(base);
                let _ = writeln!(out, "{path} results ({})", srcs(&r.results, &path));
            }
        }
    }
}

fn edges(es: &[Edge]) -> String {
    es.iter().map(edge).collect::<Vec<_>>().join("; ")
}

fn srcs(ss: &[Src], path: &str) -> String {
    let one = |s: &Src| match s {
        Src::Arg(i) => format!("{path}^{i}"),
        Src::Out(n, p) => format!("{path}.{n}^{p}"),
        Src::Const(v) => v.to_string(),
    };
    ss.iter().map(one).collect::<Vec<_>>().join(", ")
}

/// The text form of an edge type.
pub fn edge(e: &Edge) -> String {
    let v = match e {
        Edge::State(port) => return format!("state {port}"),
        Edge::Value(v) => v,
    };
    let mut s = v.ty.to_string();
    let d = &v.domain;
    if d.ints != IntervalSet::top() {
        let _ = write!(s, " in {}", d.ints);
    }
    if d.class != Congruence::top() {
        let _ = write!(s, " class {}", d.class);
    }
    if let FiniteSet::Set(vs) = &d.finite {
        let vs: Vec<String> = vs.iter().map(i64::to_string).collect();
        let _ = write!(s, " set {{{}}}", vs.join(", "));
    }
    for f in &v.facets {
        let tag = if f.hint { "hint" } else { "facet" };
        let _ = write!(s, " {tag} {} {}", f.kind, f.value);
    }
    s
}

fn op(op: &Op) -> String {
    let name = super::op_name(op);
    match op {
        Op::Reindex(Witness::Residue) => format!("{name} residue"),
        Op::Reindex(Witness::Catalog(entry)) => format!("{name} catalog {entry}"),
        Op::Fold {
            depth,
            identity,
            ev,
        } => {
            let id = if *identity { " identity" } else { "" };
            format!("{name} {depth}{id} {}", evidence(ev))
        }
        Op::Fix { lattice, ev } => {
            let kind = if *lattice { "lattice" } else { "definedness" };
            format!("{name} {kind} {}", evidence(ev))
        }
        Op::Gen(GuardPos::Before) => format!("{name} before"),
        Op::Gen(GuardPos::After) => format!("{name} after"),
        Op::Read(port) => format!("{name} read {port}"),
        Op::Push(port) => format!("{name} push {port}"),
        Op::Prim(p) => format!("{name} {}", p.printed()),
        Op::Match(ps) => {
            let ps: Vec<String> = ps.iter().map(pattern).collect();
            format!("{name} [{}]", ps.join(", "))
        }
        _ => name.into(),
    }
}

fn evidence(ev: &Evidence) -> String {
    let items: Vec<String> = ev
        .iter()
        .map(|(k, g)| {
            let g = GRADES.iter().find(|(x, _)| x == g).expect("every grade").1;
            format!("{k}: {g}")
        })
        .collect();
    format!("{{{}}}", items.join(", "))
}

/// The text form of a pattern.
///
/// Patterns nest as deep as the program, so the parts still to write wait on a stack, with
/// the text between them (step T2-mid).
pub fn pattern(p: &Pattern) -> String {
    enum Job<'p> {
        Pat(&'p Pattern),
        Text(&'p str),
    }
    let mut out = String::new();
    let mut jobs = vec![Job::Pat(p)];
    // Each part of a list, `sep` between them, then `close`: put on `jobs`, the first on top.
    fn list<'p>(
        jobs: &mut Vec<Job<'p>>,
        close: &'p str,
        parts: Vec<(Option<&'p str>, &'p Pattern)>,
    ) {
        jobs.push(Job::Text(close));
        for (i, (k, q)) in parts.into_iter().enumerate().rev() {
            jobs.push(Job::Pat(q));
            if let Some(k) = k {
                jobs.push(Job::Text(": "));
                jobs.push(Job::Text(k));
            }
            if i > 0 {
                jobs.push(Job::Text(", "));
            }
        }
    }
    while let Some(job) = jobs.pop() {
        let p = match job {
            Job::Text(t) => {
                out.push_str(t);
                continue;
            }
            Job::Pat(p) => p,
        };
        match p {
            Pattern::Wild => out.push('_'),
            // A canonical binder `\0k` is written `$$k`; every other binder as it is.
            Pattern::Bind(x) => match x.strip_prefix('\0') {
                Some(k) => {
                    out.push_str("$$");
                    out.push_str(k);
                }
                None => out.push_str(x),
            },
            Pattern::Lit(v) => {
                let _ = write!(out, "={v}");
            }
            Pattern::Atom(name, ps) if ps.is_empty() => {
                let _ = write!(out, "#{name}");
            }
            Pattern::Atom(name, ps) => {
                let _ = write!(out, "#{name}(");
                list(&mut jobs, ")", ps.iter().map(|q| (None, q)).collect());
            }
            Pattern::Fields(name, fs) => {
                let _ = write!(out, "#{name}(");
                list(
                    &mut jobs,
                    ")",
                    fs.iter().map(|(k, q)| (Some(&**k), q)).collect(),
                );
            }
            Pattern::Tuple(ps) if ps.len() == 1 => {
                out.push('(');
                list(&mut jobs, ",)", vec![(None, &ps[0])]);
            }
            Pattern::Tuple(ps) => {
                out.push('(');
                list(&mut jobs, ")", ps.iter().map(|q| (None, q)).collect());
            }
            Pattern::AnyAtom => out.push_str("#_"),
            Pattern::Is(t) => {
                let _ = write!(out, "(is {t})");
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph in `text`, which [`super::validate::validate`] has not yet checked. An error names the
/// line and column.
pub fn parse(text: &str) -> Result<Region, String> {
    let mut lines = Vec::new();
    let mut header = false;
    for (no, line) in text.lines().enumerate() {
        let no = no + 1;
        if line.trim().is_empty() {
            continue;
        }
        if !header {
            if line.trim() != format!("zir {VERSION}") {
                return Err(format!("line {no}: the first line is `zir {VERSION}`"));
            }
            header = true;
            continue;
        }
        let mut p = P { s: line, i: 0 };
        let l = p
            .line()
            .map_err(|e| format!("line {no}: column {}: {e}", p.i + 1))?;
        lines.push((l, no));
    }
    if !header {
        return Err(format!("the text is empty, and starts `zir {VERSION}`"));
    }
    lines.sort_by_cached_key(|a| a.0.key());
    for w in lines.windows(2) {
        if w[0].0.key() == w[1].0.key() {
            return Err(format!(
                "lines {} and {}: two lines for {}",
                w[0].1,
                w[1].1,
                w[1].0.what()
            ));
        }
    }
    let mut lines = lines.into_iter().peekable();
    let root = build(&mut lines)?;
    if let Some((l, no)) = lines.peek() {
        return Err(format!(
            "line {no}: {} is not in the graph: its parent or an earlier sibling has no line",
            l.what()
        ));
    }
    Ok(root)
}

/// The edge type written `s`, such as `int in [0..=9]`.
pub fn parse_edge(s: &str) -> Result<Edge, String> {
    whole(s, P::edge)
}

/// The type written `s` in the kernel's prefix syntax, such as `(| int String)`.
pub fn parse_type(s: &str) -> Result<Type, String> {
    whole(s, P::ty)
}

/// The value written `s` as the kernel prints values, such as `#err(code: 3)`.
pub fn parse_value(s: &str) -> Result<Value, String> {
    whole(s, P::value)
}

/// The pattern written `s`, such as `#some(x)`.
pub fn parse_pattern(s: &str) -> Result<Pattern, String> {
    whole(s, P::pattern)
}

fn whole<'a, T>(
    s: &'a str,
    item: impl FnOnce(&mut P<'a>) -> Result<T, String>,
) -> Result<T, String> {
    let mut p = P { s, i: 0 };
    let at = |p: &P, e: String| format!("column {}: {e}", p.i + 1);
    let v = item(&mut p).map_err(|e| at(&p, e))?;
    p.ws();
    match p.rest().is_empty() {
        true => Ok(v),
        false => Err(at(&p, format!("unexpected {} after the item", p.found()))),
    }
}

/// A path: alternately node and region indices below the root region.
type Path = Vec<usize>;

fn show(path: &[usize]) -> String {
    let mut s = String::from("r");
    for (i, k) in path.iter().enumerate() {
        let _ = write!(s, "{}{k}", if i % 2 == 0 { '.' } else { '/' });
    }
    s
}

/// The sort key of a region's path: header, nodes in order, results.
fn region_key(path: &[usize]) -> Vec<usize> {
    let mut key = Vec::new();
    for pair in path.chunks(2) {
        key.extend([1, pair[0], pair[1]]);
    }
    key
}

enum Body {
    Header(RegionKind, Vec<Edge>),
    Node(Op, Vec<Src>, Vec<Edge>),
    Results(Vec<Src>),
}

struct Line {
    path: Path,
    body: Body,
}

impl Line {
    fn key(&self) -> Vec<usize> {
        match self.body {
            Body::Header(..) => [region_key(&self.path), vec![0]].concat(),
            Body::Results(_) => [region_key(&self.path), vec![2]].concat(),
            Body::Node(..) => {
                let (last, region) = self.path.split_last().expect("a node's path");
                [region_key(region), vec![1, *last]].concat()
            }
        }
    }

    fn what(&self) -> String {
        match self.body {
            Body::Header(..) => format!("region {}", show(&self.path)),
            Body::Node(..) => format!("node {}", show(&self.path)),
            Body::Results(_) => format!("the results of {}", show(&self.path)),
        }
    }
}

/// The sorted lines, each taken once, in order, by the region it belongs to.
type Lines = std::iter::Peekable<std::vec::IntoIter<(Line, usize)>>;

/// A region or node whose lines are being read.
enum Open {
    Region(Region),
    Node(Node),
}

/// The graph whose lines are `lines`, from each region's header line to its results line.
/// Each line's contents move into the graph, so nothing is copied. The walk keeps the regions
/// and nodes begun and not yet ended on a stack, and one path: a region's, while the region is
/// on top, and a node's extended by the index of the region looked for next, while the node is.
fn build(lines: &mut Lines) -> Result<Region, String> {
    let mut path: Path = Vec::new();
    let mut open = vec![head(lines, &path)?];
    loop {
        match open
            .last_mut()
            .expect("the loop returns when the root ends")
        {
            Open::Region(r) => {
                let k = r.nodes.len();
                let at = path.len();
                if let Some((
                    Line {
                        body: Body::Node(op, inputs, outputs),
                        ..
                    },
                    _,
                )) = lines.next_if(|(l, _)| {
                    let p = &l.path;
                    matches!(l.body, Body::Node(..))
                        && p.len() == at + 1
                        && p[..at] == *path
                        && p[at] == k
                }) {
                    path.extend([k, 0]);
                    open.push(Open::Node(Node {
                        op,
                        inputs,
                        outputs,
                        regions: Vec::new(),
                    }));
                    continue;
                }
                let results =
                    |(l, _): &(Line, usize)| l.path == path && matches!(l.body, Body::Results(_));
                let Some((
                    Line {
                        body: Body::Results(results),
                        ..
                    },
                    _,
                )) = lines.next_if(results)
                else {
                    return Err(match lines.peek() {
                        Some((l, no)) if l.path.starts_with(&path) => format!(
                            "line {no}: {} is not in the graph: region {} has {} before it, \
                             numbered from 0",
                            l.what(),
                            show(&path),
                            match k {
                                1 => "1 node".to_string(),
                                n => format!("{n} nodes"),
                            }
                        ),
                        _ => format!("region {} has no results line", show(&path)),
                    });
                };
                r.results = results;
                let Some(Open::Region(r)) = open.pop() else {
                    unreachable!("the top is this region")
                };
                match open.last_mut() {
                    Some(Open::Node(n)) => {
                        n.regions.push(Arc::new(r));
                        *path
                            .last_mut()
                            .expect("a node's path ends in a region index") = n.regions.len();
                    }
                    Some(Open::Region(_)) => unreachable!("a region lies in a node"),
                    None => return Ok(r),
                }
            }
            Open::Node(_) => {
                if lines
                    .peek()
                    .is_some_and(|(l, _)| l.path == path && matches!(l.body, Body::Header(..)))
                {
                    open.push(head(lines, &path)?);
                    continue;
                }
                let Some(Open::Node(n)) = open.pop() else {
                    unreachable!("the top is this node")
                };
                path.truncate(path.len() - 2);
                match open.last_mut() {
                    Some(Open::Region(r)) => r.nodes.push(n),
                    _ => unreachable!("a node lies in a region"),
                }
            }
        }
    }
}

/// The region at `path`, opened by its header line.
fn head(lines: &mut Lines, path: &[usize]) -> Result<Open, String> {
    let header = |(l, _): &(Line, usize)| l.path == path && matches!(l.body, Body::Header(..));
    let Some((
        Line {
            body: Body::Header(kind, args),
            ..
        },
        _,
    )) = lines.next_if(header)
    else {
        return Err(format!("region {} has no header line", show(path)));
    };
    Ok(Open::Region(Region {
        kind,
        args,
        nodes: Vec::new(),
        results: Vec::new(),
    }))
}

/// A cursor over one line.
struct P<'a> {
    s: &'a str,
    i: usize,
}

/// The length in bytes of the word at the start of `s`: its characters a word holds
/// ([`lex::is_word_char`]) and one prime after them, so that every name the lexer accepts
/// (lex/name.rs) reads back and a word beyond ASCII is read whole, to be refused by name.
fn word_len(s: &str) -> usize {
    let n = s.find(|c| !lex::is_word_char(c)).unwrap_or(s.len());
    n + usize::from(n > 0 && s[n..].starts_with('\''))
}

/// Why `w` is not a name by the lexer's rule ([`lex::name_end`]: a character that starts a
/// name, or `_` before one that continues a name, then characters that continue a name and one
/// prime at most), or `None` when it is one. The rule is the lexer's own function; the first
/// character is looked at again here only to say which part of the rule `w` breaks. The binary
/// form ([`super::binary`]) checks its names with this function too.
pub(super) fn not_a_name(w: &str) -> Option<String> {
    if lex::name_end(w, 0) == Some(w.len()) {
        return None;
    }
    let mut cs = w.chars();
    let why = match cs.next() {
        Some('_') if !cs.next().is_some_and(lex::is_name_continue) => {
            ": a name that starts with `_` has an ASCII letter, a digit or `_` next"
        }
        Some(c) if c != '_' && !lex::is_name_start(c) => {
            ": a name starts with an ASCII letter or `_`"
        }
        _ => "",
    };
    Some(format!("`{w}` is not a name{why}"))
}

/// Why `w` is not a port's name, or `None` when it is one: names joined by `.`, the grammar's
/// `PushTarget` (`m.stdout`, a field of `main`'s argument), or a name and `()`, the port a
/// prelude constructor opens (`files()`). The binary form ([`super::binary`]) checks its port
/// names with this function too.
pub(super) fn not_a_port(w: &str) -> Option<String> {
    let path = w.strip_suffix("()").unwrap_or(w);
    let bad = path.split('.').find_map(not_a_name)?;
    // A plain name is refused as any name is.
    if path == w && !w.contains('.') {
        return Some(bad);
    }
    Some(format!("`{w}` is not a port's name: {bad}"))
}

/// Why `w` is not a pattern binder, or `None` when it is one: a name, or a binder the compiler
/// makes, which no written name can equal. Those are the elaborator's `$N` (elab.rs `temp`)
/// and the canonical `\0N` (canon/binders.rs `level_name`), `N` a decimal number with no
/// leading zero, and for `\0N` a level that fits a `usize`. Both forms read binders by this
/// function: the binary form as they are, the text form after writing `\0N` as `$$N`
/// ([`pattern`]). This is the one place that says which made binders a reader accepts.
pub(super) fn not_a_binder(w: &str) -> Option<String> {
    let number = |n: &str| {
        !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) && (n == "0" || !n.starts_with('0'))
    };
    let made = match w.strip_prefix('$') {
        Some(n) => number(n),
        None => w.strip_prefix('\0').is_some_and(number) && level_of(w).is_some(),
    };
    if made { None } else { not_a_name(w) }
}

impl<'a> P<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.i..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn ws(&mut self) {
        while self.peek() == Some(' ') {
            self.i += 1;
        }
    }

    /// Consumes `t`, after spaces, when it comes next.
    fn eat(&mut self, t: &str) -> bool {
        self.ws();
        if self.rest().starts_with(t) {
            self.i += t.len();
            true
        } else {
            false
        }
    }

    /// Consumes the word `w` when it comes next and is not the start of a longer word.
    fn eat_word(&mut self, w: &str) -> bool {
        self.ws();
        let r = self.rest();
        if r.starts_with(w)
            && !r[w.len()..].starts_with(|c: char| lex::is_word_char(c) || c == '\'')
        {
            self.i += w.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: &str) -> Result<(), String> {
        if self.eat(t) {
            Ok(())
        } else {
            Err(format!("expected `{t}`, found {}", self.found()))
        }
    }

    fn found(&self) -> String {
        match self.rest().split(' ').next() {
            Some("") | None => "the end of the line".into(),
            Some(t) => format!("`{t}`"),
        }
    }

    /// A word: a run of characters that continue a name, then at most one prime. A keyword is
    /// read so; a name is read by [`P::name`], which also checks how it starts.
    fn word(&mut self) -> Result<&'a str, String> {
        self.ws();
        let n = word_len(self.rest());
        if n == 0 {
            return Err(format!("expected a name, found {}", self.found()));
        }
        let w = &self.rest()[..n];
        self.i += n;
        Ok(w)
    }

    /// A name, by the lexer's rule; an error points at its start.
    fn name(&mut self) -> Result<&'a str, String> {
        self.ws();
        let start = self.i;
        let w = self.word()?;
        match not_a_name(w) {
            None => Ok(w),
            Some(e) => {
                self.i = start;
                Err(e)
            }
        }
    }

    /// A port's name ([`not_a_port`]): names joined by `.`, as `m.stdout`, or a name and `()`,
    /// as `files()`. An error points at the name it is about. The cost is linear in the name.
    fn port_name(&mut self) -> Result<&'a str, String> {
        self.ws();
        let start = self.i;
        loop {
            let n = word_len(self.rest());
            if n == 0 {
                return Err(match self.rest().chars().next() {
                    Some(c) if c.is_whitespace() && self.i > start => {
                        "expected a name right after `.`, found a space".to_string()
                    }
                    _ => format!("expected a name, found {}", self.found()),
                });
            }
            if let Some(e) = not_a_name(&self.rest()[..n]) {
                return Err(e);
            }
            self.i += n;
            if self.rest().starts_with("()") && !self.s[start..self.i].contains('.') {
                self.i += 2;
                break;
            }
            if !self.rest().starts_with('.') {
                break;
            }
            self.i += 1;
        }
        Ok(&self.s[start..self.i])
    }

    /// A run of characters up to a space or a bracket.
    fn token(&mut self, stop: &str) -> &'a str {
        self.ws();
        let n = self
            .rest()
            .find(|c: char| c == ' ' || stop.contains(c))
            .unwrap_or(self.rest().len());
        let t = &self.rest()[..n];
        self.i += n;
        t
    }

    fn number<T: std::str::FromStr>(&mut self) -> Result<T, String> {
        self.ws();
        let n = self
            .rest()
            .find(|c: char| !(c.is_ascii_digit() || c == '-'))
            .unwrap_or(self.rest().len());
        let t = &self.rest()[..n];
        let v = t
            .parse()
            .map_err(|_| format!("expected a number, found {}", self.found()))?;
        self.i += n;
        Ok(v)
    }

    fn list<T>(
        &mut self,
        open: &str,
        close: &str,
        sep: &str,
        mut item: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        self.expect(open)?;
        let mut out = Vec::new();
        if self.eat(close) {
            return Ok(out);
        }
        loop {
            out.push(item(self)?);
            if self.eat(close) {
                return Ok(out);
            }
            self.expect(sep)?;
        }
    }

    fn line(&mut self) -> Result<Line, String> {
        let path = self.path()?;
        let body = if self.eat_word("region") {
            if path.len() % 2 == 1 {
                return Err(format!("{} is a node's path, not a region's", show(&path)));
            }
            let kind = self.word()?;
            let kind = *KINDS
                .iter()
                .find(|k| kind_name(**k) == kind)
                .ok_or_else(|| format!("`{kind}` is not a region kind"))?;
            Body::Header(kind, self.list("(", ")", ";", Self::edge)?)
        } else if self.eat_word("results") {
            if path.len() % 2 == 1 {
                return Err(format!("{} is a node's path, not a region's", show(&path)));
            }
            Body::Results(self.list("(", ")", ",", |p| p.src(&path))?)
        } else {
            if path.len() % 2 == 0 {
                return Err(format!(
                    "{} is a region's path, and its lines are `region` and `results`",
                    show(&path)
                ));
            }
            let op = self.op()?;
            let region = &path[..path.len() - 1];
            let inputs = self.list("(", ")", ",", |p| p.src(region))?;
            self.expect("->")?;
            Body::Node(op, inputs, self.list("(", ")", ";", Self::edge)?)
        };
        self.ws();
        if !self.rest().is_empty() {
            return Err(format!("unexpected {} after the line", self.found()));
        }
        Ok(Line { path, body })
    }

    fn path(&mut self) -> Result<Path, String> {
        self.ws();
        if !self.rest().starts_with('r') {
            return Err(format!(
                "expected a path such as `r.0`, found {}",
                self.found()
            ));
        }
        self.i += 1;
        let mut path = Vec::new();
        loop {
            let sep = if path.len() % 2 == 0 { '.' } else { '/' };
            if self.peek() != Some(sep) {
                return Ok(path);
            }
            self.i += 1;
            path.push(self.number()?);
        }
    }

    fn src(&mut self, region: &[usize]) -> Result<Src, String> {
        self.ws();
        if self.peek() != Some('r') {
            return self.value().map(Src::Const);
        }
        let start = self.i;
        let path = self.path()?;
        self.expect("^")?;
        let k = self.number()?;
        if path == region {
            Ok(Src::Arg(k))
        } else if path.len() == region.len() + 1 && path[..region.len()] == *region {
            Ok(Src::Out(path[region.len()], k))
        } else {
            self.i = start;
            Err(format!(
                "{}^{k} is not an edge of region {}, and a region reads only its own edges",
                show(&path),
                show(region)
            ))
        }
    }

    fn op(&mut self) -> Result<Op, String> {
        let name = self.word()?;
        Ok(match name {
            "reindex" => match self.word()? {
                "residue" => Op::Reindex(Witness::Residue),
                "catalog" => Op::Reindex(Witness::Catalog(self.token("(").into())),
                w => return Err(format!("`reindex` takes `residue` or `catalog`, not `{w}`")),
            },
            "discard" => Op::Discard,
            "fold" => Op::Fold {
                depth: self.number()?,
                identity: self.eat_word("identity"),
                ev: self.evidence()?,
            },
            "fix" => Op::Fix {
                lattice: match self.word()? {
                    "lattice" => true,
                    "definedness" => false,
                    w => return Err(format!("`fix` is `lattice` or `definedness`, not `{w}`")),
                },
                ev: self.evidence()?,
            },
            "gen" => Op::Gen(match self.word()? {
                "before" => GuardPos::Before,
                "after" => GuardPos::After,
                w => {
                    return Err(format!(
                        "`gen` tests its guard `before` or `after`, not `{w}`"
                    ));
                }
            }),
            "port" => match self.word()? {
                "read" => Op::Read(self.port_name()?.into()),
                "push" => Op::Push(self.port_name()?.into()),
                w => return Err(format!("`port` is `read` or `push`, not `{w}`")),
            },
            "fam" => Op::Fam,
            "group" => Op::Derived(Derived::Group),
            "orderedValues" => Op::Derived(Derived::OrderedValues),
            "scan" => Op::Derived(Derived::Scan),
            "join" => Op::Derived(Derived::Join),
            "prim" => {
                let t = self.token("(");
                Op::Prim(
                    *PRIMS
                        .iter()
                        .find(|p| p.printed() == t)
                        .ok_or_else(|| format!("`{t}` is not a primitive"))?,
                )
            }
            "apply" => Op::Apply,
            "lambda" => Op::Lambda,
            "if" => Op::If,
            "match" => Op::Match(self.list("[", "]", ",", Self::pattern)?),
            "rec" => Op::Rec,
            "wave" => Op::Wave,
            _ => return Err(format!("`{name}` is not a ZIR operation")),
        })
    }

    fn evidence(&mut self) -> Result<Evidence, String> {
        let items = self.list("{", "}", ",", |p| {
            let k = p.name()?;
            p.expect(":")?;
            let g = p.word()?;
            let g = GRADES
                .iter()
                .find(|(_, n)| *n == g)
                .ok_or_else(|| format!("`{g}` is not a grade"))?
                .0;
            Ok((k.into(), g))
        })?;
        Ok(items.into_iter().collect())
    }

    fn edge(&mut self) -> Result<Edge, String> {
        if self.eat_word("state") {
            return Ok(Edge::State(self.port_name()?.into()));
        }
        let ty = self.ty()?;
        let mut domain = any_domain();
        let mut facets = Vec::new();
        loop {
            if self.eat_word("in") {
                domain.ints = self.intervals()?;
            } else if self.eat_word("class") {
                domain.class = self.congruence()?;
            } else if self.eat_word("set") {
                let vs = self.list("{", "}", ",", |p| p.number::<i64>())?;
                domain.finite = FiniteSet::Set(vs.into_iter().collect::<BTreeSet<_>>());
            } else if self.eat_word("facet") || self.eat_word("hint") {
                let hint = self.s[..self.i].ends_with("hint");
                let kind = self.name()?.into();
                facets.push(Facet {
                    hint,
                    kind,
                    value: self.value()?,
                });
            } else {
                return Ok(Edge::Value(ValueEdge { ty, domain, facets }));
            }
        }
    }

    fn intervals(&mut self) -> Result<IntervalSet, String> {
        let pieces = self.list("[", "]", ",", |p| {
            p.ws();
            let lo = match p.peek() {
                Some('.') => End::NegInf,
                _ => End::Fin(p.number()?),
            };
            p.expect("..")?;
            let hi = match p.rest().starts_with('=') {
                true => {
                    p.i += 1;
                    End::Fin(p.number()?)
                }
                false => End::PosInf,
            };
            Ok((lo, hi))
        })?;
        Ok(IntervalSet::from_pieces(pieces))
    }

    fn congruence(&mut self) -> Result<Congruence, String> {
        if self.eat("{}") {
            return Ok(Congruence::Bottom);
        }
        if self.eat_word("any") {
            return Ok(Congruence::top());
        }
        let r: Num = self.number()?;
        if self.eat_word("mod") {
            Ok(Congruence::new(self.number::<Num>()?, r))
        } else {
            Ok(Congruence::single(r))
        }
    }

    /// A type, from a stack of the forms `(head …)` begun and not yet ended: types nest as
    /// deep as the program (step T2-mid).
    fn ty(&mut self) -> Result<Type, String> {
        let mut open: Vec<(&'a str, Vec<Type>)> = Vec::new();
        loop {
            self.ws();
            let mut got = if self.eat("(") {
                open.push((self.token("();,"), Vec::new()));
                None
            } else {
                Some(self.ty_leaf()?)
            };
            loop {
                let Some((_, ts)) = open.last_mut() else {
                    return Ok(got.expect("a type read"));
                };
                ts.extend(got.take());
                if !self.eat(")") {
                    if self.rest().is_empty() {
                        return Err("expected `)`, found the end of the line".into());
                    }
                    break;
                }
                let (head, ts) = open.pop().expect("the top");
                got = Some(ty_form(head, ts)?);
            }
        }
    }

    /// A type that is not a form `(head …)`.
    fn ty_leaf(&mut self) -> Result<Type, String> {
        match self.peek() {
            Some('"') => return lit(self.value()?),
            Some(c) if c.is_ascii_digit() || c == '-' => {
                // An integer the kernel prints as its powers, `3^200000` or `-5*3^200000`
                // (`Rat::integer_text`), is read as one; any other number by `value`.
                let start = self.i;
                let t = self.token("();,[]{}");
                if t.contains(['^', '*']) {
                    return match Value::power_text(t) {
                        Ok(Some(v)) => lit(v),
                        Ok(None) => Err(format!("expected a value, found `{t}`")),
                        Err(e) => Err(format!(
                            "the system refused the {} bytes of memory asked to read the number \
                             `{t}`",
                            bytes_of(&e.bits)
                        )),
                    };
                }
                self.i = start;
                return lit(self.value()?);
            }
            _ => {}
        }
        let start = self.i;
        let w = self.token("();,[]{}");
        Ok(match w {
            "_" => Type::top(),
            "bool" => Type::bool(),
            "int" => Type::int(),
            "rat" => Type::rat(),
            "f32" => Type::f32(),
            "f64" => Type::f64(),
            "String" => Type::string(),
            "tuple" => Type::universe(Universe::Tuple),
            "struct" => Type::universe(Universe::Struct),
            "morphism" => Type::universe(Universe::Morphism),
            "#_" => all_atoms(),
            "true" | "false" | "nan" | "inf" => {
                self.i = start;
                return lit(self.value()?);
            }
            w if w.len() > 1 && w.starts_with('#') => match not_a_name(&w[1..]) {
                None => Type::atom(&w[1..]),
                Some(e) => {
                    self.i = start + 1;
                    return Err(e);
                }
            },
            w => {
                self.i = start;
                return Err(format!(
                    "`{w}` is not a type of the text form; a recursive type has none until step L2 declares types"
                ));
            }
        })
    }

    /// A value, from a stack of the atoms, tuples, paths and families begun and not yet
    /// ended: values nest as deep as the program (step T2-mid).
    fn value(&mut self) -> Result<Value, String> {
        let mut open: Vec<OpenValue<'a>> = Vec::new();
        loop {
            let mut got = self.value_start(&mut open)?;
            loop {
                let Some(top) = open.last_mut() else {
                    if let Some(v) = got {
                        return Ok(v);
                    }
                    unreachable!("a value opened is on the stack");
                };
                let Some(v) = got.take() else { break };
                if !self.value_part(top, v)? {
                    break;
                }
                got = Some(open.pop().expect("the top").close()?);
            }
        }
    }

    /// A value with no parts; or `None`, when a value with parts is opened on `open`, with
    /// what comes before its first part read.
    fn value_start(&mut self, open: &mut Vec<OpenValue<'a>>) -> Result<Option<Value>, String> {
        self.ws();
        Ok(Some(match self.peek() {
            Some('"') => Value::str(&self.string()?),
            Some('#') => {
                self.i += 1;
                let name = self.name()?;
                if self.peek() != Some('(') {
                    return Ok(Some(Value::atom(name)));
                }
                self.expect("(")?;
                if self.eat(")") {
                    return Ok(Some(Value::atom_with(name, Vec::new())));
                }
                let mut fields = Vec::new();
                self.field(&mut fields)?;
                open.push(OpenValue::Atom {
                    name,
                    fields,
                    args: Vec::new(),
                });
                return Ok(None);
            }
            Some(c @ ('(' | '[')) => {
                let path = c == '[';
                self.expect(if path { "[" } else { "(" })?;
                if self.eat(if path { "]" } else { ")" }) {
                    return Ok(Some(match path {
                        false => Value::tuple(Vec::new()),
                        true => Value::path(Vec::new()),
                    }));
                }
                open.push(OpenValue::Items {
                    path,
                    items: Vec::new(),
                });
                return Ok(None);
            }
            Some('{') => {
                self.expect("{")?;
                if self.eat("}") {
                    return Ok(Some(Value::Family(Family::new())));
                }
                open.push(OpenValue::Family {
                    map: None,
                    entries: Vec::new(),
                    key: None,
                });
                return Ok(None);
            }
            _ => {
                let t = self.token("()[]{},;^");
                if t.is_empty() {
                    return Err(format!("expected a value, found {}", self.found()));
                }
                number(t)?
            }
        }))
    }

    /// The name of an atom's next part, `f: `, when it has one, pushed on `fields`; an error
    /// when the word before `: ` is not a name.
    fn field(&mut self, fields: &mut Vec<Arc<str>>) -> Result<(), String> {
        self.ws();
        let save = self.i;
        if let Ok(f) = self.word()
            && self.rest().starts_with(": ")
        {
            if let Some(e) = not_a_name(f) {
                self.i = save;
                return Err(e);
            }
            self.i += 1;
            fields.push(f.into());
            return Ok(());
        }
        self.i = save;
        Ok(())
    }

    /// Puts part `v` in `top` and reads what follows it: true when `top` ends there.
    fn value_part(&mut self, top: &mut OpenValue<'a>, v: Value) -> Result<bool, String> {
        match top {
            OpenValue::Atom { fields, args, .. } => {
                args.push(v);
                if self.eat(")") {
                    return Ok(true);
                }
                self.expect(",")?;
                self.field(fields)?;
            }
            OpenValue::Items { path, items } => {
                items.push(v);
                if self.eat(if *path { "]" } else { ")" }) {
                    return Ok(true);
                }
                self.expect(if *path { "->" } else { "," })?;
                // A tuple may end in `,`, as a pattern may: the kernel writes a one-tuple `(x,)`.
                if !*path && self.eat(")") {
                    return Ok(true);
                }
            }
            OpenValue::Family { map, entries, key } => {
                // The first part says whether the family is a map: `{k -> v, …}` or `{k, …}`.
                let map = *map.get_or_insert_with(|| self.eat("->"));
                match key.take() {
                    None if map => {
                        if !entries.is_empty() {
                            self.expect("->")?;
                        }
                        *key = Some(v);
                        return Ok(false);
                    }
                    None => entries.push((v.clone(), v)),
                    Some(k) => entries.push((k, v)),
                }
                if self.eat("}") {
                    return Ok(true);
                }
                self.expect(",")?;
            }
        }
        Ok(false)
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect("\"")?;
        let mut out = String::new();
        let mut chars = self.rest().char_indices();
        while let Some((at, c)) = chars.next() {
            match c {
                '"' => {
                    self.i += at + 1;
                    return Ok(out);
                }
                '\\' => {
                    let (_, e) = chars.next().ok_or("an unfinished escape")?;
                    out.push(match e {
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        '0' => '\0',
                        '\\' | '"' | '\'' | '$' => e,
                        'u' => {
                            let mut hex = String::new();
                            if chars.next().map(|c| c.1) != Some('{') {
                                return Err("`\\u` is followed by `{`".into());
                            }
                            for (_, h) in chars.by_ref() {
                                if h == '}' {
                                    break;
                                }
                                hex.push(h);
                            }
                            u32::from_str_radix(&hex, 16)
                                .ok()
                                .and_then(char::from_u32)
                                .ok_or_else(|| format!("`\\u{{{hex}}}` is not a character"))?
                        }
                        e => return Err(format!("`\\{e}` is not an escape")),
                    });
                }
                c => out.push(c),
            }
        }
        Err("the string has no closing `\"`".into())
    }

    /// A pattern, from a stack of the patterns with parts begun and not yet ended: patterns
    /// nest as deep as the program (step T2-mid).
    fn pattern(&mut self) -> Result<Pattern, String> {
        let mut open: Vec<OpenPattern> = Vec::new();
        loop {
            let mut got = self.pattern_start(&mut open)?;
            loop {
                let Some(top) = open.last_mut() else {
                    if let Some(p) = got {
                        return Ok(p);
                    }
                    unreachable!("a pattern opened is on the stack");
                };
                let Some(p) = got.take() else { break };
                if !self.pattern_part(top, p)? {
                    break;
                }
                got = Some(open.pop().expect("the top").close());
            }
        }
    }

    /// A pattern with no parts; or `None`, when a pattern with parts is opened on `open`,
    /// with what comes before its first part read.
    fn pattern_start(&mut self, open: &mut Vec<OpenPattern>) -> Result<Option<Pattern>, String> {
        self.ws();
        if self.eat("=") {
            return self.value().map(|v| Some(Pattern::Lit(v)));
        }
        if self.eat_word("#_") {
            return Ok(Some(Pattern::AnyAtom));
        }
        if self.eat("#") {
            let name: Arc<str> = self.name()?.into();
            if self.peek() != Some('(') {
                return Ok(Some(Pattern::Atom(name, Vec::new())));
            }
            if self.rest().starts_with("()") {
                self.i += 2;
                return Ok(Some(Pattern::Fields(name, Vec::new())));
            }
            let save = self.i;
            self.i += 1;
            let named = self.word().is_ok() && self.rest().starts_with(": ");
            self.i = save;
            self.expect("(")?;
            if self.eat(")") {
                return Ok(Some(match named {
                    true => Pattern::Fields(name, Vec::new()),
                    false => Pattern::Atom(name, Vec::new()),
                }));
            }
            open.push(match named {
                true => OpenPattern::Fields(name, Vec::new(), self.field_name()?),
                false => OpenPattern::Atom(name, Vec::new()),
            });
            return Ok(None);
        }
        if self.eat("(") {
            if self.eat_word("is") {
                let t = self.ty()?;
                self.expect(")")?;
                return Ok(Some(Pattern::Is(t)));
            }
            if self.eat(")") {
                return Ok(Some(Pattern::Tuple(Vec::new())));
            }
            open.push(OpenPattern::Tuple(Vec::new()));
            return Ok(None);
        }
        if self.eat_word("_") {
            return Ok(Some(Pattern::Wild));
        }
        if self.peek() == Some('$') {
            return self.generated_binder().map(|x| Some(Pattern::Bind(x)));
        }
        Ok(Some(Pattern::Bind(self.name()?.into())))
    }

    /// A binder the compiler made: `$k`, the elaborator's binder of that name, or `$$k`, the
    /// canonical binder at de Bruijn level `k` (`\0k`). Which binders exist is
    /// [`not_a_binder`]'s to say, as for the binary form; the number has no leading zero, so
    /// each binder has one spelling. An error points at the `$`.
    fn generated_binder(&mut self) -> Result<Arc<str>, String> {
        let canonical = self.rest().starts_with("$$");
        let sigil = if canonical { 2 } else { 1 };
        let digits = &self.rest()[sigil..];
        let n = digits
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(digits.len());
        let (k, after) = digits.split_at(n);
        let joined = after.starts_with(|c: char| lex::is_word_char(c) || c == '\'');
        let x: Arc<str> = match canonical {
            true => format!("\0{k}"),
            false => format!("${k}"),
        }
        .into();
        if !joined && not_a_binder(&x).is_none() {
            self.i += sigil + n;
            return Ok(x);
        }
        let why = if k.is_empty() {
            "a binder written with `$` has a number after the `$`"
        } else if k.len() > 1 && k.starts_with('0') {
            "a binder written with `$` has a number with no leading zero"
        } else if joined {
            "a binder written with `$` ends with its number"
        } else {
            "its level is too large"
        };
        let w = &self.rest()[..sigil + n + word_len(after)];
        Err(format!("`{w}` is not a binder: {why}"))
    }

    /// `f:`, the name of the next part of a fields pattern.
    fn field_name(&mut self) -> Result<Arc<str>, String> {
        let f = self.name()?.into();
        self.expect(":")?;
        Ok(f)
    }

    /// Puts part `p` in `top` and reads what follows it: true when `top` ends there.
    fn pattern_part(&mut self, top: &mut OpenPattern, p: Pattern) -> Result<bool, String> {
        match top {
            OpenPattern::Atom(_, ps) => {
                ps.push(p);
                if self.eat(")") {
                    return Ok(true);
                }
                self.expect(",")?;
            }
            OpenPattern::Fields(_, fs, key) => {
                fs.push((key.clone(), p));
                if self.eat(")") {
                    return Ok(true);
                }
                self.expect(",")?;
                *key = self.field_name()?;
            }
            OpenPattern::Tuple(ps) => {
                ps.push(p);
                if !self.eat(",") {
                    self.expect(")")?;
                    return Ok(true);
                }
                if self.eat(")") {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}

/// An atom, a tuple or path (`path`), or a family whose parts are being read.
enum OpenValue<'a> {
    Atom {
        name: &'a str,
        fields: Vec<Arc<str>>,
        args: Vec<Value>,
    },
    Items {
        path: bool,
        items: Vec<Value>,
    },
    /// `map` is known once the first part is read; `key` is the key of the entry being read.
    Family {
        map: Option<bool>,
        entries: Vec<(Value, Value)>,
        key: Option<Value>,
    },
}

impl OpenValue<'_> {
    /// The value, all its parts read.
    fn close(self) -> Result<Value, String> {
        match self {
            OpenValue::Atom { name, fields, args } => {
                if fields.is_empty() {
                    return Ok(Value::atom_with(name, args));
                }
                if fields.len() != args.len() {
                    return Err(format!("atom `#{name}` mixes named and positional payload"));
                }
                Value::atom_named(name, fields.into_iter().zip(args).collect())
                    .ok_or_else(|| format!("atom `#{name}` names a field twice"))
            }
            OpenValue::Items { path: false, items } => Ok(Value::tuple(items)),
            OpenValue::Items { path: true, items } => Ok(Value::path(items)),
            OpenValue::Family { entries, .. } => family(entries).map(Value::Family),
        }
    }
}

/// The family a literal's `entries` write, read from text or binary data. Each key is
/// written once: the printer never repeats one, so data that does is damaged, and is refused
/// naming the least key it repeats. Keys are compared as keys, so `-0.0` repeats `0.0`.
/// O(n log n) comparisons for n entries.
pub(super) fn family(mut entries: Vec<(Value, Value)>) -> Result<Family, String> {
    for (k, _) in &mut entries {
        if !k.is_key() {
            *k = k.key();
        }
    }
    entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    if let Some(w) = entries.windows(2).find(|w| w[0].0 == w[1].0) {
        return Err(format!("the family writes the key {} twice", w[0].0));
    }
    Family::from_leaves(entries.into_iter().map(|(k, v)| (vec![k], v))).map_err(|e| e.to_string())
}

/// An atom, fields or tuple pattern whose parts are being read; a fields pattern holds the
/// name of the part being read.
enum OpenPattern {
    Atom(Arc<str>, Vec<Pattern>),
    Fields(Arc<str>, Vec<(Arc<str>, Pattern)>, Arc<str>),
    Tuple(Vec<Pattern>),
}

impl OpenPattern {
    fn close(self) -> Pattern {
        match self {
            OpenPattern::Atom(name, ps) => Pattern::Atom(name, ps),
            OpenPattern::Fields(name, fs, _) => Pattern::Fields(name, fs),
            OpenPattern::Tuple(ps) => Pattern::Tuple(ps),
        }
    }
}

/// The type `(head ts…)`.
fn ty_form(head: &str, ts: Vec<Type>) -> Result<Type, String> {
    let arity = |n: usize| -> Result<(), String> {
        match ts.len() == n {
            true => Ok(()),
            false => Err(format!(
                "`({head} …)` takes {n} types, and has {}",
                ts.len()
            )),
        }
    };
    Ok(match head {
        "|" => Type::union_all(ts.iter().cloned()),
        "&" => Type::meet_all(ts.iter().cloned()),
        "!" => {
            arity(1)?;
            !&ts[0]
        }
        "\\" if !ts.is_empty() => ts[1..].iter().fold(ts[0].clone(), |a, t| &a - t),
        "tuple" => Type::tuple(ts),
        "->" if ts.len() == 2 => Type::morphism(ts[0].clone(), ts[0].clone(), ts[1].clone()),
        "->" => {
            arity(3)?;
            Type::morphism(ts[0].clone(), ts[1].clone(), ts[2].clone())
        }
        "->?" => {
            arity(2)?;
            Type::morphism(Type::empty(), ts[0].clone(), ts[1].clone())
        }
        h if h.len() > 1 && h.starts_with('#') && not_a_name(&h[1..]).is_none() => {
            arity(1)?;
            Type::atom_with(&h[1..], &ts[0])
        }
        h if h.len() > 1 && h.starts_with('#') => {
            return Err(format!("`({h} …)`: `{}` is not a name", &h[1..]));
        }
        h => return Err(format!("`({h} …)` is not a type form")),
    })
}

/// The type of the one value `v`.
fn lit(v: Value) -> Result<Type, String> {
    Type::lit(&v).ok_or_else(|| format!("`{v}` is not a literal type"))
}

/// Every atom: the scalars that are not booleans, numbers or strings.
fn all_atoms() -> Type {
    [
        Type::bool(),
        Type::int(),
        Type::rat(),
        Type::f32(),
        Type::f64(),
        Type::string(),
    ]
    .iter()
    .fold(Type::universe(Universe::Scalar), |a, t| &a - t)
}

/// A number, as the kernel prints numbers: `3`, `-2r/3r`, `1.5`, `1.0e300`, `nan`, `-inf`;
/// the message says why `t` is not one.
fn number(t: &str) -> Result<Value, String> {
    let not = || format!("expected a value, found `{t}`");
    match t {
        "true" => return Ok(Value::Bool(true)),
        "false" => return Ok(Value::Bool(false)),
        "nan" | "inf" | "-inf" => return t.parse().map(Value::float).map_err(|_| not()),
        _ => {}
    }
    // An `f32` prints with its suffix (`0.1f32`, `nanf32`), as a `rat` prints with its `r`.
    if let Some(body) = t.strip_suffix("f32") {
        return match body {
            "nan" | "inf" | "-inf" => body.parse().map(Value::float32).map_err(|_| not()),
            _ if body.contains(['.', 'e']) => {
                read_f32_ieee(body).map(Value::float32).ok_or_else(not)
            }
            _ => Err(not()),
        };
    }
    let refused = |e: TooLarge| {
        format!(
            "the system refused the {} bytes of memory asked to read the number `{t}`",
            bytes_of(&e.bits)
        )
    };
    if t.contains('r') {
        // A side is digits, or digits and an exponent as a type prints them (`1e400000r`),
        // read as a decimal literal so the power is kept and not built.
        let side = |s: &str| -> Result<Rat, String> {
            let Some(s) = s.strip_suffix('r').filter(|s| !s.contains('.')) else {
                return Err(not());
            };
            Rat::decimal(s).map_err(refused)?.ok_or_else(not)
        };
        let Some((n, d)) = t.split_once('/') else {
            return side(t).map(Value::rat);
        };
        return match side(n)?.div(&side(d)?) {
            Ok(Some(r)) => Ok(Value::rat(r)),
            Ok(None) => Err(not()),
            Err(e) => Err(refused(e)),
        };
    }
    if t.contains(['.', 'e']) {
        return read_f64_ieee(t).map(Value::float).ok_or_else(not);
    }
    if t.is_empty()
        || !t
            .trim_start_matches('-')
            .chars()
            .all(|c| c.is_ascii_digit())
    {
        return Err(not());
    }
    Value::int_text(t, 10).map_err(refused)?.ok_or_else(not)
}
