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
//! that shape. A recursive type prints as its name, which this form cannot read back: such
//! types are declared from step L2, and their text form comes with the declarations.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use num_bigint::BigInt;
use zed_kernel::family::Family;
use zed_kernel::num::Rat;
use zed_kernel::term::{Evidence, Grade, GuardPos, Pattern, Prim, Witness};
use zed_kernel::types::{Type, Universe};
use zed_kernel::value::Value;

use super::{Derived, Edge, Node, Op, Region, RegionKind, Src, ValueEdge, any_domain, kind_name};
use crate::canon::Facet;
use crate::store::interval::{End, IntervalSet};
use crate::store::lattice::{Congruence, FiniteSet, Lattice};

/// The version of the text and binary forms.
pub const VERSION: u32 = 1;

/// Every primitive, in the order the binary form numbers them.
pub const PRIMS: [Prim; 39] = {
    use Prim::*;
    [
        Add, Sub, Mul, Div, IntDiv, Mod, Neg, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Not, Min, Max, Get,
        Count, Union, Path, PathKey, PathLen, Tuple, TupleGet, Concat, Pow, Atom, Show, CastInt,
        CastRat, CastF64, Abs, Len, Lower, Upper, Trim, Sum,
    ]
};

/// How the text form spells a primitive: as the kernel's printer does.
pub fn spell(p: Prim) -> &'static str {
    use Prim::*;
    match p {
        Add => "+",
        Sub => "-",
        Mul => "*",
        Div => "/",
        IntDiv => "div",
        Mod => "mod",
        Neg => "neg",
        Eq => "==",
        Ne => "!=",
        Lt => "<",
        Le => "<=",
        Gt => ">",
        Ge => ">=",
        And => "&&",
        Or => "||",
        Not => "not",
        Min => "min",
        Max => "max",
        Get => "get",
        Count => "count",
        Union => "union",
        Path => "path",
        PathKey => "pathKey",
        PathLen => "pathLen",
        Tuple => "tuple",
        TupleGet => "tupleGet",
        Concat => "++",
        Pow => "**",
        Atom => "atom",
        Show => "String",
        CastInt => "int",
        CastRat => "rat",
        CastF64 => "f64",
        Abs => "abs",
        Len => "len",
        Lower => "lower",
        Upper => "upper",
        Trim => "trim",
        Sum => "sum",
    }
}

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
    region_lines(root, "r", &mut out);
    out
}

fn region_lines(r: &Region, path: &str, out: &mut String) {
    let _ = writeln!(
        out,
        "{path} region {} ({})",
        kind_name(r.kind),
        edges(&r.args)
    );
    for (k, n) in r.nodes.iter().enumerate() {
        let at = format!("{path}.{k}");
        let _ = writeln!(
            out,
            "{at} {} ({}) -> ({})",
            op(&n.op),
            srcs(&n.inputs, path),
            edges(&n.outputs)
        );
        for (j, sub) in n.regions.iter().enumerate() {
            region_lines(sub, &format!("{at}/{j}"), out);
        }
    }
    let _ = writeln!(out, "{path} results ({})", srcs(&r.results, path));
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
        Op::Prim(p) => format!("{name} {}", spell(*p)),
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
pub fn pattern(p: &Pattern) -> String {
    let list = |ps: &[Pattern]| ps.iter().map(pattern).collect::<Vec<_>>().join(", ");
    match p {
        Pattern::Wild => "_".into(),
        Pattern::Bind(x) => x.to_string(),
        Pattern::Lit(v) => format!("={v}"),
        Pattern::Atom(name, ps) if ps.is_empty() => format!("#{name}"),
        Pattern::Atom(name, ps) => format!("#{name}({})", list(ps)),
        Pattern::Fields(name, fs) => {
            let fs: Vec<String> = fs
                .iter()
                .map(|(k, p)| format!("{k}: {}", pattern(p)))
                .collect();
            format!("#{name}({})", fs.join(", "))
        }
        Pattern::Tuple(ps) if ps.len() == 1 => format!("({},)", pattern(&ps[0])),
        Pattern::Tuple(ps) => format!("({})", list(ps)),
        Pattern::AnyAtom => "#_".into(),
        Pattern::Is(t) => format!("(is {t})"),
    }
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph in `text`, which [`super::validate`] has not yet checked. An error names the
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
    lines.sort_by_key(|a| a.0.key());
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
    let mut i = 0;
    let root = build(&lines, &mut i, &[])?;
    if let Some((l, no)) = lines.get(i) {
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

fn build(lines: &[(Line, usize)], i: &mut usize, path: &[usize]) -> Result<Region, String> {
    let (kind, args) = match lines.get(*i) {
        Some((
            Line {
                path: p,
                body: Body::Header(kind, args),
            },
            _,
        )) if p == path => (*kind, args.clone()),
        _ => return Err(format!("region {} has no header line", show(path))),
    };
    *i += 1;
    let mut nodes = Vec::new();
    while let Some((
        Line {
            path: p,
            body: Body::Node(op, inputs, outputs),
        },
        _,
    )) = lines.get(*i)
    {
        if p.len() != path.len() + 1 || p[..path.len()] != *path || p[path.len()] != nodes.len() {
            break;
        }
        *i += 1;
        let mut regions = Vec::new();
        loop {
            let sub = [p.as_slice(), &[regions.len()]].concat();
            match lines.get(*i) {
                Some((l, _)) if l.path == sub && matches!(l.body, Body::Header(..)) => {
                    regions.push(build(lines, i, &sub)?);
                }
                _ => break,
            }
        }
        nodes.push(Node {
            op: op.clone(),
            inputs: inputs.clone(),
            outputs: outputs.clone(),
            regions,
        });
    }
    let results = match lines.get(*i) {
        Some((
            Line {
                path: p,
                body: Body::Results(rs),
            },
            _,
        )) if p == path => rs.clone(),
        Some((l, no)) if l.path.starts_with(path) => {
            return Err(format!(
                "line {no}: {} is not in the graph: region {} has {} before it, numbered from 0",
                l.what(),
                show(path),
                match nodes.len() {
                    1 => "1 node".to_string(),
                    n => format!("{n} nodes"),
                }
            ));
        }
        _ => return Err(format!("region {} has no results line", show(path))),
    };
    *i += 1;
    Ok(Region {
        kind,
        args,
        nodes,
        results,
    })
}

/// A cursor over one line.
struct P<'a> {
    s: &'a str,
    i: usize,
}

fn ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
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
        if r.starts_with(w) && !r[w.len()..].starts_with(ident) {
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

    /// A run of letters, digits and `_`.
    fn word(&mut self) -> Result<&'a str, String> {
        self.ws();
        let n = self.rest().find(|c| !ident(c)).unwrap_or(self.rest().len());
        if n == 0 {
            return Err(format!("expected a name, found {}", self.found()));
        }
        let w = &self.rest()[..n];
        self.i += n;
        Ok(w)
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
                "read" => Op::Read(self.word()?.into()),
                "push" => Op::Push(self.word()?.into()),
                w => return Err(format!("`port` is `read` or `push`, not `{w}`")),
            },
            "fam" => Op::Fam,
            "group" => Op::Derived(Derived::Group),
            "rank" => Op::Derived(Derived::Rank),
            "scan" => Op::Derived(Derived::Scan),
            "join" => Op::Derived(Derived::Join),
            "prim" => {
                let t = self.token("(");
                Op::Prim(
                    *PRIMS
                        .iter()
                        .find(|p| spell(**p) == t)
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
            let k = p.word()?;
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
            return Ok(Edge::State(self.word()?.into()));
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
                let kind = self.word()?.into();
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
        let r: i64 = self.number()?;
        if self.eat_word("mod") {
            Ok(Congruence::new(self.number()?, r))
        } else {
            Ok(Congruence::single(r))
        }
    }

    fn ty(&mut self) -> Result<Type, String> {
        self.ws();
        if self.eat("(") {
            let head = self.token("();,");
            let items = |p: &mut Self| -> Result<Vec<Type>, String> {
                let mut out = Vec::new();
                while !p.eat(")") {
                    if p.rest().is_empty() {
                        return Err("expected `)`, found the end of the line".into());
                    }
                    out.push(p.ty()?);
                }
                Ok(out)
            };
            let ts = items(self)?;
            let arity = |n: usize| -> Result<(), String> {
                match ts.len() == n {
                    true => Ok(()),
                    false => Err(format!(
                        "`({head} …)` takes {n} types, and has {}",
                        ts.len()
                    )),
                }
            };
            return Ok(match head {
                "|" => Type::union_all(ts.iter().cloned()),
                "&" => Type::meet_all(ts.iter().cloned()),
                "!" => {
                    arity(1)?;
                    !&ts[0]
                }
                "\\" if !ts.is_empty() => ts[1..].iter().fold(ts[0].clone(), |a, t| &a - t),
                "tuple" => Type::tuple(ts),
                "->" if ts.len() == 2 => {
                    Type::morphism(ts[0].clone(), ts[0].clone(), ts[1].clone())
                }
                "->" => {
                    arity(3)?;
                    Type::morphism(ts[0].clone(), ts[1].clone(), ts[2].clone())
                }
                "->?" => {
                    arity(2)?;
                    Type::morphism(Type::empty(), ts[0].clone(), ts[1].clone())
                }
                h if h.len() > 1 && h.starts_with('#') => {
                    arity(1)?;
                    Type::atom_with(&h[1..], &ts[0])
                }
                h => return Err(format!("`({h} …)` is not a type form")),
            });
        }
        match self.peek() {
            Some('"') => return lit(self.value()?),
            Some(c) if c.is_ascii_digit() || c == '-' => return lit(self.value()?),
            _ => {}
        }
        let start = self.i;
        let w = self.token("();,[]{}");
        Ok(match w {
            "_" => Type::top(),
            "bool" => Type::bool(),
            "int" => Type::int(),
            "rat" => Type::rat(),
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
            w if w.len() > 1 && w.starts_with('#') && w[1..].chars().all(ident) => {
                Type::atom(&w[1..])
            }
            w => {
                self.i = start;
                return Err(format!(
                    "`{w}` is not a type of the text form; a recursive type has none until step L2 declares types"
                ));
            }
        })
    }

    fn value(&mut self) -> Result<Value, String> {
        self.ws();
        match self.peek() {
            Some('"') => self.string().map(|s| Value::str(&s)),
            Some('#') => {
                self.i += 1;
                let name = self.word()?;
                if self.peek() != Some('(') {
                    return Ok(Value::atom(name));
                }
                let mut fields = Vec::new();
                let args = self.list("(", ")", ",", |p| {
                    p.ws();
                    let save = p.i;
                    if let Ok(f) = p.word()
                        && p.rest().starts_with(": ")
                    {
                        p.i += 1;
                        fields.push(f.into());
                        return p.value();
                    }
                    p.i = save;
                    p.value()
                })?;
                if fields.is_empty() {
                    return Ok(Value::atom_with(name, args));
                }
                if fields.len() != args.len() {
                    return Err(format!("atom `#{name}` mixes named and positional payload"));
                }
                Value::atom_named(name, fields.into_iter().zip(args).collect())
                    .ok_or_else(|| format!("atom `#{name}` names a field twice"))
            }
            Some('(') => Ok(Value::Tuple(self.list("(", ")", ",", Self::value)?)),
            Some('[') => Ok(Value::Path(self.list("[", "]", "->", Self::value)?)),
            Some('{') => {
                self.expect("{")?;
                if self.eat("}") {
                    return Ok(Value::Family(Family::new()));
                }
                let first = self.value()?;
                let map = self.eat("->");
                let mut entries = Vec::new();
                let mut item = first;
                loop {
                    let v = if map { self.value()? } else { item.clone() };
                    entries.push((item, v));
                    if self.eat("}") {
                        break;
                    }
                    self.expect(",")?;
                    item = self.value()?;
                    if map {
                        self.expect("->")?;
                    }
                }
                Ok(Value::Family(Family::of(entries)))
            }
            _ => {
                let t = self.token("()[]{},;^");
                number(t).ok_or_else(|| format!("expected a value, found `{t}`"))
            }
        }
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
                        '\\' | '"' | '\'' => e,
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

    fn pattern(&mut self) -> Result<Pattern, String> {
        self.ws();
        if self.eat("=") {
            return self.value().map(Pattern::Lit);
        }
        if self.eat_word("#_") {
            return Ok(Pattern::AnyAtom);
        }
        if self.eat("#") {
            let name: std::sync::Arc<str> = self.word()?.into();
            if self.peek() != Some('(') {
                return Ok(Pattern::Atom(name, Vec::new()));
            }
            if self.rest().starts_with("()") {
                self.i += 2;
                return Ok(Pattern::Fields(name, Vec::new()));
            }
            let save = self.i;
            self.i += 1;
            let named = self.word().is_ok() && self.rest().starts_with(": ");
            self.i = save;
            return Ok(match named {
                true => Pattern::Fields(
                    name,
                    self.list("(", ")", ",", |p| {
                        let f = p.word()?.into();
                        p.expect(":")?;
                        Ok((f, p.pattern()?))
                    })?,
                ),
                false => Pattern::Atom(name, self.list("(", ")", ",", Self::pattern)?),
            });
        }
        if self.eat("(") {
            if self.eat_word("is") {
                let t = self.ty()?;
                self.expect(")")?;
                return Ok(Pattern::Is(t));
            }
            let mut ps = Vec::new();
            while !self.eat(")") {
                ps.push(self.pattern()?);
                if !self.eat(",") {
                    self.expect(")")?;
                    break;
                }
            }
            return Ok(Pattern::Tuple(ps));
        }
        let w = self.word()?;
        Ok(match w {
            "_" => Pattern::Wild,
            w => Pattern::Bind(w.into()),
        })
    }
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
        Type::f64(),
        Type::string(),
    ]
    .iter()
    .fold(Type::universe(Universe::Scalar), |a, t| &a - t)
}

/// A number, as the kernel prints numbers: `3`, `-2r/3r`, `1.5`, `1.0e300`, `nan`, `-inf`.
fn number(t: &str) -> Option<Value> {
    match t {
        "true" => return Some(Value::Bool(true)),
        "false" => return Some(Value::Bool(false)),
        "nan" | "inf" | "-inf" => return t.parse().ok().map(Value::float),
        _ => {}
    }
    if t.contains('r') {
        let mut parts = t.split('/');
        let big = |s: Option<&str>| -> Option<BigInt> { s?.strip_suffix('r')?.parse().ok() };
        let num = big(parts.next())?;
        let den = match parts.next() {
            Some(d) => big(Some(d))?,
            None => BigInt::from(1),
        };
        return Rat::new(num, den).map(Value::rat);
    }
    if t.contains(['.', 'e']) {
        return t.parse().ok().map(Value::float);
    }
    if t.is_empty()
        || !t
            .trim_start_matches('-')
            .chars()
            .all(|c| c.is_ascii_digit())
    {
        return None;
    }
    Value::int_text(t, 10)
}
