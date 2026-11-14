//! Verdicts on recursive type groups against values (plan item GROUP-oracle, DESIGN.md
//! sec:type_language): random systems of mutually recursive definitions, with tuples,
//! morphisms, `&` and `\`, are built as kernel groups, one per strongly connected component,
//! and each member's `Type::verdict` and `Type::is_empty` are compared with what a finite pool
//! of values shows. The oracle is the one of cross-review xs2 (Gemini, Q2Q3), ported to Rust.
//!
//! The pool holds the atoms of the system, 0 and 1, both booleans, finite tuples and closures.
//! A closure is a stored domain type and a body: a constant (which may be the closure itself or
//! a tuple holding it, as `f(x) = f`), the identity, the first or second component, divergence,
//! `x(x)` or `x(v)`. A closure is a member of `L .. U -> V` when its domain is within the bounds
//! and it terminates in `V` on every value of its domain. That reads the answer negatively, so
//! the oracle takes the alternating three-valued fixed point: `lo`, the values surely members,
//! and `hi`, the values possibly members; reads in a domain or on the right of `\` take the
//! other bound, and positive reads take the greatest fixed point, which a finite tuple cannot
//! sustain and a closure can. A definition is `I` when `lo` holds a value (a proof: the value
//! is shown), `E` when `hi` holds none, and `U` otherwise.
//!
//! An `E` is a proof only when the pool was built from every choice of a union arm and of a
//! divergent morphism, not from a sample: past the cap, a sample is drawn, and an `E` is rerun
//! with a pool `RERUN` times larger (R2_CLAUDE records a false `E` at a cap of 600 that a cap
//! of 2000 corrects). A kernel answer is wrong when it is `Empty` against an `I`, or `Inhabited`
//! against an `E` of a pool built from every choice.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Range;

use super::bes_families::{self, reference};
use super::judgments::{bodies, group};
use zed_kernel::types::bes::{Answer, decide};
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::{Rng, pick_seeds};
use zed_tests::scaling;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

// ---------------------------------------------------------------------------------------------
// Systems
// ---------------------------------------------------------------------------------------------

/// A type of a system of definitions; `Ref(i)` is definition `i`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum E {
    Atom(&'static str),
    Int,
    Bool,
    Empty,
    Top,
    Ref(usize),
    Tup(Vec<E>),
    /// `Mor(l, u, v)`: guarantee `l`, permission `u`, value type `v`.
    Mor(Box<E>, Box<E>, Box<E>),
    Union(Vec<E>),
    Diff(Box<E>, Box<E>),
    And(Vec<E>),
}

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |f: &mut fmt::Formatter<'_>, xs: &[E], sep: &str| {
            for (i, x) in xs.iter().enumerate() {
                if i > 0 {
                    f.write_str(sep)?;
                }
                write!(f, "{x}")?;
            }
            Ok(())
        };
        match self {
            E::Atom(a) => write!(f, "#{a}"),
            E::Int => f.write_str("int"),
            E::Bool => f.write_str("bool"),
            E::Empty => f.write_str("empty"),
            E::Top => f.write_str("top"),
            E::Ref(i) => write!(f, "R{i}"),
            E::Tup(xs) => {
                f.write_str("(")?;
                list(f, xs, ", ")?;
                f.write_str(if xs.len() == 1 { ",)" } else { ")" })
            }
            E::Mor(l, u, v) if l == u => write!(f, "(({l}) -> {v})"),
            E::Mor(l, u, v) => write!(f, "({l} .. {u} -> {v})"),
            E::Union(xs) => {
                f.write_str("(")?;
                list(f, xs, " | ")?;
                f.write_str(")")
            }
            E::Diff(a, b) => write!(f, "({a} \\ {b})"),
            E::And(xs) => {
                f.write_str("(")?;
                list(f, xs, " & ")?;
                f.write_str(")")
            }
        }
    }
}

fn exact(k: E, v: E) -> E {
    E::Mor(Box::new(k.clone()), Box::new(k), Box::new(v))
}

fn tup(xs: Vec<E>) -> E {
    E::Tup(xs)
}

fn diff(a: E, b: E) -> E {
    E::Diff(Box::new(a), Box::new(b))
}

/// The system as text, one definition after another.
fn show_system(sys: &[E]) -> String {
    let defs: Vec<String> = sys
        .iter()
        .enumerate()
        .map(|(i, d)| format!("R{i} = {d}"))
        .collect();
    defs.join("; ")
}

/// The definitions `e` names.
fn refs(e: &E, out: &mut Vec<usize>) {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match e {
            E::Ref(i) => out.push(*i),
            E::Tup(xs) | E::Union(xs) | E::And(xs) => stack.extend(xs),
            E::Mor(l, u, v) => stack.extend([&**l, &**u, &**v]),
            E::Diff(a, b) => stack.extend([&**a, &**b]),
            E::Atom(_) | E::Int | E::Bool | E::Empty | E::Top => {}
        }
    }
}

/// `e` as a kernel expression: a definition with a place `pos` in the component being built is a
/// reference into the group, any other one its type, which must have been built.
fn expr(e: &E, pos: &[Option<usize>], built: &[Option<Type>]) -> Option<Expr> {
    Some(match e {
        E::Atom(a) => Expr::Type(Type::atom(a)),
        E::Int => Expr::Type(Type::int()),
        E::Bool => Expr::Type(Type::bool()),
        E::Empty => Expr::Type(Type::empty()),
        E::Top => Expr::Type(Type::top()),
        E::Ref(i) => match pos[*i] {
            Some(k) => Expr::Ref(k, vec![]),
            None => Expr::Type(built[*i].clone()?),
        },
        E::Tup(xs) => Expr::Tuple(
            xs.iter()
                .map(|x| expr(x, pos, built))
                .collect::<Option<_>>()?,
        ),
        E::Union(xs) => Expr::Union(
            xs.iter()
                .map(|x| expr(x, pos, built))
                .collect::<Option<_>>()?,
        ),
        E::And(xs) => Expr::And(
            xs.iter()
                .map(|x| expr(x, pos, built))
                .collect::<Option<_>>()?,
        ),
        E::Diff(a, b) => Expr::Diff(
            Box::new(expr(a, pos, built)?),
            Box::new(expr(b, pos, built)?),
        ),
        E::Mor(l, u, v) => Expr::Morphism(
            Box::new(expr(l, pos, built)?),
            Box::new(expr(u, pos, built)?),
            Box::new(expr(v, pos, built)?),
        ),
    })
}

/// The kernel type of each definition: one `Group` per strongly connected component, each
/// after those it names, as a source file's mutually recursive `type` declarations are
/// grouped. `None` for a definition its group's admission rejects, and for every definition
/// that names one. Definition `i` is named `{tag}_{i}`, so systems do not share names. The
/// components are those of [`components`].
fn kernel(sys: &[E], tag: &str) -> Vec<Option<Type>> {
    kernel_named(sys, tag, None)
}

fn kernel_named(sys: &[E], tag: &str, names: Option<&[usize]>) -> Vec<Option<Type>> {
    let n = sys.len();
    let mut built: Vec<Option<Type>> = vec![None; n];
    // The place of each definition in the component being built, `None` outside it.
    let mut pos: Vec<Option<usize>> = vec![None; n];
    components(&ref_edges(sys), |comp| {
        for (k, &d) in comp.iter().enumerate() {
            pos[d] = Some(k);
        }
        let defs: Option<Vec<Def>> = comp
            .iter()
            .map(|&d| {
                expr(&sys[d], &pos, &built).map(|body| Def {
                    name: format!("{tag}_{}", names.map_or(d, |ns| ns[d])),
                    params: vec![],
                    body,
                })
            })
            .collect();
        if let Some(Ok(g)) = defs.map(Group::new) {
            for (k, t) in g.instance(vec![]).into_iter().enumerate() {
                built[comp[k]] = Some(t);
            }
        }
        for &d in comp {
            pos[d] = None;
        }
    });
    built
}

/// The definitions each definition of `sys` names, in the order [`refs`] finds them: the edges
/// of the system's reference graph.
fn ref_edges(sys: &[E]) -> Vec<Vec<usize>> {
    (sys.iter())
        .map(|d| {
            let mut out = Vec::new();
            refs(d, &mut out);
            out
        })
        .collect()
}

/// Calls `each` on every strongly connected component of the graph `edges`, its members in
/// increasing order, each component after every component it reaches.
///
/// Tarjan's algorithm (R. Tarjan, "Depth-first search and linear graph algorithms", SIAM
/// Journal on Computing 1(2), 1972) on an explicit stack of frames, so a long chain does not
/// overflow the thread's stack: O(V + E) for the search, and O(c log c) to sort a component of
/// c, where a search from each definition costs O(V (V + E)) and a pass per component
/// O(V^2 (V + E)). The sort is there so a group's definitions keep their order in the source.
fn components(edges: &[Vec<usize>], mut each: impl FnMut(&[usize])) {
    let n = edges.len();
    let (mut index, mut low) = (vec![usize::MAX; n], vec![0; n]);
    let (mut on_stack, mut stack) = (vec![false; n], Vec::new());
    let mut next = 0;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // Each frame is a definition and the number of its references followed so far.
        let mut frames = vec![(root, 0)];
        (index[root], low[root], next) = (next, next, next + 1);
        stack.push(root);
        on_stack[root] = true;
        while let Some(&(v, i)) = frames.last() {
            if let Some(&w) = edges[v].get(i) {
                let top = frames.len() - 1;
                frames[top].1 += 1;
                if index[w] == usize::MAX {
                    (index[w], low[w], next) = (next, next, next + 1);
                    stack.push(w);
                    on_stack[w] = true;
                    frames.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(u, _)) = frames.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] != index[v] {
                continue;
            }
            // The component is `v` and everything pushed after it, so this search from the
            // top costs the component's size.
            let at = stack
                .iter()
                .rposition(|&x| x == v)
                .expect("v is on the stack");
            let mut comp = stack.split_off(at);
            comp.sort_unstable();
            for &d in &comp {
                on_stack[d] = false;
            }
            each(&comp);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The oracle
// ---------------------------------------------------------------------------------------------

/// An interned type of the oracle; `Alias(x)` is a definition, whose body is `x`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Ty {
    Atom(usize),
    Int,
    Bool,
    Empty,
    Top,
    Alias(usize),
    Tup(Vec<usize>),
    Mor(usize, usize, usize),
    Union(Vec<usize>),
    Diff(usize, usize),
    And(Vec<usize>),
}

struct Types {
    tys: Vec<Ty>,
    ix: HashMap<Ty, usize>,
    /// The `Alias` of each definition.
    defs: Vec<usize>,
    atoms: Vec<&'static str>,
}

impl Types {
    fn new(sys: &[E]) -> Types {
        let mut ts = Types {
            tys: Vec::new(),
            ix: HashMap::new(),
            defs: Vec::new(),
            atoms: Vec::new(),
        };
        // The definitions' places come first, filled once their bodies are interned; they are
        // not interned themselves, so two definitions are two types.
        for _ in sys {
            ts.defs.push(ts.tys.len());
            ts.tys.push(Ty::Alias(usize::MAX));
        }
        for (i, e) in sys.iter().enumerate() {
            let body = ts.of(e);
            ts.tys[ts.defs[i]] = Ty::Alias(body);
        }
        ts
    }

    fn add(&mut self, t: Ty) -> usize {
        if let Some(&i) = self.ix.get(&t) {
            return i;
        }
        self.tys.push(t.clone());
        self.ix.insert(t, self.tys.len() - 1);
        self.tys.len() - 1
    }

    fn of(&mut self, e: &E) -> usize {
        match e {
            E::Atom(a) => {
                let i = match self.atoms.iter().position(|x| x == a) {
                    Some(i) => i,
                    None => {
                        self.atoms.push(a);
                        self.atoms.len() - 1
                    }
                };
                self.add(Ty::Atom(i))
            }
            E::Int => self.add(Ty::Int),
            E::Bool => self.add(Ty::Bool),
            E::Empty => self.add(Ty::Empty),
            E::Top => self.add(Ty::Top),
            E::Ref(i) => self.defs[*i],
            E::Tup(xs) => {
                let v = xs.iter().map(|x| self.of(x)).collect();
                self.add(Ty::Tup(v))
            }
            E::Union(xs) => {
                let v = xs.iter().map(|x| self.of(x)).collect();
                self.add(Ty::Union(v))
            }
            E::And(xs) => {
                let v = xs.iter().map(|x| self.of(x)).collect();
                self.add(Ty::And(v))
            }
            E::Diff(a, b) => {
                let (a, b) = (self.of(a), self.of(b));
                self.add(Ty::Diff(a, b))
            }
            E::Mor(l, u, v) => {
                let (l, u, v) = (self.of(l), self.of(u), self.of(v));
                self.add(Ty::Mor(l, u, v))
            }
        }
    }

    /// `t` with its definitions' names followed, or `None` on a cycle of names.
    fn resolve(&self, mut t: usize) -> Option<usize> {
        let mut seen = HashSet::new();
        while let Ty::Alias(x) = self.tys[t] {
            if !seen.insert(t) {
                return None;
            }
            t = x;
        }
        Some(t)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Body {
    Const(usize),
    Id,
    Fst,
    Snd,
    Diverge,
    SelfApp,
    AppArg(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    Atom(usize),
    Int(i64),
    Bool(bool),
    Tup(Vec<usize>),
    /// A closure: its domain type (`None` the empty domain) and body.
    Fn(Option<usize>, Body),
    /// A node being built.
    Hole,
}

/// The pool: each value once, by its structure or, for a value with a cycle through a closure,
/// by the text of its minimal graph (`seen`).
#[derive(Default)]
struct Pool {
    n: Vec<Node>,
    ix: HashMap<Node, usize>,
    seen: HashMap<String, usize>,
}

impl Pool {
    fn add(&mut self, x: Node) -> usize {
        if let Some(&i) = self.ix.get(&x) {
            return i;
        }
        self.n.push(x.clone());
        self.ix.insert(x, self.n.len() - 1);
        self.n.len() - 1
    }

    fn fresh(&mut self) -> usize {
        self.n.push(Node::Hole);
        self.n.len() - 1
    }

    fn show(&self, v: usize, depth: usize) -> String {
        if depth == 0 {
            return "…".into();
        }
        match &self.n[v] {
            Node::Atom(a) => format!("atom {a}"),
            Node::Int(i) => i.to_string(),
            Node::Bool(b) => b.to_string(),
            Node::Tup(xs) => {
                let xs: Vec<String> = xs.iter().map(|&x| self.show(x, depth - 1)).collect();
                format!("({})", xs.join(", "))
            }
            Node::Fn(d, b) => {
                let d = d.map_or("empty".into(), |d| format!("type {d}"));
                match b {
                    Body::Const(c) => format!("fn[{d}] -> {}", self.show(*c, depth - 1)),
                    Body::AppArg(c) => format!("fn[{d}] x({})", self.show(*c, depth - 1)),
                    o => format!("fn[{d}] {o:?}"),
                }
            }
            Node::Hole => "hole".into(),
        }
    }
}

/// Applies closures. The evaluator is deterministic, so meeting one application again before
/// it ends is a loop: divergence. The results are kept in a table of every pair of pool values,
/// read in each round of the fixed point.
// Complexity tradeoff: the table is quadratic in the pool, and pools are deduplicated to
// canonical values, so they stay near a thousand values at `CAP` and below two thousand at the
// rerun (1,709 at `CAP * RERUN` on the slowest generated system, seed 20 of the X14 family):
// some megabytes, against a hash map that made one system take 35 s.
struct Machine {
    nv: usize,
    memo: Vec<u32>,
}

const UNKNOWN: u32 = u32::MAX;
const DIVERGES: u32 = u32::MAX - 1;
const ON_THE_PATH: u32 = u32::MAX - 2;

impl Machine {
    fn new(nv: usize) -> Machine {
        assert!(
            nv < ON_THE_PATH as usize,
            "pool values are numbered below the markers"
        );
        Machine {
            nv,
            memo: vec![UNKNOWN; nv * nv],
        }
    }

    /// `c(x)`: `Some` result, or `None` for divergence or a stuck term. `x(x)` and `x(v)` are
    /// calls in tail position, so the application is a loop over the calls it makes.
    fn app(&mut self, p: &Pool, mut c: usize, mut x: usize) -> Option<usize> {
        let mut path = Vec::new();
        let r = loop {
            let at = c * self.nv + x;
            match self.memo[at] {
                UNKNOWN => {}
                DIVERGES | ON_THE_PATH => break None,
                r => break Some(r as usize),
            }
            self.memo[at] = ON_THE_PATH;
            path.push(at);
            let Node::Fn(_, b) = &p.n[c] else { break None };
            match *b {
                Body::Const(v) => break Some(v),
                Body::Id => break Some(x),
                Body::Fst => match &p.n[x] {
                    Node::Tup(v) if !v.is_empty() => break Some(v[0]),
                    _ => break None,
                },
                Body::Snd => match &p.n[x] {
                    Node::Tup(v) if v.len() > 1 => break Some(v[1]),
                    _ => break None,
                },
                Body::Diverge => break None,
                Body::SelfApp => c = x,
                Body::AppArg(v) => (c, x) = (x, v),
            }
        };
        for at in path {
            self.memo[at] = r.map_or(DIVERGES, |r| r as u32);
        }
        r
    }
}

/// One bound of the fixed point: for each type, which pool values it holds.
type Bound = Vec<Vec<bool>>;

/// The next value of the bound `pos` (`lo` or `hi`), reading `neg`, the other bound, where the
/// type is read negatively: in a domain, and on the right of `\`.
fn step(ts: &Types, p: &Pool, m: &mut Machine, pos: &Bound, neg: &Bound) -> Bound {
    let nv = p.n.len();
    let mut lists: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut out = vec![vec![false; nv]; ts.tys.len()];
    for (t, ty) in ts.tys.iter().enumerate() {
        // Whether a closure of domain `d` is within the bounds, the same for every body.
        let mut within: HashMap<Option<usize>, bool> = HashMap::new();
        for v in 0..nv {
            let node = &p.n[v];
            out[t][v] = match ty {
                Ty::Atom(a) => *node == Node::Atom(*a),
                Ty::Int => matches!(node, Node::Int(_)),
                Ty::Bool => matches!(node, Node::Bool(_)),
                Ty::Empty => false,
                Ty::Top => true,
                Ty::Alias(x) => pos[*x][v],
                Ty::Tup(c) => match node {
                    Node::Tup(x) if x.len() == c.len() => c.iter().zip(x).all(|(c, x)| pos[*c][*x]),
                    _ => false,
                },
                Ty::Union(c) => c.iter().any(|c| pos[*c][v]),
                Ty::And(c) => c.iter().all(|c| pos[*c][v]),
                Ty::Diff(a, b) => pos[*a][v] && !neg[*b][v],
                Ty::Mor(gl, gu, val) => {
                    let Node::Fn(d, _) = *node else {
                        continue;
                    };
                    let ok = *within.entry(d).or_insert_with(|| {
                        let in_d = |b: &Bound, x: usize| d.is_some_and(|d| b[d][x]);
                        let empty_l = ts.resolve(*gl).is_some_and(|l| ts.tys[l] == Ty::Empty);
                        let same_l = d == Some(*gl) || (d.is_none() && empty_l);
                        let same_u = d == Some(*gu);
                        (0..nv).all(|x| {
                            (same_l || !neg[*gl][x] || in_d(pos, x))
                                && (same_u || !in_d(neg, x) || pos[*gu][x])
                        })
                    });
                    match d {
                        Some(d) if ok => {
                            let xs = lists
                                .entry(d)
                                .or_insert_with(|| (0..nv).filter(|&x| neg[d][x]).collect());
                            xs.iter()
                                .all(|&x| m.app(p, v, x).is_some_and(|r| pos[*val][r]))
                        }
                        _ => ok,
                    }
                }
            };
        }
    }
    out
}

/// The alternating fixed point: `(lo, hi)`.
fn bounds(ts: &Types, p: &Pool) -> (Bound, Bound) {
    let (nt, nv) = (ts.tys.len(), p.n.len());
    let mut m = Machine::new(nv);
    let gfp = |m: &mut Machine, neg: &Bound| {
        let mut pos = vec![vec![true; nv]; nt];
        loop {
            let next = step(ts, p, m, &pos, neg);
            if next == pos {
                return pos;
            }
            pos = next;
        }
    };
    let (mut lo, mut hi) = (vec![vec![false; nv]; nt], vec![vec![true; nv]; nt]);
    loop {
        let next_lo = gfp(&mut m, &hi);
        let next_hi = gfp(&mut m, &next_lo);
        if next_lo == lo && next_hi == hi {
            return (lo, hi);
        }
        (lo, hi) = (next_lo, next_hi);
    }
}

/// A node of a value being built for one choice: a pool value, or a new node.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum At {
    Pool(usize),
    New(usize),
}

#[derive(Clone, Debug)]
enum Draft {
    Hole,
    Tup(Vec<At>),
    /// A closure of the given domain returning the value.
    Const(usize, At),
    /// A closure of the given domain that diverges.
    Diverge(usize),
}

fn draft_kids(d: &Draft) -> &[At] {
    match d {
        Draft::Tup(xs) => xs,
        Draft::Const(_, x) => std::slice::from_ref(x),
        Draft::Hole | Draft::Diverge(_) => &[],
    }
}

/// Whether the new node `root` is a finite value: no hole under it and no cycle of tuples.
fn finite(drafts: &[Draft], root: usize) -> bool {
    let mut seen = vec![false; drafts.len()];
    let mut stack = vec![root];
    while let Some(x) = stack.pop() {
        if std::mem::replace(&mut seen[x], true) {
            continue;
        }
        if matches!(drafts[x], Draft::Hole) {
            return false;
        }
        stack.extend(draft_kids(&drafts[x]).iter().filter_map(|k| match k {
            At::New(k) => Some(*k),
            At::Pool(_) => None,
        }));
    }
    // A cycle of tuple edges, by a depth-first search with colors from an explicit stack.
    let mut color = vec![0u8; drafts.len()];
    for s in (0..drafts.len()).filter(|&s| seen[s]) {
        if color[s] != 0 {
            continue;
        }
        let mut stack = vec![(s, 0usize)];
        color[s] = 1;
        while let Some((x, i)) = stack.last_mut() {
            let kids: &[At] = match &drafts[*x] {
                Draft::Tup(xs) => xs,
                _ => &[],
            };
            match kids.get(*i) {
                None => {
                    color[*x] = 2;
                    stack.pop();
                }
                Some(k) => {
                    *i += 1;
                    if let At::New(k) = *k {
                        match color[k] {
                            0 => {
                                color[k] = 1;
                                stack.push((k, 0));
                            }
                            1 => return false,
                            _ => {}
                        }
                    }
                }
            }
        }
    }
    true
}

/// The key of a draft node in a round of the partition: pool values are leaves; new nodes are
/// named by their class.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key {
    Tup(usize, Vec<At>),
    Const(usize, usize, At),
    Diverge(usize, usize),
}

/// Copies the finite value at new node `root` into the pool, merging nodes of equal values by
/// partition refinement (Moore), so the pool holds each value once.
fn import(drafts: &[Draft], root: usize, p: &mut Pool) -> usize {
    let mut reach = vec![root];
    let mut pos: HashMap<usize, usize> = HashMap::from([(root, 0)]);
    let mut i = 0;
    while i < reach.len() {
        for k in draft_kids(&drafts[reach[i]]) {
            if let At::New(k) = *k
                && !pos.contains_key(&k)
            {
                pos.insert(k, reach.len());
                reach.push(k);
            }
        }
        i += 1;
    }
    let n = reach.len();
    let mut class = vec![0usize; n];
    let named = |a: At, class: &[usize]| match a {
        At::New(k) => At::New(class[pos[&k]]),
        p => p,
    };
    loop {
        let mut keys: HashMap<Key, usize> = HashMap::new();
        let next: Vec<usize> = reach
            .iter()
            .enumerate()
            .map(|(i, &x)| {
                let key = match &drafts[x] {
                    Draft::Tup(xs) => {
                        Key::Tup(class[i], xs.iter().map(|&a| named(a, &class)).collect())
                    }
                    Draft::Const(d, a) => Key::Const(class[i], *d, named(*a, &class)),
                    Draft::Diverge(d) => Key::Diverge(class[i], *d),
                    Draft::Hole => unreachable!("a finite value has no hole"),
                };
                let fresh = keys.len();
                *keys.entry(key).or_insert(fresh)
            })
            .collect();
        if next == class {
            break;
        }
        class = next;
    }
    // The text of the class graph from the root, classes named in the order first met.
    let first: HashMap<usize, usize> = (0..n).rev().map(|i| (class[i], reach[i])).collect();
    let mut order = vec![class[0]];
    let mut name: HashMap<usize, usize> = HashMap::from([(class[0], 0)]);
    let mut text = String::new();
    let mut at = 0;
    while at < order.len() {
        let x = first[&order[at]];
        let word = |a: At, name: &mut HashMap<usize, usize>, order: &mut Vec<usize>| match a {
            At::Pool(v) => format!("p{v}"),
            At::New(k) => {
                let c = class[pos[&k]];
                let fresh = name.len();
                let e = *name.entry(c).or_insert(fresh);
                if e == fresh {
                    order.push(c);
                }
                format!("n{e}")
            }
        };
        let item = match &drafts[x] {
            Draft::Tup(xs) => {
                let w: Vec<String> = xs.iter().map(|&a| word(a, &mut name, &mut order)).collect();
                format!("T{};", w.join(","))
            }
            Draft::Const(d, a) => format!("C{d},{};", word(*a, &mut name, &mut order)),
            Draft::Diverge(d) => format!("D{d};"),
            Draft::Hole => unreachable!("a finite value has no hole"),
        };
        text.push_str(&item);
        at += 1;
    }
    if let Some(&v) = p.seen.get(&text) {
        return v;
    }
    let mut made: HashMap<usize, usize> = HashMap::new();
    for (i, &x) in reach.iter().enumerate() {
        made.entry(class[i]).or_insert_with(|| match drafts[x] {
            Draft::Diverge(d) => p.add(Node::Fn(Some(d), Body::Diverge)),
            _ => p.fresh(),
        });
    }
    let to = |a: At, made: &HashMap<usize, usize>| match a {
        At::Pool(v) => v,
        At::New(k) => made[&class[pos[&k]]],
    };
    for (i, &x) in reach.iter().enumerate() {
        let id = made[&class[i]];
        if p.n[id] != Node::Hole {
            continue;
        }
        p.n[id] = match &drafts[x] {
            Draft::Tup(xs) => Node::Tup(xs.iter().map(|&a| to(a, &made)).collect()),
            Draft::Const(d, a) => Node::Fn(Some(*d), Body::Const(to(*a, &made))),
            Draft::Diverge(_) | Draft::Hole => unreachable!("filled above, or not finite"),
        };
        p.ix.entry(p.n[id].clone()).or_insert(id);
    }
    let r = made[&class[0]];
    p.seen.insert(text, r);
    r
}

/// The pool of candidate values: the scalars; closures with generic bodies at each domain; for
/// each choice of a union arm per union type and of divergence per morphism type, one value per
/// tuple and morphism type, whose cycles pass through closures; then rounds that add tuples and
/// constant closures from the values surely in each type. The pool decides nothing: membership
/// is computed by `bounds`. Returns the pool and whether every choice was taken (else `cap`
/// choices are drawn from `seed`).
fn build_pool(ts: &Types, cap: usize, seed: u64) -> (Pool, bool) {
    let mut p = Pool::default();
    for a in 0..ts.atoms.len() {
        p.add(Node::Atom(a));
    }
    let i0 = p.add(Node::Int(0));
    p.add(Node::Int(1));
    let b0 = p.add(Node::Bool(true));
    p.add(Node::Bool(false));
    let base: Vec<usize> = (0..p.n.len()).collect();
    let empty = ts.tys.iter().position(|t| *t == Ty::Empty);
    let mut doms: Vec<Option<usize>> = vec![None];
    for ty in &ts.tys {
        if let Ty::Mor(l, u, _) = ty {
            for d in [*l, *u] {
                if Some(d) != empty && !doms.contains(&Some(d)) {
                    doms.push(Some(d));
                }
            }
        }
    }
    for &d in &doms {
        for b in [Body::Id, Body::Fst, Body::Snd, Body::Diverge, Body::SelfApp] {
            p.add(Node::Fn(d, b));
        }
        for &v in &base {
            p.add(Node::Fn(d, Body::Const(v)));
            p.add(Node::Fn(d, Body::AppArg(v)));
        }
    }
    let nt = ts.tys.len();
    let unions: Vec<usize> = (0..nt)
        .filter(|&t| matches!(ts.tys[t], Ty::Union(_)))
        .collect();
    let mors: Vec<usize> = (0..nt)
        .filter(|&t| matches!(ts.tys[t], Ty::Mor(..)))
        .collect();
    let arms = |u: usize| match &ts.tys[u] {
        Ty::Union(c) => c.len(),
        _ => unreachable!("listed as a union"),
    };
    // The number of choices, saturated: past `cap` only whether it is past matters.
    let total = unions
        .iter()
        .map(|&u| arms(u))
        .chain(mors.iter().map(|_| 2))
        .try_fold(1usize, |a, k| a.checked_mul(k));
    let exhaustive = total.is_some_and(|t| t <= cap);
    let count = if exhaustive {
        total.expect("checked above")
    } else {
        cap
    };
    let mut rng = Rng::new(seed);
    let shaped: Vec<usize> = (0..nt)
        .filter(|&t| matches!(ts.tys[t], Ty::Tup(_) | Ty::Mor(..)))
        .collect();
    for it in 0..count {
        let mut pick = vec![0usize; nt];
        let mut left = it;
        for &u in &unions {
            pick[u] = if exhaustive {
                let k = left % arms(u);
                left /= arms(u);
                k
            } else {
                rng.below(arms(u))
            };
        }
        for &m in &mors {
            pick[m] = if exhaustive {
                let k = left % 2;
                left /= 2;
                k
            } else {
                usize::from(rng.below(8) == 0)
            };
        }
        // One new node per tuple and morphism type under this choice.
        let mut node: Vec<Option<usize>> = vec![None; nt];
        for (k, &t) in shaped.iter().enumerate() {
            node[t] = Some(k);
        }
        // The node a type stands for under the choice: follow names, the chosen arm, the left of
        // `\` and the first of `&` to a tuple, a morphism or a scalar; `None` for `empty` or a
        // cycle of names and unions.
        let target = |mut t: usize| -> Option<At> {
            let mut seen = HashSet::new();
            loop {
                if !seen.insert(t) {
                    return None;
                }
                match &ts.tys[t] {
                    Ty::Alias(x) | Ty::Diff(x, _) => t = *x,
                    Ty::Union(c) => t = c[pick[t]],
                    Ty::And(c) => t = c[0],
                    Ty::Tup(_) | Ty::Mor(..) => return node[t].map(At::New),
                    Ty::Atom(a) => return Some(At::Pool(*a)),
                    Ty::Int | Ty::Top => return Some(At::Pool(i0)),
                    Ty::Bool => return Some(At::Pool(b0)),
                    Ty::Empty => return None,
                }
            }
        };
        let drafts: Vec<Draft> = shaped
            .iter()
            .map(|&t| match &ts.tys[t] {
                Ty::Tup(c) => c
                    .iter()
                    .map(|&x| target(x))
                    .collect::<Option<Vec<At>>>()
                    .map_or(Draft::Hole, Draft::Tup),
                Ty::Mor(l, ..) if pick[t] == 1 => Draft::Diverge(*l),
                Ty::Mor(l, _, v) => target(*v).map_or(Draft::Hole, |r| Draft::Const(*l, r)),
                _ => unreachable!("only tuple and morphism types have a node"),
            })
            .collect();
        for k in 0..drafts.len() {
            if finite(&drafts, k) {
                import(&drafts, k, &mut p);
            }
        }
    }
    // Rounds that add tuples and constants built from values surely in each type.
    // Complexity tradeoff: each round takes the first 6 values per component and 36 tuples per
    // tuple type, so the pool stays small enough to decide in the test's time; what is given up
    // is values the choices did not build, so an `E` is a proof only of the pool. The choices
    // (above) are what make an `E` from a pool of every choice the answer the tests rely on.
    // Naive version: every value per component, the product of the pool's sizes over a tuple
    // type's components each round; used: at most 36 tuples and 6 constants per type each round,
    // after building at most 6^w combinations for a tuple type of width w.
    for _ in 0..4 {
        let (lo, _) = bounds(ts, &p);
        let before = p.n.len();
        for ty in &ts.tys {
            match ty {
                Ty::Tup(c) => {
                    let opts: Vec<Vec<usize>> = c
                        .iter()
                        .map(|&x| (0..before).filter(|&v| lo[x][v]).take(6).collect())
                        .collect();
                    if opts.iter().any(Vec::is_empty) {
                        continue;
                    }
                    for c in first_tuples(&opts, 36) {
                        p.add(Node::Tup(c));
                    }
                }
                Ty::Mor(l, _, v) => {
                    for r in (0..before).filter(|&x| lo[*v][x]).take(6) {
                        p.add(Node::Fn(Some(*l), Body::Const(r)));
                    }
                }
                _ => {}
            }
        }
        if p.n.len() == before {
            break;
        }
    }
    (p, exhaustive)
}

/// The first `keep` tuples of the product of `opts`, the choices for each component in turn,
/// in the order of the product's rows: the last component varies fastest. The empty product has
/// one tuple, the empty one.
///
/// Complexity tradeoff: the naive form builds the whole product, `prod |opts[i]|` tuples
/// (`6^w` for a tuple type of `w` components here, 1.7 million at `w = 8`), and then keeps
/// `keep`. This one steps a counter with one digit per component, the last fastest, and builds
/// only the tuples kept: `O(keep * w)` time and memory. Nothing is given up; the tuples and their
/// order are those of the naive form (`the_first_tuples_are_those_of_the_whole_product`).
fn first_tuples(opts: &[Vec<usize>], keep: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::with_capacity(keep);
    if opts.iter().any(Vec::is_empty) {
        return out;
    }
    let mut digit = vec![0; opts.len()];
    while out.len() < keep {
        out.push(digit.iter().zip(opts).map(|(&d, o)| o[d]).collect());
        // The next row: raise the last digit that is not at its end and reset those after it.
        let Some(k) = (0..opts.len())
            .rev()
            .find(|&k| digit[k] + 1 < opts[k].len())
        else {
            break;
        };
        digit[k] += 1;
        digit[k + 1..].fill(0);
    }
    out
}

/// What the pool shows about a definition.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Seen {
    /// A value surely in it, shown.
    Member(String),
    /// No value possibly in it.
    None,
    /// Values possibly in it, none surely.
    Open,
}

struct Truth {
    seen: Vec<Seen>,
    /// Whether the pool was built from every choice, so that `Seen::None` is the answer.
    exhaustive: bool,
    pool: usize,
}

fn truth(sys: &[E], cap: usize) -> Truth {
    let ts = Types::new(sys);
    let (p, exhaustive) = build_pool(&ts, cap, 0x9E37_79B9_7F4A_7C15);
    let (lo, hi) = bounds(&ts, &p);
    let seen = ts
        .defs
        .iter()
        .map(|&t| match (0..p.n.len()).find(|&v| lo[t][v]) {
            Some(w) => Seen::Member(p.show(w, 5)),
            None if hi[t].iter().any(|&h| h) => Seen::Open,
            None => Seen::None,
        })
        .collect();
    Truth {
        seen,
        exhaustive,
        pool: p.n.len(),
    }
}

/// The first cap, and how many times larger the pool of a rerun is.
const CAP: usize = 100;
const RERUN: usize = 16;

// ---------------------------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------------------------

/// Cross-review X14's family: unions of `#stop`, pairs and `(int) -> R`.
fn gen_claude(g: &mut Rng) -> Vec<E> {
    let n = 2 + g.below(5);
    claude_of(g, n)
}

/// `n` definitions of the X14 family, each a union of up to three arms.
fn claude_of(g: &mut Rng, n: usize) -> Vec<E> {
    (0..n)
        .map(|_| {
            let alts: Vec<E> = (0..1 + g.below(3))
                .map(|_| match g.below(8) {
                    0 => E::Atom("stop"),
                    1..=4 => tup(vec![E::Ref(g.below(n)), E::Ref(g.below(n))]),
                    _ => exact(E::Int, E::Ref(g.below(n))),
                })
                .collect();
            one_or_union(alts)
        })
        .collect()
}

fn one_or_union(mut alts: Vec<E>) -> E {
    if alts.len() == 1 {
        alts.remove(0)
    } else {
        E::Union(alts)
    }
}

/// Partial morphisms, keys that are definitions, `\ #stop` and empty value types.
fn gen_mixed(g: &mut Rng) -> Vec<E> {
    let n = 2 + g.below(3);
    let r = |g: &mut Rng| E::Ref(g.below(n));
    let key = |g: &mut Rng| match g.below(7) {
        0 | 1 => E::Int,
        2 => E::Bool,
        3 => E::Atom("a"),
        4 => E::Empty,
        _ => r(g),
    };
    let val = |g: &mut Rng| match g.below(9) {
        0..=2 => r(g),
        3 => E::Int,
        4 => E::Empty,
        5 => tup(vec![r(g), r(g)]),
        6 => tup(vec![E::Int, r(g)]),
        7 => exact(E::Bool, E::Empty),
        _ => exact(E::Bool, r(g)),
    };
    (0..n)
        .map(|_| {
            let alts: Vec<E> = (0..1 + g.below(3))
                .map(|_| match g.below(12) {
                    0 => E::Atom("stop"),
                    1 | 2 => tup(vec![r(g), r(g)]),
                    3 => tup(vec![E::Int, r(g)]),
                    4 => E::Empty,
                    5 => {
                        let (k, v) = (key(g), val(g));
                        E::Mor(Box::new(E::Empty), Box::new(k), Box::new(v))
                    }
                    6 => diff(r(g), E::Atom("stop")),
                    _ => {
                        let (k, v) = (key(g), val(g));
                        exact(k, v)
                    }
                })
                .collect();
            one_or_union(alts)
        })
        .collect()
}

/// Layered: domains and subtracted types name earlier definitions only, so most systems are
/// admitted and negative reads cross groups.
fn gen_layer(g: &mut Rng) -> Vec<E> {
    let n = 3 + g.below(4);
    (0..n)
        .map(|i| {
            let up = |g: &mut Rng| {
                if i == 0 { E::Int } else { E::Ref(g.below(i)) }
            };
            let r = |g: &mut Rng| E::Ref(g.below(i + 1));
            let val = |g: &mut Rng| match g.below(7) {
                0 | 1 => r(g),
                2 => tup(vec![r(g), r(g)]),
                3 => tup(vec![r(g), up(g)]),
                4 => tup(vec![r(g), exact(E::Bool, E::Empty)]),
                5 if i > 0 => tup(vec![E::Ref(i), diff(up(g), up(g))]),
                _ => E::Int,
            };
            let alts: Vec<E> = (0..1 + g.below(2))
                .map(|_| match g.below(10) {
                    0 => E::Atom("stop"),
                    1..=3 => exact(up(g), E::Empty),
                    4..=6 => exact(E::Int, val(g)),
                    7 => {
                        let (u, w) = (up(g), up(g));
                        exact(u, w)
                    }
                    8 => {
                        let (u, v) = (up(g), val(g));
                        tup(vec![exact(u, E::Empty), v])
                    }
                    _ => tup(vec![E::Int, val(g)]),
                })
                .collect();
            one_or_union(alts)
        })
        .collect()
}

/// Meets and differences: `&` of definitions and tuples, and a product of unions less tuples of
/// atoms or earlier definitions, so that a member may lie only in a cell of the box that no one
/// tuple type holds (`(#a | R, #b | R) \ ((#a, #b) | (#b, #a))`).
fn gen_cells(g: &mut Rng) -> Vec<E> {
    let n = 2 + g.below(4);
    let atom = |g: &mut Rng| E::Atom(["a", "b"][g.below(2)]);
    (0..n)
        .map(|i| {
            let r = |g: &mut Rng| E::Ref(g.below(n));
            let up = |g: &mut Rng| {
                if i == 0 || g.below(2) == 0 {
                    atom(g)
                } else {
                    E::Ref(g.below(i))
                }
            };
            let alts: Vec<E> = (0..1 + g.below(3))
                .map(|_| match g.below(11) {
                    0 => E::Atom("stop"),
                    1 => tup(vec![r(g), r(g)]),
                    2 => {
                        let side = |g: &mut Rng| E::Union(vec![atom(g), r(g)]);
                        let (x, y) = (side(g), side(g));
                        let (a, b) = (up(g), up(g));
                        diff(tup(vec![x, y]), tup(vec![a, b]))
                    }
                    3 => {
                        let side = || E::Union(vec![E::Atom("a"), E::Atom("b")]);
                        let rows = (0..1 + g.below(3))
                            .map(|_| tup(vec![atom(g), atom(g)]))
                            .collect();
                        let base = tup(vec![side(), E::Union(vec![side(), r(g)])]);
                        diff(base, E::Union(rows))
                    }
                    4 => E::And(vec![r(g), tup(vec![E::Union(vec![atom(g), r(g)]), E::Int])]),
                    5 => E::And(vec![r(g), r(g)]),
                    6 => exact(E::Int, r(g)),
                    7 => diff(r(g), tup(vec![atom(g), up(g)])),
                    8 => E::And(vec![r(g), exact(E::Int, r(g))]),
                    9 => tup(vec![E::Int, r(g)]),
                    _ => atom(g),
                })
                .collect();
            one_or_union(alts)
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------------------------

#[derive(Default, Debug)]
struct Tally {
    systems: usize,
    members: usize,
    rejected: usize,
    empty: usize,
    inhabited: usize,
    refused: usize,
    /// Kernel answers the pool leaves open.
    open: usize,
    /// `E` answers from a sampled pool, rerun at a larger one.
    reruns: usize,
    /// `Inhabited` against an `E` of a sampled pool at the larger cap too: not a proof either
    /// way.
    unsettled: usize,
    /// `is_empty` answers inhabited for a type the pool proves empty: allowed, since it may
    /// count an empty type as inhabited.
    conservative: usize,
    /// Refusals of a type the pool shows a member of: allowed, a verdict may refuse.
    missed: usize,
    /// The members the verdicts sent to the search, their group's decider leaving them open
    /// (`Type::members_searched`): a member asked counts each member of its group so sent.
    searched: usize,
    /// Each refused member, in the order asked: its index, what the pool showed of it (`I` a
    /// member, `E` no value of a pool built from every choice, `U` neither) and the reason.
    refusals: Vec<(usize, char, Refusal)>,
}

/// Each member of system `sys` against the pool; panics on a wrong answer.
fn compare(sys: &[E], tag: &str, tally: &mut Tally) {
    let types = kernel(sys, tag);
    let first = truth(sys, CAP);
    let mut rerun: Option<Truth> = None;
    tally.systems += 1;
    for (i, t) in types.iter().enumerate() {
        let Some(t) = t else {
            tally.rejected += 1;
            continue;
        };
        tally.members += 1;
        Type::forget_emptiness();
        let before = Type::members_searched();
        let verdict = t.verdict();
        tally.searched += Type::members_searched() - before;
        Type::forget_emptiness();
        let empty = t.is_empty();
        let mut seen = &first;
        if first.seen[i] == Seen::None && !first.exhaustive && verdict == Verdict::Inhabited {
            tally.reruns += 1;
            seen = rerun.get_or_insert_with(|| truth(sys, CAP * RERUN));
        }
        let at = || {
            format!(
                "{tag}: R{i} of {} (pool {}, every choice: {})",
                show_system(sys),
                seen.pool,
                seen.exhaustive
            )
        };
        match &seen.seen[i] {
            Seen::Member(w) => {
                assert!(verdict != Verdict::Empty, "{}: Empty, but holds {w}", at());
                assert!(!empty, "{}: is_empty, but holds {w}", at());
                if matches!(verdict, Verdict::Refused(_)) {
                    tally.missed += 1;
                    eprintln!("missed: {verdict:?}: {}: holds {w}", at());
                }
            }
            Seen::None if seen.exhaustive => {
                assert!(
                    verdict != Verdict::Inhabited,
                    "{}: Inhabited, but the pool shows no value",
                    at()
                );
                if !empty {
                    tally.conservative += 1;
                }
            }
            Seen::None => {
                if verdict == Verdict::Inhabited {
                    tally.unsettled += 1;
                    eprintln!("unsettled: {}", at());
                }
            }
            Seen::Open => tally.open += 1,
        }
        match verdict {
            Verdict::Empty => tally.empty += 1,
            Verdict::Inhabited => tally.inhabited += 1,
            Verdict::Refused(why) => {
                tally.refused += 1;
                let shown = match seen.seen[i] {
                    Seen::Member(_) => 'I',
                    Seen::None if seen.exhaustive => 'E',
                    Seen::None | Seen::Open => 'U',
                };
                tally.refusals.push((i, shown, why));
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Seeds 0 to 1500, every refusal listed (plan items TESTS-l01_23-group-oracle-sweep and
// TEST-bench-move-l0123)
// ---------------------------------------------------------------------------------------------

/// A refusal a sweep expects: the seed, the member, what the pool showed of it (as in
/// `Tally::refusals`) and the reason.
type Listed = (u64, usize, char, Refusal);

/// The seeds `fixed`, asked each run, and `count` more of `all` drawn from `rng` and printed with
/// `what`. Each test that asks these makes `rng` with [`Rng::fresh`], so that it asks other
/// seeds each run (author P169: random tests run fewer cases, with a new seed each run;
/// `ZED_TEST_SEED` repeats a run); each swept the whole of `all` until TEST-bench-move-l0123.
fn seeds_of(
    rng: &mut Rng,
    what: &str,
    fixed: Range<u64>,
    all: Range<u64>,
    count: usize,
) -> Vec<u64> {
    let mut seeds: Vec<u64> = fixed.collect();
    seeds.extend(pick_seeds(rng, what, all, count));
    seeds.sort();
    seeds.dedup();
    seeds
}

/// The seeds a sweep of family `name` runs: 8 of the seeds `listed` names and 24 of 0 to 1500,
/// drawn from a generator made with [`Rng::fresh`] and printed (author P169: random tests run
/// fewer cases, with a new seed each run; `ZED_TEST_SEED` repeats a run). Every seed of the range
/// was swept, and its refusals listed, as of TEST-bench-move-l0123, when each sweep ran all
/// 1500 seeds in 2 to 13 s. The seed `both`, whose system has a member shown empty and one
/// shown inhabited, is asked every run. Returns the seeds and the seed of the generator, for
/// failure messages.
fn sweep_seeds(name: &str, listed: &[Listed], both: u64) -> (Vec<u64>, u64) {
    let (mut rng, seed) = Rng::fresh(&format!("{name} sweep"));
    let mut named: Vec<u64> = listed.iter().map(|&(seed, ..)| seed).collect();
    named.dedup();
    let picks = pick_seeds(&mut rng, "listed", 0..named.len() as u64, 8);
    let mut seeds = pick_seeds(&mut rng, name, 0..1500, 24);
    seeds.extend(picks.iter().map(|&i| named[i as usize]));
    seeds.push(both);
    seeds.sort();
    seeds.dedup();
    (seeds, seed)
}

/// The systems `generate` gives for `seeds`, each against the pool, and every refusal among
/// their verdicts on `listed` (the entries of `listed` for other seeds are not read). Panics on
/// a wrong answer, on a refusal not listed, on a listed refusal that is now a verdict or has
/// another reason or member, so that the lists shrink as the checker decides more, and unless
/// the systems have members the pool shows empty and members it shows inhabited. `rng_seed`,
/// the seed [`sweep_seeds`] drew them with, is named in each message.
fn sweep_listed(
    name: &str,
    generate: fn(&mut Rng) -> Vec<E>,
    seeds: &[u64],
    listed: &[Listed],
    rng_seed: u64,
) {
    let mut tally = Tally::default();
    let mut got: Vec<Listed> = Vec::new();
    for &seed in seeds {
        let sys = generate(&mut Rng::new(seed));
        compare(&sys, &format!("{name}{seed}"), &mut tally);
        got.extend(
            (tally.refusals.drain(..)).map(|(member, shown, why)| (seed, member, shown, why)),
        );
    }
    got.sort_by_key(|&(seed, member, ..)| (seed, member));
    let want: Vec<Listed> = (listed.iter().copied())
        .filter(|(seed, ..)| seeds.contains(seed))
        .collect();
    eprintln!("{name}: {tally:?}");
    assert!(
        tally.members > 0 && tally.empty > 0 && tally.inhabited > 0,
        "{name} (ZED_TEST_SEED={rng_seed}): {tally:?}"
    );
    let new: Vec<_> = got.iter().filter(|r| !want.contains(r)).collect();
    let gone: Vec<_> = want.iter().filter(|r| !got.contains(r)).collect();
    assert!(
        new.is_empty() && gone.is_empty(),
        "{name} {seeds:?} (ZED_TEST_SEED={rng_seed}): refused and not listed: {new:?}; listed and not refused so: \
         {gone:?}; the refusals now:\n{}",
        (got.iter())
            .map(|r| format!("    {r:?},"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// The lists as of plan item TESTS-l01_23-group-oracle-sweep (2026-11-12), seeds 300 to 1500: 39
// refusals among the 13,751 admitted members of 4,800 systems, 35 of members the pool shows
// inhabited (`I`), 4 of members it leaves open (`U`), none of a member it proves empty. Seeds 0
// to 300, listed by TEST-bench-move-l0123 (2026-11-14): 11 more, all layered, all `I` (seeds 0
// to 200 had been swept with these counted, 4 and 3, not listed). On 2026-11-07 (plan item
// EMPTY-key-search) the sweep of seeds 300 to 1500 refused 54 members shown inhabited: layered
// 34, cells 9, X14 7, mixed 4.

/// The X14 family: every member decided.
const LISTED_CLAUDE: &[Listed] = &[];
/// Partial morphisms: every member decided.
const LISTED_MIXED: &[Listed] = &[];
/// Layered groups: each refused member is, or reads, a function type whose value type is a pair
/// of itself and a difference of two definitions, such as `R3 = (int) -> (R3, (R2 \ R0))` of
/// seed 799 with `R0 = (int) -> int` and `R2 = ((int) -> R2) | ((R1) -> R0)`; the pool's value
/// is a closure that returns a pair holding itself. All are refused `NoWitness` (STATUS.md Open
/// points, GROUP-oracle: the refusals in groups holding `\` or `&`).
const LISTED_LAYER: &[Listed] = &[
    (16, 3, 'I', Refusal::NoWitness),
    (37, 3, 'I', Refusal::NoWitness),
    (45, 4, 'I', Refusal::NoWitness),
    (73, 4, 'I', Refusal::NoWitness),
    (125, 2, 'I', Refusal::NoWitness),
    (125, 4, 'I', Refusal::NoWitness),
    (171, 3, 'I', Refusal::NoWitness),
    (230, 3, 'I', Refusal::NoWitness),
    (232, 3, 'I', Refusal::NoWitness),
    (236, 2, 'I', Refusal::NoWitness),
    (293, 3, 'I', Refusal::NoWitness),
    (332, 4, 'I', Refusal::NoWitness),
    (440, 3, 'I', Refusal::NoWitness),
    (508, 5, 'I', Refusal::NoWitness),
    (626, 3, 'I', Refusal::NoWitness),
    (642, 3, 'I', Refusal::NoWitness),
    (642, 4, 'U', Refusal::NoWitness),
    (692, 5, 'I', Refusal::NoWitness),
    (764, 3, 'I', Refusal::NoWitness),
    (764, 4, 'U', Refusal::NoWitness),
    (799, 3, 'I', Refusal::NoWitness),
    (815, 4, 'I', Refusal::NoWitness),
    (831, 4, 'I', Refusal::NoWitness),
    (857, 3, 'I', Refusal::NoWitness),
    (955, 3, 'I', Refusal::NoWitness),
    (975, 2, 'I', Refusal::NoWitness),
    (975, 3, 'U', Refusal::NoWitness),
    (987, 3, 'I', Refusal::NoWitness),
    (987, 4, 'I', Refusal::NoWitness),
    (996, 3, 'I', Refusal::NoWitness),
    (1043, 4, 'I', Refusal::NoWitness),
    (1048, 2, 'I', Refusal::NoWitness),
    (1051, 4, 'I', Refusal::NoWitness),
    (1068, 4, 'I', Refusal::NoWitness),
    (1068, 5, 'I', Refusal::NoWitness),
    (1147, 4, 'I', Refusal::NoWitness),
    (1229, 4, 'I', Refusal::NoWitness),
    (1241, 4, 'I', Refusal::NoWitness),
    (1326, 2, 'I', Refusal::NoWitness),
    (1354, 4, 'I', Refusal::NoWitness),
    (1421, 2, 'I', Refusal::NoWitness),
    (1421, 4, 'I', Refusal::NoWitness),
    (1446, 3, 'I', Refusal::NoWitness),
    (1454, 4, 'I', Refusal::NoWitness),
    (1466, 2, 'I', Refusal::NoWitness),
    (1483, 4, 'I', Refusal::NoWitness),
    (1485, 4, 'U', Refusal::NoWitness),
    (1498, 5, 'I', Refusal::NoWitness),
];
/// Meets and differences: one system, `R0 = (R0, R2) | (((#b | R1), (#b | R2)) \ (#b, #b))`,
/// `R1 = (int, R2) | #stop | (int, R0)`, `R2 = (R0, R0)`, whose `R0` and `R2` the pool shows
/// inhabited from every choice, refused `Fork`.
const LISTED_CELLS: &[Listed] = &[(1140, 0, 'I', Refusal::Fork), (1140, 2, 'I', Refusal::Fork)];

// The seed of each family asked every run because its system has both a member the pool shows
// empty and one it shows inhabited, so that each sweep meets both answers, which
// `sweep_listed` requires. Of seeds 0 to 300 (2026-11-14), the share of systems with an empty
// member was 113 of 300 for X14, 75 for partial morphisms, 271 for layered groups and 31 for
// meets and differences; at 31 of 300, 25 drawn seeds miss every one about 7 times in 100, as
// a run of `meets_and_differences_seeds_agree_or_are_listed` did (TEST-bench-move-l0123).
// Seeds and their empty and inhabited members: X14 0 (1, 1), partial morphisms 1 (3, 1),
// layered 0 (2, 4), meets and differences 13 (2, 3).
const BOTH_CLAUDE: u64 = 0;
const BOTH_MIXED: u64 = 1;
const BOTH_LAYER: u64 = 0;
const BOTH_CELLS: u64 = 13;

#[test]
fn x14_family_seeds_agree_or_are_listed() {
    let (seeds, seed) = sweep_seeds("claude", LISTED_CLAUDE, BOTH_CLAUDE);
    sweep_listed("claude", gen_claude, &seeds, LISTED_CLAUDE, seed);
}

#[test]
fn partial_morphism_seeds_agree_or_are_listed() {
    let (seeds, seed) = sweep_seeds("mixed", LISTED_MIXED, BOTH_MIXED);
    sweep_listed("mixed", gen_mixed, &seeds, LISTED_MIXED, seed);
}

#[test]
fn layered_seeds_agree_or_are_listed() {
    let (seeds, seed) = sweep_seeds("layer", LISTED_LAYER, BOTH_LAYER);
    sweep_listed("layer", gen_layer, &seeds, LISTED_LAYER, seed);
}

#[test]
fn meets_and_differences_seeds_agree_or_are_listed() {
    let (seeds, seed) = sweep_seeds("cells", LISTED_CELLS, BOTH_CELLS);
    sweep_listed("cells", gen_cells, &seeds, LISTED_CELLS, seed);
}

// ---------------------------------------------------------------------------------------------
// Fixed cases
// ---------------------------------------------------------------------------------------------

/// What the kernel and the pool say of each definition of `sys`: `None` where admission
/// rejects it, else the verdict and the pool's letter (`I`, `E` or `U`).
fn both(sys: &[E], tag: &str) -> Vec<Option<(Verdict, char)>> {
    let mut tally = Tally::default();
    compare(sys, tag, &mut tally);
    let seen = truth(sys, CAP * RERUN);
    kernel(sys, tag)
        .iter()
        .zip(&seen.seen)
        .map(|(t, s)| {
            t.as_ref().map(|t| {
                Type::forget_emptiness();
                let letter = match s {
                    Seen::Member(_) => 'I',
                    Seen::None => 'E',
                    Seen::Open => 'U',
                };
                (t.verdict(), letter)
            })
        })
        .collect()
}

fn r(i: usize) -> E {
    E::Ref(i)
}

/// `W = (W) -> int` is inhabited (`fn w(x) = 0` on domain `W`). Its meet with `(empty) -> int`
/// is empty: a closure has one domain, and `W` is not empty. Written in the group, as
/// `W = ((W) -> int) & ((empty) -> int)`, the recursive occurrence is a guaranteed domain
/// under `&`, a constrained place, so admission rejects it, as it rejects `W_andTop`
/// (`admission.rs`); read with no admission, it has no fixed point.
#[test]
fn w_and_a_morphism_on_the_empty_domain() {
    let empty_fn = exact(E::Empty, E::Int);
    let apart = [exact(r(0), E::Int), E::And(vec![r(0), empty_fn.clone()])];
    assert_eq!(
        both(&apart, "wand"),
        [Some((Verdict::Inhabited, 'I')), Some((Verdict::Empty, 'E'))]
    );
    let inside = [E::And(vec![exact(r(0), E::Int), empty_fn])];
    assert_eq!(both(&inside, "wand_in"), [None]);
    let defs = vec![Def {
        name: "wand_in_check".into(),
        params: vec![],
        body: Expr::And(vec![
            Expr::exact(Expr::Ref(0, vec![]), Expr::Type(Type::int())),
            Expr::exact(Expr::Type(Type::empty()), Expr::Type(Type::int())),
        ]),
    }];
    assert!(
        Group::new(defs).is_err(),
        "the meet in the group is rejected"
    );
    // `W_andTop`, `W = ((W) -> int) & top`, is rejected the same way.
    assert_eq!(
        both(&[E::And(vec![exact(r(0), E::Int), E::Top])], "wtop"),
        [None]
    );
    // The definition has no fixed point: if `W` is empty, the closure on the empty domain is in
    // both, so `W` is not empty; if `W` holds a value, a closure in `(W) -> int` has a domain
    // that is not empty, so it is not in `(empty) -> int`, and `W` is empty. The pool shows
    // this as a value possibly in `W` and none surely in it, which is why admission rejects it.
    assert!(matches!(truth(&inside, CAP).seen[..], [Seen::Open]));
}

/// A morphism on a cycle: a cycle through a value type is inhabited (`f(x) = (f, 0)`), unless a
/// tuple on it is empty; through a guarantee, `(W) -> int` is inhabited; a cycle of two
/// morphisms through a pair is inhabited, and empty when the pair's other side is empty.
#[test]
fn a_morphism_on_a_cycle() {
    let i = Some((Verdict::Inhabited, 'I'));
    let e = Some((Verdict::Empty, 'E'));
    // T = (int) -> (T, int)
    assert_eq!(
        both(&[exact(E::Int, tup(vec![r(0), E::Int]))], "cyc_a"),
        [i]
    );
    // T = (int) -> (T, U), U = (int, U): U is empty, so T has no result to give.
    let sys = [
        exact(E::Int, tup(vec![r(0), r(1)])),
        tup(vec![E::Int, r(1)]),
    ];
    assert_eq!(both(&sys, "cyc_b"), [e, e]);
    // A = (int) -> B, B = (A, #stop | A): two members on one cycle through a morphism.
    let sys = [
        exact(E::Int, r(1)),
        tup(vec![r(0), E::Union(vec![E::Atom("stop"), r(0)])]),
    ];
    assert_eq!(both(&sys, "cyc_c"), [i, i]);
    // A = (int) -> B, B = (A, C), C = (C, A): the tuple cycle through C empties all three.
    let sys = [
        exact(E::Int, r(1)),
        tup(vec![r(0), r(2)]),
        tup(vec![r(2), r(0)]),
    ];
    assert_eq!(both(&sys, "cyc_d"), [e, e, e]);
    // W = (W) -> int, and V = (int) -> (V | W): the cycle runs through a guarantee.
    let sys = [
        exact(r(0), E::Int),
        exact(E::Int, E::Union(vec![r(1), r(0)])),
    ];
    assert_eq!(both(&sys, "cyc_e"), [i, i]);
}

/// A member split across box cells: the product `(#a | #b | L, #a | #b | L)` less the two
/// tuples `(#a, #b)` and `(#b, #a)` holds `(#a, #a)`, which lies in one cell of each component;
/// less every pair of atoms, it holds only pairs with a list `L`, and with `L` empty (a cycle
/// through a tuple) it is empty.
#[test]
fn a_member_split_across_box_cells() {
    let atoms = || E::Union(vec![E::Atom("a"), E::Atom("b")]);
    let side = |l: usize| E::Union(vec![atoms(), r(l)]);
    let pairs = |rows: &[(&'static str, &'static str)]| {
        E::Union(
            rows.iter()
                .map(|&(x, y)| tup(vec![E::Atom(x), E::Atom(y)]))
                .collect(),
        )
    };
    let all = [("a", "a"), ("a", "b"), ("b", "a"), ("b", "b")];
    let i = Some((Verdict::Inhabited, 'I'));
    let e = Some((Verdict::Empty, 'E'));
    // L = #stop | (int, L)
    let list = E::Union(vec![E::Atom("stop"), tup(vec![E::Int, r(1)])]);
    let sys = [
        diff(tup(vec![side(1), side(1)]), pairs(&all[1..3])),
        list.clone(),
    ];
    assert_eq!(both(&sys, "cells_a"), [i, i]);
    let sys = [diff(tup(vec![side(1), side(1)]), pairs(&all)), list];
    assert_eq!(both(&sys, "cells_b"), [i, i]);
    // L = (int, L): empty, so the product less every pair of atoms is empty.
    let sys = [
        diff(tup(vec![side(1), side(1)]), pairs(&all)),
        tup(vec![E::Int, r(1)]),
    ];
    assert_eq!(both(&sys, "cells_c"), [e, e]);
    // The product names itself: P = (#a | #b | P, #a | #b) \ every pair of atoms. A member is
    // a pair whose left is a member, so none is finite.
    let sys = [diff(tup(vec![side(0), atoms()]), pairs(&all))];
    assert_eq!(both(&sys, "cells_d"), [e]);
}

// ---------------------------------------------------------------------------------------------
// Seeded systems of the families against the classical solver
// ---------------------------------------------------------------------------------------------

/// `random(seed, rate, n)` over 40 seeds drawn from a generator made with [`Rng::fresh`] and
/// printed with `what` (`ZED_TEST_SEED` repeats a run), and over many rates and sizes: every
/// answer `decide` gives agrees with the classical solver of the Büchi game, and so does every
/// verdict of the group the definitions admit; `is_empty` never calls an inhabited member empty.
/// The two tests swept seeds 0 to 79 until TEST-l0124-fixed-seeds.
fn seeded(what: &str) {
    let (mut rng, rng_seed) = Rng::fresh(what);
    let seeds = pick_seeds(&mut rng, what, 0..u64::MAX, 40);
    let (mut decided, mut refused, mut groups, mut verdicts) = (0, 0, 0, 0);
    for rate in [0, 2, 5, 9, 14, 18] {
        for n in [2, 3, 5, 8, 13, 21] {
            for &seed in &seeds {
                let g = bes_families::random(seed, rate, n);
                let at = format!("random({seed}, {rate}, {n}), ZED_TEST_SEED={rng_seed}");
                let want = reference::answers(&g);
                for (v, a) in decide(&g.bes()).answers.iter().enumerate() {
                    match a {
                        Answer::Empty => assert!(!want[v], "{at}: node {v} decided empty"),
                        Answer::Inhabited => assert!(want[v], "{at}: node {v} decided inhabited"),
                        Answer::Refused => {
                            refused += 1;
                            continue;
                        }
                    }
                    decided += 1;
                }
                let Ok(types) = group(bodies(&g)) else {
                    continue;
                };
                groups += 1;
                for (v, t) in types.iter().enumerate() {
                    Type::forget_emptiness();
                    match t.verdict() {
                        Verdict::Empty => assert!(!want[v], "{at}: node {v} has verdict Empty"),
                        Verdict::Inhabited => {
                            assert!(want[v], "{at}: node {v} has verdict Inhabited")
                        }
                        Verdict::Refused(_) => {}
                    }
                    Type::forget_emptiness();
                    assert!(!t.is_empty() || !want[v], "{at}: node {v} counted empty");
                    verdicts += 1;
                }
            }
        }
    }
    eprintln!("decided {decided}, refused {refused}; groups admitted {groups}, members {verdicts}");
    // Over 4000 fresh seeds, each summed over the 36 rates and sizes, `decide` decided 311.1
    // answers a seed (standard deviation 4.0, fewest 274) and the definitions of 21.6 systems a
    // seed were admitted as a group (standard deviation 6.1, fewest 6); no seed gave zero of
    // either, so 40 seeds cannot.
    assert!(
        decided > 0 && groups > 0,
        "decided {decided}, groups {groups}, ZED_TEST_SEED={rng_seed}"
    );
}

#[test]
fn seeded_random_systems_agree_with_the_reference_0() {
    seeded("random systems against the reference, first");
}

#[test]
fn seeded_random_systems_agree_with_the_reference_1() {
    seeded("random systems against the reference, second");
}

/// `n` definitions in one group, `R_i = (R_j, R0) | (R_{i+1}, #stop)` with `j` random and
/// `R_{n-1} = (R_j, R0) | #stop`: every definition is inhabited, by a chain as long as the
/// group, so a search from `R0` reads every definition.
fn chain_of(g: &mut Rng, n: usize) -> Vec<E> {
    (0..n)
        .map(|i| {
            let back = tup(vec![E::Ref(g.below(n)), E::Ref(0)]);
            let next = if i + 1 < n {
                tup(vec![E::Ref(i + 1), E::Atom("stop")])
            } else {
                E::Atom("stop")
            };
            E::Union(vec![back, next])
        })
        .collect()
}

/// Every member of a chain group of `n` is inhabited, by a chain of up to `n` values; before
/// the search kept a failure only until a type it read got a value, all but 8 of 512 were
/// refused. The verdicts agree whatever order the members are asked in, and with the verdict
/// of each member asked alone, for a few members. The chain of 512 is
/// `bench::every_member_of_a_long_chain_is_inhabited` (TEST-bench-move-l0123, author P178).
fn every_member_of_a_chain_is_inhabited(n: usize) {
    let ts: Vec<Type> = kernel(&chain_of(&mut Rng::new(7), n), "long_chain")
        .into_iter()
        .map(|t| t.expect("a chain group is admitted"))
        .collect();
    Type::forget_emptiness();
    let forward: Vec<Verdict> = ts.iter().map(Type::verdict).collect();
    Type::forget_emptiness();
    let mut backward: Vec<Verdict> = ts.iter().rev().map(Type::verdict).collect();
    backward.reverse();
    assert_eq!(
        forward, backward,
        "the verdicts depend on the order they are asked in"
    );
    for (i, v) in forward.iter().enumerate() {
        assert_eq!(*v, Verdict::Inhabited, "R{i} of the chain");
    }
    for i in [0, 1, n / 2 - 1, n - 2, n - 1] {
        Type::forget_emptiness();
        assert_eq!(ts[i].verdict(), forward[i], "R{i} asked alone");
    }
}

#[test]
fn every_member_of_a_short_chain_is_inhabited() {
    every_member_of_a_chain_is_inhabited(16);
}

/// Two X14 groups whose values the shared search of plan item VERDICT-group-share missed, by
/// the order it builds them in (plan item REP-path-memo). In `claude210` a closure's value type
/// is the meet of its morphism types, the unfolding of `R0`, while `R0` itself is being built;
/// in `claude118` the closure `(int) -> R1` inside `R3` is reached after `R1` failed on the path
/// through `R0`, which was being built, and `R1` is a member its group decided inhabited.
#[test]
fn a_closure_returns_a_member_built_or_decided_inhabited() {
    let stop = || E::Atom("stop");
    let claude210 = vec![
        E::Union(vec![tup(vec![r(0), r(0)]), tup(vec![r(3), r(2)])]),
        E::Union(vec![exact(E::Int, r(2)), stop()]),
        exact(E::Int, r(0)),
        tup(vec![r(2), r(2)]),
    ];
    let claude118 = vec![
        E::Union(vec![tup(vec![r(0), r(1)]), tup(vec![r(2), r(3)])]),
        tup(vec![r(2), r(0)]),
        E::Union(vec![exact(E::Int, r(2)), tup(vec![r(1), r(1)])]),
        E::Union(vec![
            tup(vec![r(2), r(1)]),
            exact(E::Int, r(1)),
            tup(vec![r(1), r(1)]),
        ]),
        E::Union(vec![
            exact(E::Int, r(4)),
            tup(vec![r(3), r(1)]),
            tup(vec![r(4), r(2)]),
        ]),
    ];
    for (sys, tag) in [(claude210, "c210"), (claude118, "c118")] {
        let mut tally = Tally::default();
        compare(&sys, tag, &mut tally);
        assert_eq!(
            (tally.missed, tally.inhabited),
            (0, sys.len()),
            "{tag}: {tally:?}"
        );
    }
}

/// A layered group (seed 1335) whose member `R4 = (R3) -> empty` is a closure never called: its
/// key type `R3` is empty, which only a search proves, since the group holds `R1 \ R1` and its
/// decider does not decide it (plan item EMPTY-key-search). Each phase of that search proves
/// `R3` empty again; a type proved empty again must not start another phase, or the search
/// never ends.
#[test]
fn a_key_type_proved_empty_again_ends_the_search() {
    let int_to_empty = || exact(E::Int, E::Empty);
    let sys = vec![
        E::Union(vec![int_to_empty(), int_to_empty()]),
        tup(vec![
            exact(r(0), E::Empty),
            tup(vec![r(1), exact(E::Bool, E::Empty)]),
        ]),
        exact(
            E::Int,
            tup(vec![r(2), E::Diff(Box::new(r(1)), Box::new(r(1)))]),
        ),
        E::Union(vec![
            tup(vec![E::Int, r(0)]),
            exact(E::Int, tup(vec![r(1), r(2)])),
        ]),
        exact(r(3), E::Empty),
    ];
    let mut tally = Tally::default();
    compare(&sys, "layer1335", &mut tally);
    assert_eq!(
        (tally.empty, tally.inhabited, tally.missed),
        (4, 1, 0),
        "{tally:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// Groups the decider does not decide (plan item VERDICT-group-roots)
// ---------------------------------------------------------------------------------------------

/// `sys` with each body `b` written `b \ #none`, which holds the same values: a recursive
/// occurrence under `\` makes the decider refuse the group (`rec::judge`), so every member is
/// decided by the search, with all members of its group as roots of one search.
fn undecided(sys: Vec<E>) -> Vec<E> {
    sys.into_iter().map(|b| diff(b, E::Atom("none"))).collect()
}

/// `e` with each `Ref(i)` made `Ref(to[i])`.
fn renamed(e: &E, to: &[usize]) -> E {
    let all = |xs: &[E]| xs.iter().map(|x| renamed(x, to)).collect();
    let one = |x: &E| Box::new(renamed(x, to));
    match e {
        E::Ref(i) => E::Ref(to[*i]),
        E::Tup(xs) => E::Tup(all(xs)),
        E::Union(xs) => E::Union(all(xs)),
        E::And(xs) => E::And(all(xs)),
        E::Mor(l, u, v) => E::Mor(one(l), one(u), one(v)),
        E::Diff(a, b) => E::Diff(one(a), one(b)),
        E::Atom(_) | E::Int | E::Bool | E::Empty | E::Top => e.clone(),
    }
}

/// The verdict of each admitted definition of `types`, each asked as a unit's checker asks it:
/// with the kept results dropped first.
fn alone(types: &[Option<Type>]) -> Vec<Option<Verdict>> {
    (types.iter())
        .map(|t| {
            t.as_ref().map(|t| {
                Type::forget_emptiness();
                t.verdict()
            })
        })
        .collect()
}

/// The verdicts of `types` asked one after another in `order`, keeping results between them, as
/// a batch run checks many units.
fn in_order(types: &[Option<Type>], order: &[usize]) -> Vec<Option<Verdict>> {
    Type::forget_emptiness();
    let mut got = vec![None; types.len()];
    for &i in order {
        got[i] = types[i].as_ref().map(Type::verdict);
    }
    got
}

/// Every order of `0..n`, by Heap's algorithm, for small `n`.
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut p: Vec<usize> = (0..n).collect();
    let (mut c, mut out, mut i) = (vec![0; n], vec![p.clone()], 1);
    while i < n {
        if c[i] < i {
            p.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            out.push(p.clone());
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    out
}

/// The members of a group asked in every order give the same verdicts, each the verdict it has
/// when asked alone (a unit checked by itself) and in a batch: groups of three in all six
/// orders, and with their definitions written in all six orders, larger groups in every
/// rotation. Groups the decider refuses (`\ #none` on each body) and groups it decides. The
/// X14, meet-and-difference and layered systems are of 40 seeds of each family drawn from a
/// generator made with [`Rng::fresh`] (`ZED_TEST_SEED` repeats a run); they were of seeds 0 to
/// 39 until TEST-l0124-fixed-seeds, the meets and differences until FAIL-print-height-cycle-seed,
/// before which about 1 in 10,000 other seeds made `kernel` panic. The chain of 64 and the X14
/// system of 24 are recorded cases.
#[test]
fn verdicts_do_not_depend_on_the_order_members_are_asked_in() {
    let (mut rng, rng_seed) = Rng::fresh("members asked in every order");
    let mut systems: Vec<(String, Vec<E>)> = Vec::new();
    for seed in pick_seeds(&mut rng, "x14", 0..u64::MAX, 40) {
        let sys = claude_of(&mut Rng::new(seed), 3);
        systems.push((format!("x14_{seed}"), sys.clone()));
        systems.push((format!("x14u_{seed}"), undecided(sys)));
    }
    for seed in pick_seeds(&mut rng, "cells", 0..u64::MAX, 40) {
        systems.push((format!("cells{seed}"), gen_cells(&mut Rng::new(seed))));
    }
    for seed in pick_seeds(&mut rng, "layer", 0..u64::MAX, 40) {
        systems.push((format!("layer{seed}"), gen_layer(&mut Rng::new(seed))));
    }
    systems.push(("chainu".into(), undecided(chain_of(&mut Rng::new(7), 64))));
    systems.push(("x14u".into(), undecided(claude_of(&mut Rng::new(5), 24))));
    let (mut members, mut orders) = (0, 0);
    for (tag, sys) in &systems {
        let types = kernel(sys, tag);
        let want = alone(&types);
        let n = sys.len();
        let all: Vec<Vec<usize>> = if n <= 3 {
            permutations(n)
        } else {
            (0..n)
                .map(|k| (0..n).map(|i| (i + k) % n).collect())
                .collect()
        };
        for order in &all {
            assert_eq!(
                in_order(&types, order),
                want,
                "{tag}: asked in the order {order:?}: {}, ZED_TEST_SEED={rng_seed}",
                show_system(sys)
            );
            orders += 1;
        }
        if n == 3 {
            // Definition k of the rewritten system is definition order[k] of `sys`.
            for (p, order) in all.iter().enumerate() {
                let mut to = vec![0; n];
                for (k, &i) in order.iter().enumerate() {
                    to[i] = k;
                }
                let moved: Vec<E> = order.iter().map(|&i| renamed(&sys[i], &to)).collect();
                let got = alone(&kernel(&moved, &format!("{tag}_p{p}")));
                let want: Vec<_> = order.iter().map(|&i| want[i]).collect();
                assert_eq!(
                    got,
                    want,
                    "{tag}: definitions in the order {order:?}: {}, ZED_TEST_SEED={rng_seed}",
                    show_system(&moved)
                );
            }
        }
        members += want.iter().flatten().count();
    }
    eprintln!("{members} members, {orders} orders");
}

/// Every member of a chain group of `n` that the decider refuses is inhabited, by a chain of up
/// to `n` values, decided by one search with all `n` as roots. The chain of 512 is
/// `bench::every_member_of_an_undecided_long_chain_is_inhabited` (TEST-bench-move-l0123,
/// author P178).
fn every_member_of_an_undecided_chain_is_inhabited(n: usize) {
    let ts = kernel(&undecided(chain_of(&mut Rng::new(7), n)), "long_chain_u");
    for (i, v) in in_order(&ts, &(0..ts.len()).collect::<Vec<_>>())
        .iter()
        .enumerate()
    {
        assert_eq!(*v, Some(Verdict::Inhabited), "R{i} of the chain");
    }
}

#[test]
fn every_member_of_an_undecided_short_chain_is_inhabited() {
    every_member_of_an_undecided_chain_is_inhabited(16);
}

/// The definitions of the largest group of `sys`, those that reach each other, in order:
/// [`largest_component`] of its references.
fn largest_group(sys: &[E]) -> Vec<usize> {
    largest_component(&ref_edges(sys))
}

/// The largest strongly connected component of `edges` that holds a cycle (two or more
/// members, or one that names itself), its members in increasing order, or none when no
/// component holds one. Of two such components of one size, the one holding the larger
/// member. That is the answer of [`largest_component_by_walks`], which this replaced
/// (TEST-largest-group-scc), and the test `largest_component_agrees_with_walks` holds the two
/// equal.
///
/// Complexity tradeoff: the walk from each node that this replaced costs O(V (V + E)) time and
/// a V-by-V table, which held the benchmark
/// `bench::the_verdicts_of_the_largest_undecided_x14_group_scale` at 1024 definitions; the
/// components of Tarjan's algorithm ([`components`]) cost O(V + E) and O(c log c) to sort a
/// component of c, so O((V + E) log V) at worst, and O(V) memory. Nothing is given up.
fn largest_component(edges: &[Vec<usize>]) -> Vec<usize> {
    let mut best: Vec<usize> = Vec::new();
    components(edges, |comp| {
        let cyclic = comp.len() > 1 || edges[comp[0]].contains(&comp[0]);
        if cyclic && (comp.len(), comp.last()) > (best.len(), best.last()) {
            best = comp.to_vec();
        }
    });
    best
}

/// [`largest_component`] by a walk from each node, O(V (V + E)) time and a V-by-V table: the
/// helper `largest_group` was this until TEST-largest-group-scc, kept as the reference that
/// `largest_component_agrees_with_walks` compares with at small sizes. For each node, the nodes
/// it and they reach (itself only when it is on a cycle); the longest such list, the last one
/// of the longest when they tie.
fn largest_component_by_walks(edges: &[Vec<usize>]) -> Vec<usize> {
    let n = edges.len();
    let reach: Vec<Vec<bool>> = (0..n)
        .map(|s| {
            let mut seen = vec![false; n];
            let mut stack = edges[s].clone();
            while let Some(v) = stack.pop() {
                if !std::mem::replace(&mut seen[v], true) {
                    stack.extend(&edges[v]);
                }
            }
            seen
        })
        .collect();
    (0..n)
        .map(|i| {
            (0..n)
                .filter(|&j| reach[i][j] && reach[j][i])
                .collect::<Vec<_>>()
        })
        .max_by_key(Vec::len)
        .unwrap_or_default()
}

/// `largest_component` gives what the walk from each node gave: on the corner cases, each with
/// its answer written out, on 3000 random graphs of up to 12 nodes and 3 edges each, and on
/// the largest group of X14 systems of up to 24 definitions.
#[test]
fn largest_component_agrees_with_walks() {
    let cases = [
        ("no nodes", vec![], vec![]),
        ("one node", vec![vec![]], vec![]),
        ("a node that names itself", vec![vec![0]], vec![0]),
        ("a chain", vec![vec![1], vec![2], vec![]], vec![]),
        ("a cycle", vec![vec![1], vec![2], vec![0]], vec![0, 1, 2]),
        (
            "a chain into a cycle",
            vec![vec![1], vec![2], vec![1]],
            vec![1, 2],
        ),
        (
            "a pair and a self-loop",
            vec![vec![0], vec![2], vec![1]],
            vec![1, 2],
        ),
        (
            "two pairs",
            vec![vec![1], vec![0], vec![3], vec![2]],
            vec![2, 3],
        ),
        // Tarjan's algorithm emits {2, 3} before {0, 1}, which reaches it.
        (
            "a pair that reaches a pair",
            vec![vec![1, 2], vec![0], vec![3], vec![2]],
            vec![2, 3],
        ),
        // Tarjan's algorithm emits {1, 2} before {0, 3}; the larger member decides the tie.
        (
            "two pairs, one around the other",
            vec![vec![3, 1], vec![2], vec![1], vec![0]],
            vec![0, 3],
        ),
        (
            "a reference named twice",
            vec![vec![1, 1], vec![0, 0]],
            vec![0, 1],
        ),
    ];
    for (what, edges, want) in &cases {
        assert_eq!(largest_component(edges), *want, "{what}");
        assert_eq!(largest_component_by_walks(edges), *want, "{what} by walks");
    }
    let (mut rng, seed) = Rng::fresh("largest component");
    for _ in 0..3000 {
        let n = rng.below(13);
        let edges: Vec<Vec<usize>> = (0..n)
            .map(|_| (0..rng.below(4)).map(|_| rng.below(n)).collect())
            .collect();
        assert_eq!(
            largest_component(&edges),
            largest_component_by_walks(&edges),
            "seed {seed}: {edges:?}"
        );
    }
    for n in [1, 2, 8, 24] {
        let sys = undecided(claude_of(&mut rng, n));
        let edges = ref_edges(&sys);
        assert_eq!(
            largest_group(&sys),
            largest_component_by_walks(&edges),
            "seed {seed}, n = {n}: {}",
            show_system(&sys)
        );
    }
}

/// A definition outside a group the decider refuses reads each member of it by the group's
/// verdict and the value the group's search built (plan item VERDICT-group-readers): its
/// verdict agrees with the values, and with every order of the questions. In the layered system
/// of seed 316, `R3 = (int, R0) | ((R2) -> empty)` holds the function on the empty `R2`, and
/// reads the open member `R0` through `R2` and `R1`; a search of its own that decided `R0`
/// again called `R3` empty, where the same system with the decider's verdicts called it
/// inhabited.
///
/// Each family asks seeds 0 and 1 and 4 more of 0 to 100, drawn afresh each run; it asked
/// seeds 0 to 3 and 8 more until TEST-bench-move-l0123 (author P169: correctness tests well
/// under 1 s alone), when the test took 0.56 to 0.98 s alone on a loaded machine.
#[test]
fn readers_of_undecided_groups_agree_with_the_values() {
    let sys = undecided(gen_layer(&mut Rng::new(316)));
    let types = kernel(&sys, "readers316");
    assert_eq!(
        alone(&types),
        [
            Verdict::Empty,
            Verdict::Inhabited,
            Verdict::Empty,
            Verdict::Inhabited
        ]
        .map(Some),
        "{}",
        show_system(&sys)
    );
    let (mut rng, _) = Rng::fresh("readers of undecided groups");
    let gens: [fn(&mut Rng) -> Vec<E>; 4] = [gen_claude, gen_mixed, gen_layer, gen_cells];
    for (name, g) in ["claude", "mixed", "layer", "cells"].into_iter().zip(gens) {
        for seed in seeds_of(&mut rng, name, 0..2, 0..100, 4) {
            let sys = undecided(g(&mut Rng::new(seed)));
            let tag = format!("readers-{name}{seed}");
            let types = kernel(&sys, &tag);
            let got = alone(&types);
            let truth = truth(&sys, CAP);
            for (i, v) in got.iter().enumerate() {
                let at = || format!("{tag}: R{i} of {}", show_system(&sys));
                match (&truth.seen[i], v) {
                    (Seen::Member(w), Some(Verdict::Empty)) => {
                        panic!("{}: Empty, but holds {w}", at())
                    }
                    (Seen::None, Some(Verdict::Inhabited)) if truth.exhaustive => {
                        panic!("{}: Inhabited, but the pool shows no value", at())
                    }
                    _ => {}
                }
            }
            let n = types.len();
            let forward: Vec<usize> = (0..n).collect();
            let backward: Vec<usize> = (0..n).rev().collect();
            for order in [forward, backward] {
                assert_eq!(
                    in_order(&types, &order),
                    got,
                    "{tag}: in the order {order:?}"
                );
            }
        }
    }
}

/// A chain of n groups, each one definition `Ri = (Ri, #stop) | (R(i+1), int)` that reads the
/// next, ending in `#stop`; with `open`, every body is written `b \ #none`, which the decider
/// leaves open.
fn chain_of_groups(n: usize, open: bool) -> Vec<E> {
    (0..n)
        .map(|i| {
            let next = if i + 1 < n {
                tup(vec![E::Ref(i + 1), E::Int])
            } else {
                E::Atom("stop")
            };
            let b = E::Union(vec![tup(vec![E::Ref(i), E::Atom("stop")]), next]);
            if open { diff(b, E::Atom("none")) } else { b }
        })
        .collect()
}

/// A chain of 8 groups (`chain_of_groups`), as the decider decides them and with every body
/// written `b \ #none`, asked of the first member and of a tuple outside the groups that holds
/// it, on the test's own thread. The chain of 1000 groups on a thread of 1 MiB, which shows the
/// groups are decided without nesting one search per group on the stack, is
/// `bench::a_chain_of_groups_is_decided_on_a_small_stack` (TEST-bench-move-l0123, author P178).
#[test]
fn a_short_chain_of_groups_is_decided() {
    for open in [false, true] {
        let sys = chain_of_groups(8, open);
        let first = kernel(&sys, "chain")[0].clone().expect("admitted");
        let outside = Type::tuple(vec![first.clone(), Type::int()]);
        for t in [first, outside] {
            Type::forget_emptiness();
            let v = t.verdict();
            assert_eq!(v, Verdict::Inhabited, "with every body \\ #none: {open}");
        }
    }
}

// ---------------------------------------------------------------------------------------------
// `is_empty` against the values (plan item EMPTY-nonstrict-unsound)
// ---------------------------------------------------------------------------------------------

/// `R3 = (R2) -> empty` over `R2 = (R1) -> empty`, `R1 = (R0) -> empty` and the empty
/// `R0 = ((int) -> (R0, (bool) -> empty)) \ #none`, which the decider leaves to the search. `R1`
/// holds a closure that is never called, as `R0` is empty; so `R2`, whose key type `R1` has a
/// value and whose value type has none, is empty, and `R3` holds a closure that is never called.
/// `R0` is proved empty only when the first phase of the search ends; in the next one each
/// answer starts again from empty, and `R1` was read as empty before it was decided again, and
/// taken as empty for good, which made `R2` hold a closure and `R3` empty.
#[test]
fn a_type_decided_again_is_not_read_as_empty_before_it_is() {
    let sys = vec![
        diff(
            exact(E::Int, tup(vec![E::Ref(0), exact(E::Bool, E::Empty)])),
            E::Atom("none"),
        ),
        exact(E::Ref(0), E::Empty),
        exact(E::Ref(1), E::Empty),
        exact(E::Ref(2), E::Empty),
    ];
    let types = kernel(&sys, "late");
    let empty: Vec<bool> = (types.iter())
        .map(|t| {
            Type::forget_emptiness();
            t.as_ref().expect("admitted").is_empty()
        })
        .collect();
    assert_eq!(empty, [true, false, true, false], "{}", show_system(&sys));
    assert_eq!(
        alone(&types),
        [
            Verdict::Empty,
            Verdict::Inhabited,
            Verdict::Empty,
            Verdict::Inhabited
        ]
        .map(Some),
        "{}",
        show_system(&sys)
    );
}

/// The layered system of seed 316 with every body written `b \ #none`: `R3 = (int, R0) |
/// ((R2) -> empty)` holds the closure on the empty `R2`, and `is_empty` says so, as the verdict
/// does (plan item VERDICT-group-readers).
#[test]
fn the_layered_system_316_is_not_called_empty() {
    let sys = undecided(gen_layer(&mut Rng::new(316)));
    let types = kernel(&sys, "empty316");
    let empty: Vec<bool> = (types.iter())
        .map(|t| {
            Type::forget_emptiness();
            t.as_ref().expect("admitted").is_empty()
        })
        .collect();
    assert_eq!(empty, [true, false, true, false], "{}", show_system(&sys));
}

/// Each system `generate` gives for `seeds`, as written and with every body `b \ #none` (so the
/// search decides each group, not the decider): `is_empty` never calls a member empty that the
/// pool shows a value of. Gives how many members were checked.
fn never_empty_with_a_value(name: &str, generate: fn(&mut Rng) -> Vec<E>, seeds: &[u64]) -> usize {
    let mut checked = 0;
    for &seed in seeds {
        let sys = generate(&mut Rng::new(seed));
        // `b \ #none` holds the values of `b`, so one pool shows both forms.
        let seen = truth(&sys, CAP).seen;
        for (form, sys) in [("", sys.clone()), ("-", undecided(sys))] {
            let tag = format!("never-{name}{form}{seed}");
            for (i, t) in kernel(&sys, &tag).iter().enumerate() {
                let (Some(t), Seen::Member(w)) = (t, &seen[i]) else {
                    continue;
                };
                Type::forget_emptiness();
                assert!(
                    !t.is_empty(),
                    "{tag}: R{i} of {}: is_empty, but holds {w}",
                    show_system(&sys)
                );
                checked += 1;
            }
        }
    }
    eprintln!("{name} {seeds:?}: {checked} members with a value checked");
    checked
}

#[test]
fn x14_family_is_never_called_empty_with_a_value() {
    let (mut rng, _) = Rng::fresh("never empty: claude");
    let seeds = seeds_of(&mut rng, "claude", 0..4, 0..600, 16);
    assert!(never_empty_with_a_value("claude", gen_claude, &seeds) > 0);
}

#[test]
fn partial_morphisms_are_never_called_empty_with_a_value() {
    let (mut rng, _) = Rng::fresh("never empty: mixed");
    let seeds = seeds_of(&mut rng, "mixed", 0..4, 0..600, 16);
    assert!(never_empty_with_a_value("mixed", gen_mixed, &seeds) > 0);
}

#[test]
fn layered_systems_are_never_called_empty_with_a_value() {
    let (mut rng, _) = Rng::fresh("never empty: layer");
    let seeds = seeds_of(&mut rng, "layer", 0..8, 0..600, 32);
    assert!(never_empty_with_a_value("layer", gen_layer, &seeds) > 0);
}

#[test]
fn meets_and_differences_are_never_called_empty_with_a_value() {
    let (mut rng, _) = Rng::fresh("never empty: cells");
    let seeds = seeds_of(&mut rng, "cells", 0..8, 0..600, 32);
    assert!(never_empty_with_a_value("cells", gen_cells, &seeds) > 0);
}

/// The system of [`a_type_decided_again_is_not_read_as_empty_before_it_is`] with `n` morphism
/// types above `R0`, each the key type of the next: `R(k)` is empty at an even `k` and holds a
/// closure at an odd one. The types above `R0` are decided again in the phase after `R0` is
/// proved empty, and `is_empty` of `R(n - 1)`, which holds a closure, does work of order
/// `n log n`.
fn key_chain(n: usize) -> Vec<Type> {
    let mut sys = vec![diff(
        exact(E::Int, tup(vec![E::Ref(0), exact(E::Bool, E::Empty)])),
        E::Atom("none"),
    )];
    sys.extend((0..n).map(|k| exact(E::Ref(k), E::Empty)));
    (kernel(&sys, "key_chain").into_iter())
        .map(|t| t.expect("admitted"))
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Printing the members (item SURFACE-cycle)
// ---------------------------------------------------------------------------------------------

/// Panics unless `t` prints in the surface syntax (`Type::surface`) as text the parser accepts:
/// the type, each definition as a unit's statement, every name it uses defined. Returns the
/// text.
fn prints_as_syntax(t: &Type, what: &str) -> String {
    let s = t.surface();
    assert!(s.exact, "{what}: {s}");
    let accepts = |text: &str, start: &str| {
        let tokens = lex_fence(text).unwrap_or_else(|e| panic!("{what}: {text}: {e:?}"));
        parse(text, &tokens, start, TOP).unwrap_or_else(|e| panic!("{what}: {text}: {e:?}"));
    };
    let is_name = |word: &str| {
        word.len() > 1 && word.starts_with('T') && word[1..].bytes().all(|b| b.is_ascii_digit())
    };
    accepts(&s.root, "Type");
    let defined: HashSet<&str> = s.defs.iter().map(|(name, _)| name.as_str()).collect();
    // Item PRINT-group-site-defs: the whole text is the definitions as a user declares them,
    // a line each, and then the type.
    let whole = s.to_string();
    let (decls, root) = whole.rsplit_once('\n').unwrap_or(("", &whole));
    assert_eq!(root, s.root, "{what}: {whole}");
    accepts(&format!("{decls}\ntype Printed = {root};"), "Unit");
    for (name, body) in &s.defs {
        accepts(&format!("type {name} = {body};"), "Unit");
        // A definition that is only another name would be a second name for one type.
        assert!(!is_name(body), "{what}: {name} = {body} in {s}");
    }
    for text in s.defs.iter().map(|(_, body)| body).chain([&s.root]) {
        for word in text.split(|c: char| !c.is_alphanumeric() && c != '_') {
            assert!(
                !is_name(word) || defined.contains(word),
                "{what}: {word} in {s}"
            );
        }
    }
    s.to_string()
}

/// Every member of the systems of `meets_and_differences_are_never_called_empty_with_a_value`
/// prints. A member's unfolding and a part of its body kept unevaluated, such as `#a | #b |
/// R0` in `R0 = ((#a | #b), (#a | #b | R0)) \ (#b, #a)`, share the tuple part of `R0`, so the
/// printer meets that part again below itself, through the recursive type of the part kept
/// unevaluated: 503 of these 1364 members stopped the printer, which ordered the parts by the
/// order its walk left them in.
///
/// The systems are of 600 seeds drawn from a generator made with [`Rng::fresh`]
/// (`ZED_TEST_SEED` repeats a run). They were seeds 0 to 599, with 1364 members, until
/// FAIL-print-height-cycle-seed: before it, about 1 in 10,000 other seeds made `kernel` panic in
/// `heights` (print.rs) while it built the group. Over 166 runs of 600 fresh seeds the count of
/// members had mean 1342.9, standard deviation 75.1, least 1162 and most 1552
/// (TEST-l0124-fixed-seeds), so more than 900 is asked, about 5.9 deviations under the mean.
#[test]
fn every_member_of_systems_of_meets_and_differences_prints_as_syntax() {
    let (mut rng, rng_seed) = Rng::fresh("members of meets and differences print");
    let mut members = 0;
    for seed in pick_seeds(&mut rng, "cells", 0..u64::MAX, 600) {
        let sys = gen_cells(&mut Rng::new(seed));
        for (form, sys) in [("", sys.clone()), ("-", undecided(sys))] {
            let tag = format!("printed-cells{form}{seed}");
            for (i, t) in kernel(&sys, &tag).iter().enumerate() {
                let Some(t) = t else { continue };
                let what = format!(
                    "{tag}: R{i} of {}, ZED_TEST_SEED={rng_seed}",
                    show_system(&sys)
                );
                prints_as_syntax(t, &what);
                members += 1;
            }
        }
    }
    assert!(members > 900, "{members} members, ZED_TEST_SEED={rng_seed}");
}

#[test]
fn a_member_whose_tuple_part_its_body_shares_prints_as_definitions() {
    // R0 = ((#a | #b), (#a | #b | R0)) \ (#b, #a)
    let ab = || E::Union(vec![E::Atom("a"), E::Atom("b")]);
    let sys = [diff(
        tup(vec![ab(), E::Union(vec![ab(), E::Ref(0)])]),
        tup(vec![E::Atom("b"), E::Atom("a")]),
    )];
    let r0 = kernel(&sys, "shares").remove(0).expect("admitted");
    assert_eq!(
        prints_as_syntax(&r0, "R0"),
        "type T1 = T2 | #a | #b;\ntype T2 = (#a | #b, T1) \\ (#b, #a);\nT2"
    );
    // Two such cycles: the shared `#a | #b` is named once, and each part names the other.
    assert_eq!(
        prints_as_syntax(&shared_chain(2, false, "chain-two"), "a chain of 2"),
        concat!(
            "type T1 = #a | #b;\ntype T2 = T4 | #a | #b;\n",
            "type T3 = ((T1, T2) \\ (#b, #a)) | #a | #b;\ntype T4 = (T1, T3) \\ (#b, #a);\nT4"
        )
    );
}

/// A chain of `n` definitions, each a pair whose second component is `#a | #b` or the next
/// definition, the last's the first: `R(k) = ((#a | #b), (#a | #b | R(k + 1))) \ (#b, #a)`.
/// When `marked`, the last definition's second component also holds `#c`, so no two
/// definitions unfold alike and the chain is `n` types; otherwise it is one.
fn shared_chain(n: usize, marked: bool, tag: &str) -> Type {
    let ab = || E::Union(vec![E::Atom("a"), E::Atom("b")]);
    let sys: Vec<E> = (0..n)
        .map(|k| {
            let mut second = vec![ab(), E::Ref((k + 1) % n)];
            if marked && k == n - 1 {
                second.push(E::Atom("c"));
            }
            diff(
                tup(vec![ab(), E::Union(second)]),
                tup(vec![E::Atom("b"), E::Atom("a")]),
            )
        })
        .collect();
    kernel(&sys, tag).remove(0).expect("admitted")
}

// ---------------------------------------------------------------------------------------------
// Order of the search (GROUP-search-hang, GROUP-closure-order)
// ---------------------------------------------------------------------------------------------

/// `sys` with its definitions written in `order`: definition k of the result is definition
/// `order[k]` of `sys`, its references renamed to match.
fn moved(sys: &[E], order: &[usize]) -> Vec<E> {
    let mut to = vec![0; order.len()];
    for (k, &i) in order.iter().enumerate() {
        to[i] = k;
    }
    order.iter().map(|&i| renamed(&sys[i], &to)).collect()
}

/// `e` with the parts of every tuple in the opposite order.
fn reversed(e: &E) -> E {
    let all = |xs: &[E]| xs.iter().map(reversed).collect::<Vec<_>>();
    let one = |x: &E| Box::new(reversed(x));
    match e {
        E::Tup(xs) => E::Tup(all(xs).into_iter().rev().collect()),
        E::Union(xs) => E::Union(all(xs)),
        E::And(xs) => E::And(all(xs)),
        E::Mor(l, u, v) => E::Mor(one(l), one(u), one(v)),
        E::Diff(a, b) => E::Diff(one(a), one(b)),
        E::Atom(_) | E::Int | E::Bool | E::Empty | E::Top | E::Ref(_) => e.clone(),
    }
}

/// `e` with the arms of every union and the parts of every meet in an order drawn from `g`.
fn shuffled(e: &E, g: &mut Rng) -> E {
    let all = |xs: &[E], g: &mut Rng, on: bool| {
        let mut v: Vec<E> = xs.iter().map(|x| shuffled(x, g)).collect();
        for i in (1..if on { v.len() } else { 0 }).rev() {
            let j = g.below(i + 1);
            v.swap(i, j);
        }
        v
    };
    match e {
        E::Tup(xs) => E::Tup(all(xs, g, false)),
        E::Union(xs) => E::Union(all(xs, g, true)),
        E::And(xs) => E::And(all(xs, g, true)),
        E::Mor(l, u, v) => E::Mor(
            Box::new(shuffled(l, g)),
            Box::new(shuffled(u, g)),
            Box::new(shuffled(v, g)),
        ),
        E::Diff(a, b) => E::Diff(Box::new(shuffled(a, g)), Box::new(shuffled(b, g))),
        E::Atom(_) | E::Int | E::Bool | E::Empty | E::Top | E::Ref(_) => e.clone(),
    }
}

/// Groups of two to five definitions, each a union of up to three arms of `#stop`, tuples of
/// one or two parts, `(#k, x)` and `(int) -> x`, a part a definition, a meet of two, or a meet
/// of one with `(top, top)` or with `(int) -> x`: the X14 family with meets.
fn gen_meets(g: &mut Rng) -> Vec<E> {
    let n = 2 + g.below(4);
    let r = |g: &mut Rng| E::Ref(g.below(n));
    let item = |g: &mut Rng| match g.below(6) {
        0 | 1 => r(g),
        2 => E::And(vec![r(g), r(g)]),
        3 => E::And(vec![r(g), tup(vec![E::Top, E::Top])]),
        4 => E::And(vec![r(g), exact(E::Int, r(g))]),
        _ => exact(E::Int, r(g)),
    };
    (0..n)
        .map(|_| {
            let alts: Vec<E> = (0..1 + g.below(3))
                .map(|_| match g.below(10) {
                    0 => E::Atom("stop"),
                    1 | 2 => tup(vec![item(g)]),
                    3 | 4 => tup(vec![item(g), item(g)]),
                    5 => tup(vec![E::Atom("k"), item(g)]),
                    _ => exact(E::Int, item(g)),
                })
                .collect();
            one_or_union(alts)
        })
        .collect()
}

/// `k` copies of the group that made the search for values run without end (GROUP-search-hang),
/// in a ring when `ring` holds: with `A`, `B`, `C` definitions `3j`, `3j + 1`, `3j + 2` and `A'`
/// the next copy's `A`, or its own when `ring` does not hold,
///
/// ```text
/// A = ((int) -> B) | (C,)
/// B = (C & B,) | (C & A',) | ((int) -> C)
/// C = (A & B,) | (C,)
/// ```
///
/// One copy is the group the stress run found.
fn hang_copies(k: usize, ring: bool) -> Vec<E> {
    let and = |a: usize, b: usize| E::And(vec![r(a), r(b)]);
    let one = |x: E| tup(vec![x]);
    let n = 3 * k;
    (0..k)
        .flat_map(|j| {
            let (a, b, c) = (3 * j, 3 * j + 1, 3 * j + 2);
            let next = if ring { (3 * j + 3) % n } else { a };
            [
                E::Union(vec![exact(E::Int, r(b)), one(r(c))]),
                E::Union(vec![one(and(c, b)), one(and(c, next)), exact(E::Int, r(c))]),
                E::Union(vec![one(and(a, b)), one(r(c))]),
            ]
        })
        .collect()
}

/// The group the search for values ran on without end, before the search took each function
/// type at most once per value it builds (GROUP-search-hang), gets the same verdicts in every
/// order of its questions and of its definitions, with and without the parts of its tuples
/// reversed: the decider refuses each member. Each has a value, with `h` a function in both
/// `A` and `B`: `c = (h,)`, a value of `C`, and `h = λ_. ((c,),)`, whose result is in both `B`
/// and `C`; `(c,)` is a value of `A`. The search does not build a value of a meet of two
/// members such as `A & B` (GROUP-search-meet-values).
#[test]
fn the_group_that_hung_the_search_is_decided_in_every_order() {
    let sys = hang_copies(1, false);
    let want = alone(&kernel(&sys, "hang"));
    let refused = Some(Verdict::Refused(Refusal::Group));
    assert_eq!(want, vec![refused; 3], "{}", show_system(&sys));
    let types = kernel(&sys, "hang");
    for order in permutations(3) {
        assert_eq!(
            in_order(&types, &order),
            want,
            "asked in the order {order:?}"
        );
        for rev in [false, true] {
            let mut sys = moved(&sys, &order);
            if rev {
                sys = sys.iter().map(reversed).collect();
            }
            let got = alone(&kernel(&sys, &format!("hang_{order:?}_{rev}")));
            assert_eq!(got, want, "{}", show_system(&sys));
        }
    }
}

/// The same group with the one-part tuples written as the atom `#k` with a payload,
///
/// ```text
/// type Q = ((int) -> R) | #k(S)
/// type R = #k(S & R) | #k(S & Q) | ((int) -> S)
/// type S = #k(Q & R) | #k(S)
/// ```
///
/// gets the same verdicts in every order of its questions and of its definitions: the decider
/// refuses each member, as in [`the_group_that_hung_the_search_is_decided_in_every_order`].
/// The written placement of the definitions is asked in all 6 orders of the questions and each
/// other placement in one order drawn afresh each run: 11 runs, where all 6 placements were
/// asked in all 6 orders, 36 runs and 0.68 to 0.99 s alone on a loaded machine, until
/// TEST-bench-move-l0123 (author P169: correctness tests well under 1 s alone).
#[test]
fn the_group_that_hung_the_search_with_atoms_is_decided_in_every_order() {
    let (mut rng, seed) = Rng::fresh("the group that hung the search, with atoms");
    let body = |q: &dyn Fn(usize) -> Expr| {
        let k = |x: Expr| Expr::Atom("k".into(), vec![x]);
        let and = |a: usize, b: usize| Expr::And(vec![q(a), q(b)]);
        let f = |x: Expr| Expr::exact(Expr::Type(Type::int()), x);
        [
            ("Q", Expr::Union(vec![f(q(1)), k(q(2))])),
            ("R", Expr::Union(vec![k(and(2, 1)), k(and(2, 0)), f(q(2))])),
            ("S", Expr::Union(vec![k(and(0, 1)), k(q(2))])),
        ]
    };
    for (p, at) in permutations(3).into_iter().enumerate() {
        let mut defs: Vec<Option<Def>> = vec![None, None, None];
        for (j, (name, body)) in body(&|i| Expr::Ref(at[i], vec![])).into_iter().enumerate() {
            defs[at[j]] = Some(Def {
                name: name.into(),
                params: vec![],
                body,
            });
        }
        let defs = defs
            .into_iter()
            .map(|d| d.expect("every place filled"))
            .collect();
        let types = (Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))).instance(vec![]);
        let orders = if p == 0 {
            permutations(3)
        } else {
            vec![permutations(3)[rng.below(6)].clone()]
        };
        for order in orders {
            Type::forget_emptiness();
            for &j in &order {
                assert_eq!(
                    types[at[j]].verdict(),
                    Verdict::Refused(Refusal::Group),
                    "{} with the definitions at {at:?}, asked in the order {order:?} \
                     (ZED_TEST_SEED={seed})",
                    ["Q", "R", "S"][j]
                );
            }
        }
    }
}

/// The verdicts of every member of `n` copies of the group that hung the search, at n and 8n
/// copies, in a ring when `ring` holds, the groups built before the runs. That each member is
/// refused, as the one copy is, was checked here at 32 copies until TEST-bench-move-l0123
/// (author P169); it is checked at 2 and 3 copies by
/// [`a_few_copies_of_the_group_that_hung_the_search_are_refused`] and at a ring of 3 by
/// [`a_ring_of_the_group_that_hung_the_search_is_refused`].
fn verdicts_of_copies_scale(what: &str, n: usize, ring: bool) {
    let make = |k: usize| -> Vec<Type> {
        (kernel(&hang_copies(k, ring), &format!("hang_{ring}_{k}")).into_iter())
            .map(|t| t.expect("the copies are admitted"))
            .collect()
    };
    let copies = scaling::inputs(n, make);
    scaling::check_order(what, n, 1, |k| {
        Type::forget_emptiness();
        for t in &copies[&k] {
            std::hint::black_box(t.verdict());
        }
    });
}

/// A ring of three copies of the group that hung the search, one group of nine definitions, is
/// decided: each member is refused, as the one copy is. (Eight copies until
/// TEST-bench-move-l0123; `bench::verdicts_of_a_ring_of_the_group_that_hung_the_search_scale`
/// asks larger rings.)
#[test]
fn a_ring_of_the_group_that_hung_the_search_is_refused() {
    let got = alone(&kernel(&hang_copies(3, true), "hang_ring3"));
    assert_eq!(got, vec![Some(Verdict::Refused(Refusal::Group)); 9]);
}

/// The five definitions of cases J and L of GROUP-closure-order, which differ in the last:
///
/// ```text
/// R0 = (R2, R3)
/// R1 = (R0, R2) | (R0, R3)
/// R2 = (int) -> R1
/// R3 = ((int) -> R0) | (R1, R2)
/// R4 = (#both, R0, R0 & (top, top))        J
/// R4 = (#both, R0 & (top, top), R0)        L
/// ```
///
/// and the same without `#both`. Each member is inhabited: with `t = λ_. (r0, t)`, a value of
/// `R2`, and `u = λ_. r0`, a value of `R3`, `r0 = (t, u)` (a function may return a value that
/// holds it).
fn cases_j_and_l() -> Vec<(&'static str, Vec<E>)> {
    let top2 = || tup(vec![E::Top, E::Top]);
    let met = || E::And(vec![r(0), top2()]);
    [
        ("J", tup(vec![E::Atom("both"), r(0), met()])),
        ("L", tup(vec![E::Atom("both"), met(), r(0)])),
        ("J2", tup(vec![r(0), met()])),
        ("L2", tup(vec![met(), r(0)])),
    ]
    .into_iter()
    .map(|(name, both)| {
        let sys = vec![
            tup(vec![r(2), r(3)]),
            E::Union(vec![tup(vec![r(0), r(2)]), tup(vec![r(0), r(3)])]),
            exact(E::Int, r(1)),
            E::Union(vec![exact(E::Int, r(0)), tup(vec![r(1), r(2)])]),
            both,
        ];
        (name, sys)
    })
    .collect()
}

/// Cases J and L, refused in some orders of their components and inhabited in others before
/// GROUP-closure-order, are inhabited in the orders of their definitions asked, with and
/// without the parts of their tuples reversed. Each case asks the written order and 23 more of
/// its 120 orders, drawn afresh each run; each asked all 120, 0.73 to 0.95 s alone on a loaded
/// machine, until TEST-bench-move-l0123 (author P169: correctness tests well under 1 s alone).
#[test]
fn cases_j_and_l_are_inhabited_in_every_order() {
    let (mut rng, _) = Rng::fresh("cases J and L");
    let orders = permutations(5);
    let mut runs = 0;
    for (name, sys) in cases_j_and_l() {
        let mut asked = vec![0];
        asked.extend(pick_seeds(&mut rng, name, 1..120, 23));
        for p in asked {
            let order = &orders[p as usize];
            for rev in [false, true] {
                let mut sys = moved(&sys, order);
                if rev {
                    sys = sys.iter().map(reversed).collect();
                }
                let got = alone(&kernel(&sys, &format!("{name}_{p}_{rev}")));
                assert_eq!(
                    got,
                    vec![Some(Verdict::Inhabited); 5],
                    "{name}, definitions in the order {order:?}: {}",
                    show_system(&sys)
                );
                runs += 1;
            }
        }
    }
    assert_eq!(runs, 4 * 24 * 2);
}

/// Groups the stress runs of GROUP-closure-order found inhabited in some orders and refused in
/// others, inhabited in every order of their definitions:
///
/// - x9014, the group of four that was the fixture of `group_refusal` (`Pair`, `Tree`, `Thunk`,
///   `Node`), with `p = (t, n)`, `t = λ_. p` and `n = λ_. (p, t)`;
/// - x15407, five definitions, with `r1 = (r0, r0)`, `r0 = (r2, r3)`, `r2 = λ_. r1` and
///   `r3 = λ_. (r1, r1)`, read through `r0` itself: `r0` is the pair of two functions, one
///   returning `(r0, r0)`.
#[test]
fn groups_found_inhabited_in_some_orders_are_inhabited_in_all() {
    let p = |a: usize, b: usize| tup(vec![r(a), r(b)]);
    let systems = [
        (
            "x9014",
            vec![
                p(1, 3),
                E::Union(vec![p(2, 2), p(0, 3)]),
                exact(E::Int, r(0)),
                E::Union(vec![exact(E::Int, r(1)), p(1, 2)]),
            ],
        ),
        (
            "x15407",
            vec![
                E::Union(vec![p(1, 1), p(2, 3), p(3, 3)]),
                p(0, 0),
                E::Union(vec![p(1, 4), exact(E::Int, r(1))]),
                exact(E::Int, r(4)),
                p(1, 1),
            ],
        ),
    ];
    for (tag, sys) in systems {
        let n = sys.len();
        for (k, order) in permutations(n).iter().enumerate() {
            let sys = moved(&sys, order);
            let got = alone(&kernel(&sys, &format!("{tag}_{k}")));
            assert_eq!(
                got,
                vec![Some(Verdict::Inhabited); n],
                "{tag}, definitions in the order {order:?}: {}",
                show_system(&sys)
            );
        }
    }
}

/// System 1699 of the meets family, which the group oracle (`truth`) finds empty although each
/// member has a value, since the oracle does not build values through two functions that hold
/// each other's values: with `v = (c1, c2)`, `c1 = λ_. (#k, v)` and `c2 = λ_. v`, `v` is a
/// value of `R2`, `c1` of `R0` and `(#k, v)` of `R1`. The kernel finds those three inhabited,
/// and `R3 = ((R1 & R0), R2)` empty: `R1` holds pairs and `R0` closures and one-part tuples.
///
/// ```text
/// R0 = ((int) -> R2) | ((R3 & (top, top)),)
/// R1 = (#k, R2)
/// R2 = ((R0 & ((int) -> R1)), ((int) -> R2)) | ((int) -> (R3 & ((int) -> R3))) | (#k, R2)
/// R3 = ((R1 & R0), R2)
/// ```
#[test]
fn a_value_through_two_functions_the_oracle_misses_is_found() {
    let sys = gen_meets(&mut Rng::new(1699));
    let tr = truth(&sys, CAP);
    assert!(tr.exhaustive);
    assert!(
        tr.seen.iter().all(|s| matches!(s, Seen::None)),
        "{}",
        show_system(&sys)
    );
    let inhabited = Some(Verdict::Inhabited);
    assert_eq!(
        alone(&kernel(&sys, "meets1699")),
        vec![inhabited, inhabited, inhabited, Some(Verdict::Empty)],
        "{}",
        show_system(&sys)
    );
}

/// What two orders of a system may differ in: whether a member is inhabited, and otherwise
/// whether it is empty or refused, but not the reason of a refusal, when `exact` holds; only
/// whether it is inhabited when not.
fn verdict_class(v: Option<Verdict>, exact: bool) -> u8 {
    match v {
        None => 0,
        Some(Verdict::Inhabited) => 1,
        Some(_) if !exact => 2,
        Some(Verdict::Empty) => 3,
        Some(_) => 4,
    }
}

/// The verdicts of systems `seeds` of generator `make` agree with those of the same system with
/// its definitions in four random orders, the parts of its tuples reversed in two of them, and,
/// when `parts` holds, the arms of its unions and the parts of its meets in random orders; up
/// to the reason of a refusal, or only in whether a member is inhabited when `exact` does not
/// hold.
fn verdicts_agree_across_orders(
    name: &str,
    make: fn(&mut Rng) -> Vec<E>,
    seeds: &[u64],
    (parts, exact): (bool, bool),
) {
    let class = |vs: &[Option<Verdict>]| -> Vec<u8> {
        vs.iter().map(|&v| verdict_class(v, exact)).collect()
    };
    let mut differ = Vec::new();
    for &seed in seeds {
        let sys = make(&mut Rng::new(seed));
        let tag = format!("{name}{seed}");
        let want = alone(&kernel(&sys, &tag));
        let n = sys.len();
        let mut g = Rng::new(seed ^ 0xABCD);
        for k in 0..4 {
            let mut order: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                let j = g.below(i + 1);
                order.swap(i, j);
            }
            let rev = k % 2 == 1;
            let moved: Vec<E> = (moved(&sys, &order).iter())
                .map(|e| {
                    let e = if parts {
                        shuffled(e, &mut g)
                    } else {
                        e.clone()
                    };
                    if rev { reversed(&e) } else { e }
                })
                .collect();
            let got = alone(&kernel(&moved, &format!("{tag}_p{k}")));
            let back: Vec<_> = order.iter().map(|&i| want[i]).collect();
            if class(&got) != class(&back) {
                differ.push(format!(
                    "{tag}: {back:?} in the order {order:?}{}: {got:?}\n  {}\n  {}",
                    if rev { " reversed" } else { "" },
                    show_system(&sys),
                    show_system(&moved)
                ));
            }
        }
    }
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

/// Systems of the meets family whose verdicts depended on the order of the parts of their meets
/// while a meet was keyed by its spelling: seed 11 was refused for want of a witness in three of
/// its four orders and inhabited in the fourth, as a meet written in two orders was two types,
/// and a morphism type returning it two morphism types. With a meet one type in either order
/// and the searches that a fork left open rolled back (item GROUP-search-canon-key), each is
/// decided alike in every order tried, the arms and parts shuffled too.
#[test]
fn meets_whose_parts_differ_in_order_agree_across_orders() {
    for seed in [
        11, 213, 374, 399, 433, 441, 952, 1059, 1847, 2153, 2700, 3763, 3855, 4676, 5276, 5302,
        5373, 5522, 5933, 6219, 6304, 7932, 8022, 8040, 8754, 8858, 9454, 10677, 11489, 12718,
        12856, 13004, 13161, 13383, 13665, 14180, 14382, 14702, 14813, 15093, 15218, 15717,
    ] {
        verdicts_agree_across_orders("meets", gen_meets, &[seed], (true, true));
    }
}

/// Groups of four, five and six definitions of the X14 family give the same verdicts in every
/// order tried, up to the reason of a refusal (GROUP-closure-order).
#[test]
fn x14_groups_agree_across_orders() {
    let (mut rng, _) = Rng::fresh("x14 groups across orders");
    verdicts_agree_across_orders(
        "x14_4_",
        |g| claude_of(g, 4),
        &seeds_of(&mut rng, "x14_4_", 0..8, 0..2000, 120),
        (true, true),
    );
    verdicts_agree_across_orders(
        "x14_5_",
        |g| claude_of(g, 5),
        &seeds_of(&mut rng, "x14_5_", 0..8, 0..600, 60),
        (true, true),
    );
    verdicts_agree_across_orders(
        "x14_6_",
        |g| claude_of(g, 6),
        &seeds_of(&mut rng, "x14_6_", 0..8, 0..250, 40),
        (true, true),
    );
}

/// Systems of the other families give the same verdicts in every order tried, up to the reason
/// of a refusal.
#[test]
fn other_families_agree_across_orders() {
    let (mut rng, _) = Rng::fresh("other families across orders");
    verdicts_agree_across_orders(
        "claude",
        gen_claude,
        &seeds_of(&mut rng, "claude", 0..8, 0..200, 32),
        (true, true),
    );
    verdicts_agree_across_orders(
        "mixed",
        gen_mixed,
        &seeds_of(&mut rng, "mixed", 0..8, 0..200, 32),
        (true, true),
    );
    verdicts_agree_across_orders(
        "layer",
        gen_layer,
        &seeds_of(&mut rng, "layer", 0..8, 0..200, 32),
        (true, true),
    );
    verdicts_agree_across_orders(
        "cells",
        gen_cells,
        &seeds_of(&mut rng, "cells", 0..8, 0..200, 32),
        (true, true),
    );
}

/// Systems of the meets family, with their definitions, the arms of their unions and the parts
/// of their meets in other orders, agree in which members are inhabited, empty or refused, up
/// to the reason of a refusal (item GROUP-search-canon-key). Before it, 13 of these 800 systems
/// differed between orders, and 172 of the 15,691 seeds of 0..16,000 that finished within 60 s
/// in the sweep of the item; after it none of the 16,000 differs, and 26 differ only in the
/// reason of a refusal. Each run asks seeds 0 to 3 of the 800 and 16 more chosen afresh; it
/// asked seeds 0 to 7 and 32 more, 0.35 to 1.91 s alone on a loaded machine, until
/// TEST-bench-move-l0123 (author P169: correctness tests well under 1 s alone).
#[test]
fn meets_agree_across_orders() {
    let (mut rng, _) = Rng::fresh("meets across orders");
    verdicts_agree_across_orders(
        "meets",
        gen_meets,
        &seeds_of(&mut rng, "meets", 0..4, 0..800, 16),
        (true, true),
    );
}

/// The pool's rounds keep the first 36 tuples of the product of the values found for each
/// component (`first_tuples`), built one by one. Against the whole product, built as the oracle
/// first did, on random choices of up to 6 values for each of up to 5 components, some with none:
/// the same tuples in the same order, both 36 and every one.
#[test]
fn the_first_tuples_are_those_of_the_whole_product() {
    let whole = |opts: &[Vec<usize>]| -> Vec<Vec<usize>> {
        let mut rows = vec![vec![]];
        for o in opts {
            rows = rows
                .iter()
                .flat_map(|r: &Vec<usize>| {
                    o.iter().map(move |&x| {
                        let mut d = r.clone();
                        d.push(x);
                        d
                    })
                })
                .collect();
        }
        rows
    };
    let (mut g, seed) = Rng::fresh("choices of values for the first tuples");
    for _ in 0..400 {
        let opts: Vec<Vec<usize>> = (0..g.below(6))
            .map(|_| (0..g.below(7)).map(|_| g.below(100)).collect())
            .collect();
        let all = whole(&opts);
        assert_eq!(
            first_tuples(&opts, 36),
            all[..all.len().min(36)],
            "{opts:?}, ZED_TEST_SEED={seed}"
        );
        assert_eq!(
            first_tuples(&opts, all.len()),
            all,
            "{opts:?}, ZED_TEST_SEED={seed}"
        );
    }
    // A tuple type of no components has one tuple, and one with a component of no values none.
    assert_eq!(first_tuples(&[], 36), [Vec::<usize>::new()]);
    assert!(first_tuples(&[vec![1, 2], vec![]], 36).is_empty());
    // Two components of six values: the 36 kept are the whole product, the second fastest.
    let six: Vec<usize> = (0..6).collect();
    let kept = first_tuples(&[six.clone(), six], 36);
    assert_eq!(kept.len(), 36);
    assert_eq!(
        (&kept[0], &kept[1], &kept[35]),
        (&vec![0, 0], &vec![0, 1], &vec![5, 5])
    );
}

/// All four states unfold alike, but their named edges are different. Keeping a renamed
/// instance alive must not supply the bodies printed for the original instance.
#[test]
fn named_graphs_of_one_class_keep_their_own_printed_bodies() {
    let printed = |warm_first: bool| {
        std::thread::spawn(move || {
            let targets = [(0, 1), (0, 2), (1, 3), (2, 0)];
            let sys: Vec<E> = targets
                .into_iter()
                .map(|(a, b)| {
                    E::Union(vec![
                        E::Atom("stop"),
                        E::Tup(vec![E::Atom("a"), E::Ref(a)]),
                        E::Tup(vec![E::Atom("b"), E::Ref(b)]),
                    ])
                })
                .collect();
            let names = [3, 2, 1, 0];
            let warm = warm_first.then(|| kernel_named(&sys, "named_graph_identity", Some(&names)));
            if let Some(types) = &warm {
                let _ = alone(types);
            }
            let original = kernel(&sys, "named_graph_identity");
            let texts: Vec<String> = original
                .iter()
                .map(|t| {
                    t.as_ref()
                        .expect("the regular graph is admitted")
                        .surface()
                        .to_string()
                })
                .collect();
            std::hint::black_box(&warm);
            texts
        })
        .join()
        .expect("the printing thread finishes")
    };
    assert_eq!(printed(false), printed(true));
}

/// Seed 3228 of the X14 family with meets (GSX-unsolved). The operands of a meet print in the
/// order of their digests, names-aware first (`digests_cmp` in zed-kernel), so its first
/// member writes `T8 & T6`. The text is the same when copies of the group with the definitions
/// reversed, other names, or the arms in another order were built and decided first, and when
/// the members print last first.
#[test]
fn a_group_prints_the_same_text_whatever_was_built_before_it() {
    let printed = |history: bool, last_first: bool| {
        std::thread::spawn(move || {
            let sys = gen_meets(&mut Rng::new(3228));
            let mut before = Vec::new();
            if history {
                let rev: Vec<usize> = (0..sys.len()).rev().collect();
                let mut g = Rng::new(1);
                let arms: Vec<E> = sys.iter().map(|e| shuffled(e, &mut g)).collect();
                for (s, tag) in [
                    (moved(&sys, &rev), "meets3228_order"),
                    (sys.clone(), "a_renamed_definition_3228"),
                    (arms, "meets3228_arms"),
                ] {
                    let types = kernel(&s, tag);
                    let _ = alone(&types);
                    before.push(types);
                }
            }
            let types = kernel(&sys, "meets3228");
            let mut idx: Vec<usize> = (0..types.len()).collect();
            if last_first {
                idx.reverse();
            }
            let mut texts: Vec<(usize, String)> = idx
                .into_iter()
                .map(|i| {
                    let t = types[i].as_ref().expect("the group is admitted");
                    (i, t.surface().to_string().replace('\n', " / "))
                })
                .collect();
            texts.sort();
            std::hint::black_box(&before);
            texts.into_iter().map(|(_, s)| s).collect::<Vec<_>>()
        })
        .join()
        .expect("the printing thread finishes")
    };
    let fresh = printed(false, false);
    assert_eq!(
        fresh[0],
        "type T1 = (#k, T1); / type T2 = T8 & T6; / type T3 = (#k, T1) & (#k, T3); / \
         type T4 = (#k, T3) & ((T2, T5) | (#k, T2)); / \
         type T5 = (#k, T3) & ((T1, T7) | (#k, T4)); / type T6 = (T2, T5) | (#k, T2); / \
         type T7 = int -> T6; / type T8 = (T1, T7) | (#k, T4); / type T9 = T8 | (int -> T3); / T9"
    );
    assert_eq!(printed(true, false), fresh);
    assert_eq!(printed(false, true), fresh);
    assert_eq!(printed(true, true), fresh);
}

// ---------------------------------------------------------------------------------------------
// Small instances of the benchmarks (TEST-bench-move-l0123, author P169)
// ---------------------------------------------------------------------------------------------

/// Small instance of `bench::verdicts_of_random_groups_scale`, and the check that systems of
/// the X14 family are admitted: every definition of the X14 systems of seeds 0 to 7, of a
/// chain group of 2, 8 and 24 definitions and of one X14 system of as many is admitted, and
/// each member's verdict is decided when asked alone.
#[test]
fn small_random_groups_are_admitted() {
    let mut systems: Vec<(String, Vec<E>)> = (0..8)
        .map(|seed| (format!("many_s{seed}"), gen_claude(&mut Rng::new(seed))))
        .collect();
    for n in [2, 8, 24] {
        systems.push((format!("chain_s{n}"), chain_of(&mut Rng::new(7), n)));
        systems.push((format!("one_s{n}"), claude_of(&mut Rng::new(3), n)));
    }
    for (tag, sys) in &systems {
        let types = kernel(sys, tag);
        assert!(
            types.iter().all(Option::is_some),
            "{tag}: {}",
            show_system(sys)
        );
        assert!(alone(&types).iter().all(Option::is_some), "{tag}");
    }
}

/// Small instance of `bench::verdicts_of_undecided_groups_scale`: every definition of an X14
/// system of 2, 8 and 24 definitions with each body less `#none` is admitted, and the verdicts
/// of the members of its largest group, asked together, and of every definition alone are
/// decided.
#[test]
fn small_undecided_groups_are_admitted() {
    for n in [2, 8, 24] {
        let sys = undecided(claude_of(&mut Rng::new(3), n));
        let types = kernel(&sys, &format!("oneu_s{n}"));
        assert!(
            types.iter().all(Option::is_some),
            "n = {n}: {}",
            show_system(&sys)
        );
        Type::forget_emptiness();
        for &i in &largest_group(&sys) {
            std::hint::black_box(types[i].as_ref().map(Type::verdict));
        }
        assert!(alone(&types).iter().all(Option::is_some), "n = {n}");
    }
}

/// Small instance of `bench::a_chain_decided_again_scales`, moved out of it: in a key chain of
/// up to 16, the empty members are exactly those at even places, so `R(m - 1)` is not empty.
#[test]
fn every_second_member_of_a_key_chain_is_empty() {
    for m in 1..=16 {
        let ts = key_chain(m);
        let empty: Vec<usize> = (0..=m)
            .filter(|&k| {
                Type::forget_emptiness();
                ts[k].is_empty()
            })
            .collect();
        assert_eq!(
            empty,
            (0..=m).step_by(2).collect::<Vec<_>>(),
            "a key chain of {m}"
        );
    }
}

/// Small instance of `bench::the_groups_of_a_system_are_built_in_its_size`: every group of a
/// chain of 1, 2 and 16 groups, and of one group of as many definitions, is admitted. At 1 both
/// systems are one definition that reads itself.
#[test]
fn the_groups_of_small_systems_are_built() {
    for n in [1, 2, 16] {
        let types = kernel(&chain_of_groups(n, false), &format!("built_chain{n}"));
        assert!(types.iter().all(Option::is_some), "a chain of {n} groups");
        let types = kernel(&chain_of(&mut Rng::new(7), n), &format!("built_one{n}"));
        assert!(types.iter().all(Option::is_some), "one group of {n}");
    }
}

/// Small instance of `bench::a_chain_of_shared_tuple_parts_prints_in_its_size`: a marked chain
/// of 2, 3, 5 and 8 shared tuple parts prints as syntax, with one definition for `#a | #b`, two
/// for the first pair and the part that names it, and one for each other cycle: n + 2.
#[test]
fn a_short_chain_of_shared_tuple_parts_prints() {
    for n in [2, 3, 5, 8] {
        let t = shared_chain(n, true, &format!("short_chain{n}"));
        prints_as_syntax(&t, &format!("a chain of {n}"));
        assert_eq!(t.surface().defs.len(), n + 2, "a chain of {n}");
    }
}

/// Small instance of `bench::verdicts_of_copies_of_the_group_that_hung_the_search_scale`, which
/// checked this at 32 copies until TEST-bench-move-l0123 (author P169): 2 and 3 copies of the
/// group that hung the search, each its own group, are admitted, and each member is refused, as
/// the one copy is, asked in order after one forget.
#[test]
fn a_few_copies_of_the_group_that_hung_the_search_are_refused() {
    for k in [2, 3] {
        let types = kernel(&hang_copies(k, false), &format!("hang_s{k}"));
        assert!(types.iter().all(Option::is_some), "k = {k}");
        let order: Vec<usize> = (0..types.len()).collect();
        assert_eq!(
            in_order(&types, &order),
            vec![Some(Verdict::Refused(Refusal::Group)); 3 * k],
            "k = {k}"
        );
    }
}

mod bench;

/// Item FAIL-print-height-cycle-seed: the smallest system found, its neighbors, and the ten
/// `gen_cells` seeds of 100,000 fresh seeds whose systems made the kernel panic while building
/// the group, build and print. The panic came from the refusal of `R2 = R1 \ ((int) -> R2)`
/// with `R1 = R0 \ Never` and `R0 = (#a, (#a | R0))`: written by name, `R1` unfolds once to
/// `(#a, #a | R0) | #a`, and inside it the part `#a | R0`, kept unevaluated, unfolds once to the
/// same text again. That cycle of the printer's texts passed through no recursive type with a
/// definition, and the printer assumed every one does. Such a part now gets a definition.
#[test]
fn groups_whose_printing_met_a_cycle_without_a_recursive_type_build_and_print() {
    let a = || E::Atom("a");
    let smallest = vec![
        tup(vec![a(), E::Union(vec![a(), r(0)])]),
        diff(r(0), E::Empty),
        diff(r(1), exact(E::Int, r(2))),
    ];
    // `R2` is refused, and its message prints `R1`, whose part `#a | R0` meets itself inside its
    // own unfolding: the part gets a definition, as a cycle written out where it stands has no
    // end.
    let built = kernel(&smallest[..2], "height_cycle_min");
    let body = expr(&smallest[2], &[None, None, Some(0)], &built).expect("R0 and R1 build");
    let message = Group::new(vec![Def {
        name: "height_cycle_min_2".into(),
        params: vec![],
        body,
    }])
    .expect_err("R2 is not monotone")
    .message;
    let decls: Vec<&str> = (message.lines().map(str::trim))
        .filter(|line| line.starts_with("type "))
        .collect();
    assert_eq!(decls.len(), 2, "{message}");
    let unit = decls.join("\n");
    let tokens = lex_fence(&unit).unwrap_or_else(|e| panic!("{message}: {e:?}"));
    parse(&unit, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{message}: {e:?}"));
    // Its neighbors: `R1` is `R0` itself; the cycle passes through two parts kept unevaluated,
    // one inside the other or side by side; and the group `R2` makes is accepted, by `&` or by a
    // reference to `R0` on the right of `\`.
    let b = || E::Atom("b");
    let r0 = |r0: E| vec![r0, diff(r(0), E::Empty)];
    let refused = || diff(r(1), exact(E::Int, r(2)));
    let neighbors = [
        vec![
            tup(vec![a(), E::Union(vec![a(), r(0)])]),
            diff(r(0), exact(E::Int, r(1))),
        ],
        [
            r0(tup(vec![
                a(),
                E::Union(vec![a(), tup(vec![b(), E::Union(vec![b(), r(0)])])]),
            ])),
            vec![refused()],
        ]
        .concat(),
        [
            r0(tup(vec![
                E::Union(vec![a(), r(0)]),
                E::Union(vec![b(), r(0)]),
            ])),
            vec![refused()],
        ]
        .concat(),
        [
            r0(tup(vec![a(), E::Union(vec![a(), r(0)])])),
            vec![E::And(vec![r(1), exact(E::Int, r(2))])],
        ]
        .concat(),
        [
            r0(tup(vec![a(), E::Union(vec![a(), r(0)])])),
            vec![diff(r(1), exact(E::Int, r(0)))],
        ]
        .concat(),
    ];
    let mut systems = vec![("height_cycle_min".to_string(), smallest)];
    for (k, sys) in neighbors.into_iter().enumerate() {
        systems.push((format!("height_cycle_near{k}"), sys));
    }
    for seed in [
        1480778453660708751u64,
        2332610074532812974,
        6838895980222929389,
        8443097688697121190,
        8612506816989866889,
        8825795845270495757,
        11404091016327924444,
        12649215288799211595,
        14429515599504043526,
        16467311145843597599,
    ] {
        let sys = gen_cells(&mut Rng::new(seed));
        systems.push((format!("height_cycle-{seed}"), sys.clone()));
        systems.push((format!("height_cycle--{seed}"), undecided(sys)));
    }
    for (tag, sys) in &systems {
        for (i, t) in kernel(sys, tag).iter().enumerate() {
            let Some(t) = t else { continue };
            prints_as_syntax(t, &format!("{tag}: R{i} of {}", show_system(sys)));
        }
    }
}
