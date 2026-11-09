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

use super::bes_families::{self, reference};
use super::judgments::{bodies, group};
use zed_kernel::types::bes::{Answer, decide};
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Type, Verdict};
use zed_tests::instances::Rng;
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
/// components are found by Tarjan's algorithm on an explicit stack, which emits each after
/// every component it reaches, so the whole costs the definitions and their references, where a
/// search from each definition cost their square and a pass per component their cube.
fn kernel(sys: &[E], tag: &str) -> Vec<Option<Type>> {
    let n = sys.len();
    let edges: Vec<Vec<usize>> = sys
        .iter()
        .map(|d| {
            let mut out = Vec::new();
            refs(d, &mut out);
            out
        })
        .collect();
    let mut built: Vec<Option<Type>> = vec![None; n];
    // The place of each definition in the component being built, `None` outside it.
    let mut pos: Vec<Option<usize>> = vec![None; n];
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
            let at = stack
                .iter()
                .rposition(|&x| x == v)
                .expect("v is on the stack");
            let mut comp = stack.split_off(at);
            comp.sort_unstable();
            for (k, &d) in comp.iter().enumerate() {
                on_stack[d] = false;
                pos[d] = Some(k);
            }
            let defs: Option<Vec<Def>> = comp
                .iter()
                .map(|&d| {
                    expr(&sys[d], &pos, &built).map(|body| Def {
                        name: format!("{tag}_{d}"),
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
            for &d in &comp {
                pos[d] = None;
            }
        }
    }
    built
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
                    let mut combos: Vec<Vec<usize>> = vec![vec![]];
                    for o in &opts {
                        combos = combos
                            .iter()
                            .flat_map(|c| {
                                o.iter().map(move |&x| {
                                    let mut d = c.clone();
                                    d.push(x);
                                    d
                                })
                            })
                            .collect();
                    }
                    for c in combos.into_iter().take(36) {
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
            Verdict::Refused(_) => tally.refused += 1,
        }
    }
}

/// The systems `generate` gives for `seeds`, each against the pool; panics on a wrong answer, and
/// unless the refusals of members the pool shows inhabited number `missed`, so that a change in
/// what the value builder finds is seen either way.
fn sweep(
    name: &str,
    generate: fn(&mut Rng) -> Vec<E>,
    seeds: std::ops::Range<u64>,
    missed: usize,
) -> Tally {
    let mut tally = Tally::default();
    for seed in seeds {
        let sys = generate(&mut Rng::new(seed));
        compare(&sys, &format!("{name}{seed}"), &mut tally);
    }
    eprintln!("{name}: {tally:?}");
    assert!(
        tally.members > 0 && tally.empty > 0 && tally.inhabited > 0,
        "{name}: {tally:?}"
    );
    assert_eq!(
        tally.missed, missed,
        "{name}: refusals of inhabited members: {tally:?}"
    );
    tally
}

// Each sweep is a piece of the seeds, sized to finish well under 60 s.

#[test]
fn x14_family_groups_agree_with_the_values_0() {
    sweep("claude", gen_claude, 0..150, 0);
}

#[test]
fn x14_family_groups_agree_with_the_values_1() {
    sweep("claude", gen_claude, 150..300, 0);
}

#[test]
fn partial_morphism_groups_agree_with_the_values_0() {
    sweep("mixed", gen_mixed, 0..150, 0);
}

#[test]
fn partial_morphism_groups_agree_with_the_values_1() {
    sweep("mixed", gen_mixed, 150..300, 0);
}

#[test]
fn layered_groups_agree_with_the_values_0() {
    sweep("layer", gen_layer, 0..100, 4);
}

#[test]
fn layered_groups_agree_with_the_values_1() {
    sweep("layer", gen_layer, 100..200, 3);
}

#[test]
fn meets_and_differences_agree_with_the_values_0() {
    sweep("cells", gen_cells, 0..150, 1);
}

#[test]
fn meets_and_differences_agree_with_the_values_1() {
    sweep("cells", gen_cells, 150..300, 0);
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

/// `random(seed, rate, n)` over many seeds, rates and sizes: every answer `decide` gives agrees
/// with the classical solver of the Büchi game, and so does every verdict of the group the
/// definitions admit; `is_empty` never calls an inhabited member empty.
fn seeded(seeds: std::ops::Range<u64>) {
    let (mut decided, mut refused, mut groups, mut verdicts) = (0, 0, 0, 0);
    for rate in [0, 2, 5, 9, 14, 18] {
        for n in [2, 3, 5, 8, 13, 21] {
            for seed in seeds.clone() {
                let g = bes_families::random(seed, rate, n);
                let at = format!("random({seed}, {rate}, {n})");
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
    assert!(decided > 0 && groups > 0);
}

#[test]
fn seeded_random_systems_agree_with_the_reference_0() {
    seeded(0..40);
}

#[test]
fn seeded_random_systems_agree_with_the_reference_1() {
    seeded(40..80);
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

/// The verdicts of every member of `n` random groups of the X14 family, the verdict of the
/// first member of one chain group of `n` definitions, which its search reads whole, and the
/// verdicts of every member of one group of `n` (plan item VERDICT-group-share), of the X14
/// family and of the chain family, at `n` and `8n`, the groups built before the runs. The first
/// verdict asked of a member decides the whole group in one search (`Type::verdict`), so the
/// verdicts of all members cost what one does.
#[test]
fn verdicts_of_random_groups_scale() {
    let many = |n: usize| -> Vec<Type> {
        (0..n as u64)
            .flat_map(|seed| kernel(&gen_claude(&mut Rng::new(seed)), &format!("many{n}_{seed}")))
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let chain = |n: usize| -> Vec<Type> {
        kernel(&chain_of(&mut Rng::new(7), n), &format!("chain{n}"))
            .into_iter()
            .map(|t| t.expect("a chain group is admitted"))
            .collect()
    };
    let one = |n: usize| -> Vec<Type> {
        kernel(&claude_of(&mut Rng::new(3), n), &format!("one{n}"))
            .into_iter()
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let every = |ts: &[Type]| {
        Type::forget_emptiness();
        for t in ts {
            std::hint::black_box(t.verdict());
        }
    };
    let n = 64;
    let groups = scaling::inputs(n, many);
    scaling::check("verdicts of the members of n random groups", n, |m| {
        every(&groups[&m])
    });
    let n = 128;
    let chains = scaling::inputs(n, chain);
    scaling::check("the verdict of one member of a chain group of n", n, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][0].verdict());
    });
    scaling::check(
        "the verdicts of every member of a chain group of n",
        n,
        |m| every(&chains[&m]),
    );
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of every member of one X14 group of n",
        n,
        |m| every(&ones[&m]),
    );
}

/// Every member of a chain group of 512 is inhabited, by a chain of up to 512 values; before
/// the search kept a failure only until a type it read got a value, all but 8 were refused.
/// The verdicts agree whatever order the members are asked in, and with the verdict of each
/// member asked alone, for a few members.
#[test]
fn every_member_of_a_long_chain_is_inhabited() {
    let ts: Vec<Type> = kernel(&chain_of(&mut Rng::new(7), 512), "long_chain")
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
    for i in [0, 1, 255, 510, 511] {
        Type::forget_emptiness();
        assert_eq!(ts[i].verdict(), forward[i], "R{i} asked alone");
    }
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
/// rotation. Groups the decider refuses (`\ #none` on each body) and groups it decides.
#[test]
fn verdicts_do_not_depend_on_the_order_members_are_asked_in() {
    let mut systems: Vec<(String, Vec<E>)> = Vec::new();
    for seed in 0..40 {
        let sys = claude_of(&mut Rng::new(seed), 3);
        systems.push((format!("x14_{seed}"), sys.clone()));
        systems.push((format!("x14u_{seed}"), undecided(sys)));
    }
    for seed in 0..40 {
        systems.push((format!("cells{seed}"), gen_cells(&mut Rng::new(seed))));
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
                "{tag}: asked in the order {order:?}: {}",
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
                    "{tag}: definitions in the order {order:?}: {}",
                    show_system(&moved)
                );
            }
        }
        members += want.iter().flatten().count();
    }
    eprintln!("{members} members, {orders} orders");
}

/// Every member of a chain group of 512 that the decider refuses is inhabited, by a chain of up
/// to 512 values, decided by one search with all 512 as roots.
#[test]
fn every_member_of_an_undecided_long_chain_is_inhabited() {
    let ts = kernel(&undecided(chain_of(&mut Rng::new(7), 512)), "long_chain_u");
    for (i, v) in in_order(&ts, &(0..ts.len()).collect::<Vec<_>>())
        .iter()
        .enumerate()
    {
        assert_eq!(*v, Some(Verdict::Inhabited), "R{i} of the chain");
    }
}

/// The definitions of the largest group of `sys`, those that reach each other, in order: a
/// walk from each definition, O(n^2) for the test's inputs, outside the runs it measures.
fn largest_group(sys: &[E]) -> Vec<usize> {
    let edges: Vec<Vec<usize>> = (sys.iter())
        .map(|d| {
            let mut out = Vec::new();
            refs(d, &mut out);
            out
        })
        .collect();
    let reach: Vec<Vec<bool>> = (0..sys.len())
        .map(|s| {
            let mut seen = vec![false; sys.len()];
            let mut stack = edges[s].clone();
            while let Some(v) = stack.pop() {
                if !std::mem::replace(&mut seen[v], true) {
                    stack.extend(&edges[v]);
                }
            }
            seen
        })
        .collect();
    (0..sys.len())
        .map(|i| {
            (0..sys.len())
                .filter(|&j| reach[i][j] && reach[j][i])
                .collect::<Vec<_>>()
        })
        .max_by_key(Vec::len)
        .unwrap_or_default()
}

/// The verdicts of every member of one group of `n` that the decider refuses, of the chain
/// family and of the X14 family, at `n` and `8n`, the groups built before the runs: one search
/// with every member as a root decides them all (plan item VERDICT-group-roots), where a search
/// for each member read the group n times. Then the verdicts of every definition of the X14
/// system, which read the group by its verdicts and values (plan item VERDICT-group-readers).
#[test]
fn verdicts_of_undecided_groups_scale() {
    let chain = |n: usize| -> Vec<Type> {
        kernel(
            &undecided(chain_of(&mut Rng::new(7), n)),
            &format!("chainu{n}"),
        )
        .into_iter()
        .map(|t| t.expect("a chain group is admitted"))
        .collect()
    };
    let one = |n: usize| -> Vec<Type> {
        let sys = undecided(claude_of(&mut Rng::new(3), n));
        let group = largest_group(&sys);
        let ts = kernel(&sys, &format!("oneu{n}"));
        (group.iter())
            .map(|&i| {
                ts[i]
                    .clone()
                    .expect("every definition of the X14 family is admitted")
            })
            .collect()
    };
    // Every definition, those outside the largest group too: such a definition reads the
    // members of that group by their group's verdicts, so the system's verdicts cost one search
    // of the group and one of each definition's own part (plan item VERDICT-group-readers),
    // where a search for each definition decided again the part of the group it reaches.
    let all = |n: usize| -> Vec<Type> {
        kernel(
            &undecided(claude_of(&mut Rng::new(3), n)),
            &format!("allu{n}"),
        )
        .into_iter()
        .map(|t| t.expect("every definition of the X14 family is admitted"))
        .collect()
    };
    let every = |ts: &[Type]| {
        Type::forget_emptiness();
        for t in ts {
            std::hint::black_box(t.verdict());
        }
    };
    let n = 128;
    let chains = scaling::inputs(n, chain);
    scaling::check(
        "the verdicts of every member of an undecided chain group of n",
        n,
        |m| every(&chains[&m]),
    );
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of the members of the largest undecided X14 group of n definitions",
        n,
        |m| every(&ones[&m]),
    );
    let alls = scaling::inputs(n, all);
    scaling::check(
        "the verdicts of every definition of an undecided X14 system of n",
        n,
        |m| every(&alls[&m]),
    );
}

/// A definition outside a group the decider refuses reads each member of it by the group's
/// verdict and the value the group's search built (plan item VERDICT-group-readers): its
/// verdict agrees with the values, and with every order of the questions. In the layered system
/// of seed 316, `R3 = (int, R0) | ((R2) -> empty)` holds the function on the empty `R2`, and
/// reads the open member `R0` through `R2` and `R1`; a search of its own that decided `R0`
/// again called `R3` empty, where the same system with the decider's verdicts called it
/// inhabited.
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
    let gens: [fn(&mut Rng) -> Vec<E>; 4] = [gen_claude, gen_mixed, gen_layer, gen_cells];
    for (name, g) in ["claude", "mixed", "layer", "cells"].into_iter().zip(gens) {
        for seed in 0..100 {
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

/// A chain of 1000 groups (`chain_of_groups`), as the decider decides them and with every body
/// written `b \ #none`, is decided on a thread of 1 MiB, asked of the first member and of a
/// tuple outside the groups that holds it. Each group is decided before the group that reads it
/// (`Type::decide_groups_read`), so no search starts inside another: deciding each group as the
/// search above it reads it nested one search per group on the thread's stack, as the decider's
/// verdicts of the parts it reads already did (plan item VERDICT-group-readers). The tuple runs
/// first only the groups' deciders, and the groups' verdicts are decided when its search reads
/// the first member (plan item VERDICT-meet-cost); asked first of the member's group, the
/// deciders called each other one group deep at a time and overflowed the stack.
#[test]
fn a_chain_of_groups_is_decided_on_a_small_stack() {
    let n = 1000;
    for open in [false, true] {
        let sys = chain_of_groups(n, open);
        let first = kernel(&sys, "chain")[0].clone().expect("admitted");
        let outside = Type::tuple(vec![first.clone(), Type::int()]);
        for t in [first, outside] {
            let v = scaling::on_a_thread(1 << 20, move || {
                Type::forget_emptiness();
                t.verdict()
            });
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
fn never_empty_with_a_value(
    name: &str,
    generate: fn(&mut Rng) -> Vec<E>,
    seeds: std::ops::Range<u64>,
) -> usize {
    let mut checked = 0;
    for seed in seeds.clone() {
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
    assert!(never_empty_with_a_value("claude", gen_claude, 0..600) > 0);
}

#[test]
fn partial_morphisms_are_never_called_empty_with_a_value() {
    assert!(never_empty_with_a_value("mixed", gen_mixed, 0..600) > 0);
}

#[test]
fn layered_systems_are_never_called_empty_with_a_value() {
    assert!(never_empty_with_a_value("layer", gen_layer, 0..600) > 0);
}

#[test]
fn meets_and_differences_are_never_called_empty_with_a_value() {
    assert!(never_empty_with_a_value("cells", gen_cells, 0..600) > 0);
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

#[test]
fn a_chain_decided_again_scales() {
    let chains = scaling::inputs(64, key_chain);
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
    for (&m, ts) in &chains {
        Type::forget_emptiness();
        assert!(!ts[m - 1].is_empty(), "R{} of a key chain of {m}", m - 1);
    }
    scaling::check("is_empty of R(n - 1) of a key chain of n", 64, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][m - 1].is_empty());
    });
}

/// `kernel` builds the groups of a system in time linear in its definitions and references
/// (plan item VERDICT-meet-cost): a chain of n groups, each reading the next, and one group of
/// n definitions (`chain_of`), at n and 8n, the systems written before the runs and each run
/// under names of its own, so no run finds the groups of another. A search from each definition
/// for what it reaches cost the square of the definitions, and a pass over every definition for
/// each group built their cube: 1.57 s for a chain of 1000 groups.
#[test]
fn the_groups_of_a_system_are_built_in_its_size() {
    let runs = std::sync::atomic::AtomicUsize::new(0);
    let build = |sys: &[E]| {
        let run = runs.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let types = kernel(sys, &format!("built{run}"));
        assert!(types.iter().all(Option::is_some), "every group is admitted");
    };
    let n = 128;
    let chains = scaling::inputs(n, |m| chain_of_groups(m, false));
    scaling::check("the groups of a chain of n groups", n, |m| {
        build(&chains[&m])
    });
    let groups = scaling::inputs(n, |m| chain_of(&mut Rng::new(7), m));
    scaling::check("one group of n definitions", n, |m| build(&groups[&m]));
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
#[test]
fn every_member_of_systems_of_meets_and_differences_prints_as_syntax() {
    let mut members = 0;
    for seed in 0..600 {
        let sys = gen_cells(&mut Rng::new(seed));
        for (form, sys) in [("", sys.clone()), ("-", undecided(sys))] {
            let tag = format!("printed-cells{form}{seed}");
            for (i, t) in kernel(&sys, &tag).iter().enumerate() {
                let Some(t) = t else { continue };
                prints_as_syntax(t, &format!("{tag}: R{i} of {}", show_system(&sys)));
                members += 1;
            }
        }
    }
    assert_eq!(members, 1364);
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
        r"type T1 = #a | #b | T2; type T2 = (#a | #b, T1) \ (#b, #a); T2"
    );
    // Two such cycles: the shared `#a | #b` is named once, and each part names the other.
    assert_eq!(
        prints_as_syntax(&shared_chain(2, "chain-two"), "a chain of 2"),
        concat!(
            r"type T1 = #a | #b; type T2 = #a | #b | T4; ",
            r"type T3 = #a | #b | ((T1, T2) \ (#b, #a)); type T4 = (T1, T3) \ (#b, #a); T4"
        )
    );
}

/// A chain of `n` definitions, each a pair whose second component is `#a | #b` or the next
/// definition, the last's the first: `R(k) = ((#a | #b), (#a | #b | R(k + 1))) \ (#b, #a)`.
fn shared_chain(n: usize, tag: &str) -> Type {
    let ab = || E::Union(vec![E::Atom("a"), E::Atom("b")]);
    let sys: Vec<E> = (0..n)
        .map(|k| {
            diff(
                tup(vec![ab(), E::Union(vec![ab(), E::Ref((k + 1) % n)])]),
                tup(vec![E::Atom("b"), E::Atom("a")]),
            )
        })
        .collect();
    kernel(&sys, tag).remove(0).expect("admitted")
}

/// The text of a chain of `n` cycles, each entered at a tuple part that a part kept
/// unevaluated shares, takes time and bytes of order `n log n`: the parts are ordered by their
/// contents, a sort.
#[test]
fn a_chain_of_shared_tuple_parts_prints_in_its_size() {
    let chains = scaling::inputs(64, |n| {
        let t = shared_chain(n, &format!("chain{n}"));
        // The unfoldings are made once, before the runs.
        prints_as_syntax(&t, &format!("a chain of {n}"));
        t
    });
    for (&n, t) in &chains {
        // `#a | #b`, the first pair and the part that names it, and one definition for each
        // other cycle, its pair written inside it: n + 2 in all.
        assert_eq!(t.surface().defs.len(), n + 2, "a chain of {n}");
    }
    scaling::check("the text of a chain of n shared tuple parts", 64, |n| {
        std::hint::black_box(chains[&n].surface());
    });
}
