//! The canonicalizer on ZIR (step L1.32): the four rules of step M0.7 ([`crate::canon`]),
//! moved onto the graph unchanged, and the content address taken over the normal form.
//!
//! A graph has no local names but one kind: a match pattern's binders, whose written names a
//! region reads by position, never by name. So the *binders* rule renames the first written
//! pattern binder in preorder to its level, its index among the binders of its pattern, which
//! is the number of the arm region's arguments before the one it binds; its written name
//! becomes a hint facet `binder (index, name)` on that argument's edge. The *hints*, *facets*
//! and *domain* rules are [`crate::canon::RULES`] themselves, applied to one edge at a time,
//! the edges taken in preorder: a region's arguments, then each node's outputs and then its
//! regions, in order. Each rule applies at the first place it applies, in priority order,
//! until none applies; the ranks are the sums of the per-edge ranks, and the tuple of them
//! decreases lexicographically at every step, as it does on kernel terms.
//!
//! The address is the BLAKE3-256 hash of `zed-zir\0`, [`crate::canon::VERSION`], and the
//! binary form ([`super::binary`]) of the normal form. Two graphs that differ only in binder
//! names, hints, facet order or repeats, or the spelling of one set of integers, share it.
//!
//! Every rule acts on one edge, or on one pattern, alone, and the binder rule's hint is
//! removed by the hints rule. So [`canonicalize`] normalizes each edge and each pattern in one
//! pass and reaches the normal form that [`step`] reaches: each edge's facets are sorted once,
//! `O(F log F)` comparisons for an edge of `F` facets, so `O(n log n)` for all the facets of a
//! graph of size `n`, and each edge's integer facts are put in normal form once; and
//! [`key`] hashes a node from the keys of its regions, so the lowering keys each new node
//! without walking the regions below it again.

use std::sync::Arc;

use zed_kernel::term::{Pattern, Term};
use zed_kernel::value::Value;

use super::{Edge, Node, Op, Region, RegionKind, binary};
use crate::address::ContentAddress;
use crate::canon::binders::{level_name, level_of};
use crate::canon::{self, Def, Facet, RULES};

/// The ranks of the four rules on `g`, in rule order.
pub fn ranks(g: &Region) -> [u64; 4] {
    let mut r = [written(g), 0, 0, 0];
    each_edge(g, &mut |e| {
        if let Edge::Value(v) = e {
            let d = def(v);
            for (k, rule) in RULES.iter().enumerate().skip(1) {
                r[k] += (rule.rank)(&d);
            }
        }
    });
    r
}

/// One rewrite: the first rule that applies anywhere, applied at the first place it applies.
/// Returns the rule's name, or `None` when `g` is in normal form.
pub fn step(g: &mut Region) -> Option<&'static str> {
    if rename_first(g) {
        return Some(RULES[0].name);
    }
    for rule in &RULES[1..] {
        let mut done = false;
        each_edge_mut(g, &mut |e| {
            if let (false, Edge::Value(v)) = (done, &mut *e) {
                let mut d = def(v);
                if (rule.apply)(&mut d) {
                    v.domain = d.domain.expect("an edge has a domain");
                    v.facets = d.facets;
                    done = true;
                }
            }
        });
        if done {
            return Some(rule.name);
        }
    }
    None
}

/// The normal form of `g`: the graph [`step`] reaches, in one pass.
pub fn canonicalize(g: &Region) -> Region {
    let mut g = g.clone();
    normalize(&mut g);
    g
}

/// Puts each edge and pattern of `g` in normal form, from a stack of the regions left to do:
/// each is normalized alone, so the order does not matter.
fn normalize(g: &mut Region) {
    let mut todo = vec![g];
    while let Some(r) = todo.pop() {
        r.args.iter_mut().for_each(normal_edge);
        for n in &mut r.nodes {
            normal_shell(n);
            todo.extend(n.regions.iter_mut().map(Arc::make_mut));
        }
    }
}

/// A node's operation and outputs in normal form; its regions are left alone.
fn normal_shell(n: &mut Node) {
    n.outputs.iter_mut().for_each(normal_edge);
    if let Op::Match(ps) = &mut n.op {
        for p in ps {
            rename_all(p, &mut 0);
        }
    }
}

/// An edge in normal form, the one the rules after the binder rule reach (DESIGN M0.7): its
/// hints dropped, its facets sorted once and each run of equal ones kept once, and its integer
/// facts normal. `O(F log F)` comparisons for `F` facets. The facets end in the one order with
/// no adjacent pair out of order or equal, since a facet's [`Ord`] is total and its ties are
/// exactly `==`; so which of two equal facets the unstable sort puts first does not matter.
fn normal_edge(e: &mut Edge) {
    if let Edge::Value(v) = e {
        v.facets.retain(|f| !f.hint);
        v.facets.sort_unstable();
        v.facets.dedup();
        v.domain = v.domain.normal();
    }
}

/// Each written binder of `p` renamed to its level, the number of binders before it.
fn rename_all(p: &mut Pattern, index: &mut usize) {
    // A stack of the subpatterns left, the next on top, visits them in preorder.
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(name) => {
                if level_of(name).is_none() {
                    *name = level_name(*index);
                }
                *index += 1;
            }
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter_mut().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter_mut().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
}

/// The key of node `n` whose regions have the keys `regions`: equal keys mean equal normal
/// forms of the one-node regions holding the nodes (up to the hash).
pub fn node_key(n: &Node, regions: &[ContentAddress]) -> ContentAddress {
    let mut shell = Node {
        op: n.op.clone(),
        inputs: n.inputs.clone(),
        outputs: n.outputs.clone(),
        regions: Vec::new(),
    };
    normal_shell(&mut shell);
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir-node\0");
    h.update(&canon::VERSION.to_le_bytes());
    h.update(&binary::encode(&Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: vec![shell],
        results: Vec::new(),
    }));
    h.update(&(regions.len() as u64).to_le_bytes());
    for r in regions {
        h.update(&r.0);
    }
    ContentAddress(*h.finalize().as_bytes())
}

/// The key of region `r` whose nodes' regions have the keys `inner`, one list per node.
pub fn region_key(r: &Region, inner: &[Vec<ContentAddress>]) -> ContentAddress {
    let mut shell = Region {
        kind: r.kind,
        args: r.args.clone(),
        nodes: Vec::new(),
        results: r.results.clone(),
    };
    shell.args.iter_mut().for_each(normal_edge);
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir-region\0");
    h.update(&canon::VERSION.to_le_bytes());
    h.update(&binary::encode(&shell));
    h.update(&(r.nodes.len() as u64).to_le_bytes());
    for (n, keys) in r.nodes.iter().zip(inner) {
        h.update(&node_key(n, keys).0);
    }
    ContentAddress(*h.finalize().as_bytes())
}

/// The key of `g` from the bottom up: what [`region_key`] gives with every region's key.
pub fn key(g: &Region) -> ContentAddress {
    // Each open region with the keys of its nodes' regions found so far, one list per node
    // begun.
    let mut open: Vec<(&Region, Vec<Vec<ContentAddress>>)> = vec![(g, Vec::new())];
    loop {
        let (r, inner) = open
            .last_mut()
            .expect("the loop returns when the root ends");
        let r = *r;
        if let Some(keys) = inner.last()
            && let Some(sub) = r.nodes[inner.len() - 1].regions.get(keys.len())
        {
            open.push((sub, Vec::new()));
        } else if inner.len() < r.nodes.len() {
            inner.push(Vec::new());
        } else {
            let k = region_key(r, inner);
            open.pop();
            match open.last_mut() {
                Some((_, up)) => up.last_mut().expect("a node is begun").push(k),
                None => return k,
            }
        }
    }
}

/// The content address of `g`.
pub fn address(g: &Region) -> ContentAddress {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir\0");
    h.update(&canon::VERSION.to_le_bytes());
    h.update(&binary::encode(&canonicalize(g)));
    ContentAddress(*h.finalize().as_bytes())
}

/// An edge's facts as the M0.7 rules see a definition: no name and no body.
fn def(v: &super::ValueEdge) -> Def {
    Def {
        name: "".into(),
        domain: Some(v.domain.clone()),
        facets: v.facets.clone(),
        body: Term::Lit(Value::tuple(Vec::new())),
    }
}

/// The pattern binders of `g` that still carry their written names.
fn written(g: &Region) -> u64 {
    let mut n = 0;
    let mut todo = vec![g];
    while let Some(r) = todo.pop() {
        for node in &r.nodes {
            if let Op::Match(ps) = &node.op {
                for p in ps {
                    binds(p, &mut |name| n += u64::from(level_of(name).is_none()));
                }
            }
            todo.extend(node.regions.iter().map(|r| &**r));
        }
    }
    n
}

/// The binder rule: the first written pattern binder in preorder renamed to its level, its
/// written name a hint on the argument it binds. Only the regions on the way down to its node
/// are made unique.
fn rename_first(g: &mut Region) -> bool {
    let Some((steps, k)) = first_written(g) else {
        return false;
    };
    let mut r = g;
    for (k, j) in steps {
        r = Arc::make_mut(&mut r.nodes[k].regions[j]);
    }
    let node = &mut r.nodes[k];
    let Op::Match(ps) = &mut node.op else {
        unreachable!("first_written finds a match node")
    };
    for (arm, p) in ps.iter_mut().enumerate() {
        let mut index = 0;
        if let Some(name) = rename_in(p, &mut index) {
            if let Edge::Value(v) = &mut Arc::make_mut(&mut node.regions[arm]).args[index] {
                v.facets.push(Facet {
                    hint: true,
                    kind: "binder".into(),
                    value: Value::tuple(vec![Value::Int(index as i64), Value::Str(name.into())]),
                });
            }
            return true;
        }
    }
    unreachable!("first_written finds a written binder")
}

/// The place of the first node of `g`, in preorder, whose patterns hold a written binder: the
/// node and region indices down to its region, and its index there.
fn first_written(g: &Region) -> Option<(Vec<(usize, usize)>, usize)> {
    let has_written = |p: &Pattern| {
        let mut found = false;
        binds(p, &mut |name| found |= level_of(name).is_none());
        found
    };
    /// A region being searched: node `k` is next, or is being searched, its patterns already
    /// read when `read` and its regions before `j` already searched.
    struct Frame<'a> {
        r: &'a Region,
        k: usize,
        j: usize,
        read: bool,
    }
    let mut frames = vec![Frame {
        r: g,
        k: 0,
        j: 0,
        read: false,
    }];
    while let Some(top) = frames.last_mut() {
        let Some(node) = top.r.nodes.get(top.k) else {
            frames.pop();
            if let Some(up) = frames.last_mut() {
                up.j += 1;
            }
            continue;
        };
        if !top.read {
            top.read = true;
            if let Op::Match(ps) = &node.op
                && ps.iter().any(has_written)
            {
                let k = top.k;
                let steps = frames[..frames.len() - 1].iter().map(|f| (f.k, f.j));
                return Some((steps.collect(), k));
            }
        }
        if let Some(sub) = node.regions.get(top.j) {
            frames.push(Frame {
                r: sub,
                k: 0,
                j: 0,
                read: false,
            });
        } else {
            top.k += 1;
            top.j = 0;
            top.read = false;
        }
    }
    None
}

/// Renames the first written binder of `p`, counting in `index` the binders before it, and
/// returns its written name.
fn rename_in(p: &mut Pattern, index: &mut usize) -> Option<std::sync::Arc<str>> {
    // A stack of the subpatterns left, the next on top, visits them in preorder.
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(name) if level_of(name).is_none() => {
                let written = name.clone();
                *name = level_name(*index);
                return Some(written);
            }
            Pattern::Bind(_) => *index += 1,
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter_mut().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter_mut().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    None
}

/// Calls `f` on each binder name of `p`, in preorder.
fn binds(p: &Pattern, f: &mut dyn FnMut(&str)) {
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(name) => f(name),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
}

/// What is left of a walk over the edges in preorder: a region, whose arguments come first,
/// or a node, whose outputs come before its regions.
enum Part<R, N> {
    Region(R),
    Node(N),
}

/// Calls `f` on each edge of `g`, in preorder.
fn each_edge(g: &Region, f: &mut dyn FnMut(&Edge)) {
    let mut todo = vec![Part::Region(g)];
    while let Some(part) = todo.pop() {
        match part {
            Part::Region(r) => {
                r.args.iter().for_each(&mut *f);
                todo.extend(r.nodes.iter().rev().map(Part::Node));
            }
            Part::Node(n) => {
                n.outputs.iter().for_each(&mut *f);
                todo.extend(n.regions.iter().rev().map(|r| Part::Region(&**r)));
            }
        }
    }
}

/// Calls `f` on each edge of `g`, in preorder, mutably.
fn each_edge_mut(g: &mut Region, f: &mut dyn FnMut(&mut Edge)) {
    let mut todo = vec![Part::Region(g)];
    while let Some(part) = todo.pop() {
        match part {
            Part::Region(r) => {
                r.args.iter_mut().for_each(&mut *f);
                todo.extend(r.nodes.iter_mut().rev().map(Part::Node));
            }
            Part::Node(n) => {
                n.outputs.iter_mut().for_each(&mut *f);
                let subs = n.regions.iter_mut().rev();
                todo.extend(subs.map(|r| Part::Region(Arc::make_mut(r))));
            }
        }
    }
}
