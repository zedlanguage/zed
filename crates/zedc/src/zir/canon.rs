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
//! pass and reaches the normal form that [`step`] reaches, in time linear in the graph; and
//! [`key`] hashes a node from the keys of its regions, so the lowering keys each new node
//! without walking the regions below it again.

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

fn normalize(g: &mut Region) {
    g.args.iter_mut().for_each(normal_edge);
    for n in &mut g.nodes {
        normal_shell(n);
        n.regions.iter_mut().for_each(normalize);
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

/// An edge in normal form: the first rule in priority order that applies, until none does.
fn normal_edge(e: &mut Edge) {
    if let Edge::Value(v) = e {
        let mut d = def(v);
        while RULES[1..].iter().any(|rule| (rule.apply)(&mut d)) {}
        v.domain = d.domain.expect("an edge has a domain");
        v.facets = d.facets;
    }
}

/// Each written binder of `p` renamed to its level, the number of binders before it.
fn rename_all(p: &mut Pattern, index: &mut usize) {
    match p {
        Pattern::Bind(name) => {
            if level_of(name).is_none() {
                *name = level_name(*index);
            }
            *index += 1;
        }
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
            ps.iter_mut().for_each(|q| rename_all(q, index))
        }
        Pattern::Fields(_, fs) => fs.iter_mut().for_each(|(_, q)| rename_all(q, index)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
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
    let inner: Vec<Vec<ContentAddress>> = g
        .nodes
        .iter()
        .map(|n| n.regions.iter().map(key).collect())
        .collect();
    region_key(g, &inner)
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
        body: Term::Lit(Value::Tuple(Vec::new())),
    }
}

/// The pattern binders of `g` that still carry their written names.
fn written(g: &Region) -> u64 {
    let mut n = 0;
    for node in &g.nodes {
        if let Op::Match(ps) = &node.op {
            for p in ps {
                binds(p, &mut |name| n += u64::from(level_of(name).is_none()));
            }
        }
        for r in &node.regions {
            n += written(r);
        }
    }
    n
}

/// The binder rule: the first written pattern binder in preorder renamed to its level, its
/// written name a hint on the argument it binds.
fn rename_first(g: &mut Region) -> bool {
    for node in &mut g.nodes {
        if let Op::Match(ps) = &mut node.op {
            for (arm, p) in ps.iter_mut().enumerate() {
                let mut index = 0;
                if let Some(name) = rename_in(p, &mut index) {
                    if let Edge::Value(v) = &mut node.regions[arm].args[index] {
                        v.facets.push(Facet {
                            hint: true,
                            kind: "binder".into(),
                            value: Value::Tuple(vec![
                                Value::Int(index as i64),
                                Value::Str(name.into()),
                            ]),
                        });
                    }
                    return true;
                }
            }
        }
        if node.regions.iter_mut().any(rename_first) {
            return true;
        }
    }
    false
}

/// Renames the first written binder of `p`, counting in `index` the binders before it, and
/// returns its written name.
fn rename_in(p: &mut Pattern, index: &mut usize) -> Option<std::sync::Arc<str>> {
    match p {
        Pattern::Bind(name) if level_of(name).is_none() => {
            let written = name.clone();
            *name = level_name(*index);
            Some(written)
        }
        Pattern::Bind(_) => {
            *index += 1;
            None
        }
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
            ps.iter_mut().find_map(|q| rename_in(q, index))
        }
        Pattern::Fields(_, fs) => fs.iter_mut().find_map(|(_, q)| rename_in(q, index)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => None,
    }
}

/// Calls `f` on each binder name of `p`, in preorder.
fn binds(p: &Pattern, f: &mut dyn FnMut(&str)) {
    match p {
        Pattern::Bind(name) => f(name),
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().for_each(|q| binds(q, f)),
        Pattern::Fields(_, fs) => fs.iter().for_each(|(_, q)| binds(q, f)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
    }
}

/// Calls `f` on each edge of `g`, in preorder.
fn each_edge(g: &Region, f: &mut dyn FnMut(&Edge)) {
    g.args.iter().for_each(&mut *f);
    for node in &g.nodes {
        node.outputs.iter().for_each(&mut *f);
        node.regions.iter().for_each(|r| each_edge(r, f));
    }
}

/// Calls `f` on each edge of `g`, in preorder, mutably.
fn each_edge_mut(g: &mut Region, f: &mut dyn FnMut(&mut Edge)) {
    g.args.iter_mut().for_each(&mut *f);
    for node in &mut g.nodes {
        node.outputs.iter_mut().for_each(&mut *f);
        node.regions.iter_mut().for_each(|r| each_edge_mut(r, f));
    }
}
