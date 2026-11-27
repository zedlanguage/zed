//! A term whose parts are shared, written in text linear in its distinct parts (STAGE-print).
//!
//! A [`Shared`] node that two or more places hold, and that is not [`small`], is a *part*. Where
//! that writes fewer nodes (see [`choose`]), its text is written once, as `partN = <text>;` in a
//! block, and each place that holds it writes `partN`. The block is put around a node every path
//! to the part passes through (a dominator), so the part's text and every place that holds it
//! are inside the block: the highest such node below which no name the part may read is bound,
//! so that the definitions stand side by side in one block rather than one inside another.
//!
//! A part's text read at its definition must mean what it means at each place. A name the term
//! binds in one place only, or that is free and bound nowhere, does: the one binder is above
//! the block (see [`shared_form`]). A name bound in two or more places, or bound once and also
//! read outside its binder, may not, as in `x = x + 1; p` and `x = x + 2; p` with `p` reading
//! `x`. Given the names that resolve where the term is written, a part that reads such a name,
//! directly or through the parts it holds, is a function of one value holding all such names,
//! `partN = env1 -> <text>;`, and each place writes `partN(env2)`, the value of the names
//! there, so the names are read where the part is held, as the shared term reads them. Without
//! them, as in `Display`, such a part is written at its first place with a label, `#1=<text>`,
//! and `#1#` at the others.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::term::walk::{Binds, Built, Kid, kids, rebuild, small};
use crate::term::{Prim, Shared, Term};
use crate::value::Value;

/// A node of the graph of a term: the root, a part held in place, or a [`Shared`] node, each
/// shared node once by its id.
struct Node<'a> {
    term: &'a Term,
    /// The parts of the term, in the order written, each with the names bound over it.
    kids: Vec<(usize, Binds<'a>)>,
    /// The number of places that hold the node.
    preds: u32,
}

/// The graph of `root`, node 0 the root: each node's parts, each shared node read once.
fn graph<'a>(root: &'a Term) -> Vec<Node<'a>> {
    let mut nodes = vec![Node {
        term: root,
        kids: Vec::new(),
        preds: 0,
    }];
    let mut ids: HashMap<u64, usize> = HashMap::new();
    let mut todo = vec![0];
    while let Some(v) = todo.pop() {
        let mut ks = Vec::new();
        kids(nodes[v].term, |k, b| {
            let fresh = |nodes: &mut Vec<Node<'a>>, todo: &mut Vec<usize>, t: &'a Term| {
                nodes.push(Node {
                    term: t,
                    kids: Vec::new(),
                    preds: 0,
                });
                todo.push(nodes.len() - 1);
                nodes.len() - 1
            };
            let c = match k {
                Kid::Inline(t) => fresh(&mut nodes, &mut todo, t),
                Kid::Shared(s) => match ids.get(&s.id()) {
                    Some(&c) => c,
                    None => {
                        let c = fresh(&mut nodes, &mut todo, s);
                        ids.insert(s.id(), c);
                        c
                    }
                },
            };
            ks.push((c, b));
        });
        for &(c, _) in &ks {
            nodes[c].preds += 1;
        }
        nodes[v].kids = ks;
    }
    nodes
}

/// The nodes in an order where each node comes after every node that holds it: the reverse of
/// the order in which a depth-first walk from the root finishes them.
fn topological(nodes: &[Node<'_>]) -> Vec<usize> {
    let mut done = vec![false; nodes.len()];
    let mut finished = Vec::with_capacity(nodes.len());
    zed_graph::post_order(
        &mut done,
        [0],
        |done, &v, kids| {
            let first = !std::mem::replace(&mut done[v], true);
            if first {
                kids.extend(nodes[v].kids.iter().map(|&(c, _)| c));
            }
            first
        },
        |_, v| finished.push(v),
    );
    finished.reverse();
    finished
}

/// The immediate dominator of each node, the root its own: the lowest common ancestor, in the
/// tree of dominators built so far, of the nodes that hold it, taken in topological order,
/// which is exact on a graph without cycles ([`zed_graph::dag_idom`]). Also the tree's
/// preorder intervals: `a` dominates `b` exactly when `a`'s interval holds `b`'s.
// Complexity tradeoff: the naive method walks every path from the root, 2^d of them for d
// nested `if`s over one shared arm; here each node is read once and each of its E holders costs
// one ancestor query by binary lifting, O(E log n) time and O(n log n) memory in all.
fn dominators(nodes: &[Node<'_>], order: &[usize]) -> (Vec<usize>, zed_graph::Intervals) {
    let n = nodes.len();
    let tree = zed_graph::dag_idom(n, order, |v| nodes[v].kids.iter().map(|&(c, _)| c));
    // Node 0, the root of the part, hangs from the tree's own root `n`; every other node is
    // held by a node it is reached from, so hangs from a node.
    let mut idom: Vec<usize> = (0..n).map(|v| tree.parent(v)).collect();
    idom[0] = 0;
    (idom, tree.intervals())
}

/// The names that may mean different things at the places of a part: each name bound in two or
/// more places, and each name bound in one place that is read where its binder's scope does
/// not dominate the read (or whose scope is also reached without the binder).
fn rebound(nodes: &[Node<'_>], dom: &zed_graph::Intervals) -> HashSet<Arc<str>> {
    // For each name: the number of places that bind it, and the scope of the last one.
    let mut binders: HashMap<Arc<str>, (usize, usize)> = HashMap::new();
    for v in nodes {
        for &(c, b) in &v.kids {
            b.each(|x| {
                let e = binders.entry(x.clone()).or_insert((0, c));
                *e = (e.0 + 1, c);
            });
        }
    }
    let mut out = HashSet::new();
    for (v, node) in nodes.iter().enumerate() {
        if let Term::Var(x) = node.term
            && let Some(&(count, scope)) = binders.get(x)
        {
            let inside = dom.holds(scope, v);
            if count > 1 || !inside || nodes[scope].preds > 1 {
                out.insert(x.clone());
            }
        }
    }
    out
}

/// Which nodes held in two or more places are written once as parts, and which nodes read a
/// name in `rebound`: each node that is such a name, or holds one. Nodes are taken after the
/// nodes they hold.
///
/// A node held in `r` places, not [`small`], whose text with its own parts written has `s`
/// nodes, is named when that writes fewer nodes: when `s + def + r * place < r * s`, `def` the
/// nodes of `partN = ` (and of `envN ->` when the part reads a rebound name), `place` those of
/// `partN` (or `partN(envN)`). The text of a node counts the definitions put around it
/// (`at[top[idom[p]]]` in [`shared_form`]), so a node written at each of its places writes
/// them at each. A short part, such as `w(w)` in `if c { w(w) } else { w(w) }`, is written in
/// place as before. A part written in place has at most about as many nodes as the references
/// that would replace it, so the text stays within a constant factor of the text with every
/// such node named.
// Complexity tradeoff: the naive method writes each part at each place, 2^d nodes for d nested
// `if`s over one shared arm, and the method before this one passed each part the rebound names
// it reads, `partN(x, y, …)`, O(n k) for k rebound names read through n parts. Here each node is
// read once and its holders once, O(n) in all: a part reads its rebound names from one value
// passed at each place (see `Builder`), so what it reads is one yes or no. The text is
// O(n log k), not O(n): a binder of a rebound name writes the path to its slot, O(log k) pairs
// (`Builder::update`; round 2 of XR-lazy-and-kernel-batch-1, Claude C-2).
fn choose(
    nodes: &[Node<'_>],
    order: &[usize],
    rebound: &HashSet<Arc<str>>,
    top: &[usize],
    idom: &[usize],
) -> (Vec<bool>, Vec<bool>) {
    let n = nodes.len();
    let candidate = |v: usize| v != 0 && nodes[v].preds > 1 && !small(nodes[v].term);
    let mut named = vec![false; n];
    let mut reads = vec![false; n];
    // The nodes of each node's text, its named parts written as references and the parts
    // defined around it in full; saturating, since a node no part holds may be written many
    // times.
    let mut size = vec![0u64; n];
    let mut around = vec![0u64; n];
    let costs = |reads: bool| match reads {
        false => (2, 1),
        true => (4, 3),
    };
    for &p in order.iter().rev() {
        reads[p] = matches!(nodes[p].term, Term::Var(x) if rebound.contains(x))
            || nodes[p].kids.iter().any(|&(c, _)| reads[c]);
        size[p] = nodes[p]
            .kids
            .iter()
            .fold(around[p].saturating_add(1), |s, &(c, _)| {
                s.saturating_add(match named[c] {
                    true => costs(reads[c]).1,
                    false => size[c],
                })
            });
        if !candidate(p) {
            continue;
        }
        let (def, place) = costs(reads[p]);
        let r = u64::from(nodes[p].preds);
        let written_once = size[p]
            .saturating_add(def)
            .saturating_add(r.saturating_mul(place));
        named[p] = written_once < r.saturating_mul(size[p]);
        if named[p] {
            // Above `p` in the order: it dominates `p`.
            let d = top[idom[p]];
            around[d] = around[d].saturating_add(size[p]).saturating_add(def);
        }
    }
    (named, reads)
}

/// What a node's text is built in.
#[derive(Clone, Copy)]
enum Ctx {
    /// Each name read as written, and no part below reads a rebound name: the text is the same
    /// wherever the node is, so it is built once.
    Free,
    /// Outside every part's definition: each name read as written, and env `.0` holds the
    /// value of each rebound name here, for the parts below that read one.
    Root(usize),
    /// In a part's definition: each rebound name read from env `.0`.
    Part(usize),
}

impl Ctx {
    fn env(self) -> Option<usize> {
        match self {
            Ctx::Free => None,
            Ctx::Root(e) | Ctx::Part(e) => Some(e),
        }
    }

    fn with(self, e: usize) -> Ctx {
        match self {
            Ctx::Free => Ctx::Free,
            Ctx::Root(_) => Ctx::Root(e),
            Ctx::Part(_) => Ctx::Part(e),
        }
    }
}

/// The env `to`, which is `from` with the slot of `x` set to `x`, at a binder of `x`.
struct Update {
    x: Arc<str>,
    from: usize,
    to: usize,
}

enum Job {
    Build(usize, Ctx),
    Finish {
        v: usize,
        ctx: Ctx,
        /// For each part of the node: what it is built in, and the envs set over it.
        kids: Vec<(Ctx, Vec<Update>)>,
        /// The parts defined around the node, each with the env it takes if it reads a rebound
        /// name.
        defs: Vec<(usize, Option<usize>)>,
    },
}

/// Builds the term [`shared_form`] gives, from the graph and the choice of parts.
struct Builder<'a, 'r> {
    nodes: &'a [Node<'a>],
    named: Vec<bool>,
    /// Whether the node reads a rebound name, or holds a node that does.
    reads: Vec<bool>,
    /// Whether a part that reads a rebound name is called below the node, not inside another
    /// part: then its text depends on the env in scope.
    needs: Vec<bool>,
    /// The parts defined around each node.
    at: Vec<Vec<usize>>,
    names: Vec<Option<Arc<str>>>,
    /// The rebound names in the order of their slots in the env.
    slots: Vec<Arc<str>>,
    slot: HashMap<Arc<str>, usize>,
    /// The pairs and slots of the env, numbered in preorder ([`env_tree`]): for each but the
    /// root (0), the pair it is an item of and which item.
    up: Vec<(usize, bool)>,
    /// The number in that order of each slot.
    leaf: Vec<usize>,
    /// For the update being written: the numbers on the paths to the slots it sets, and the
    /// name each such slot is set to; cleared after each update.
    touched: Vec<bool>,
    set_to: Vec<Option<Arc<str>>>,
    /// The names that resolve where the term is written; `None` when no scope is given, and a
    /// part that reads a rebound name is then written once and labeled.
    resolves: Option<&'r dyn Fn(&str) -> bool>,
    written: HashSet<&'a str>,
    /// The name of each env, given when it is first read; an env never read is not written.
    envs: Vec<Option<Arc<str>>>,
    /// For an env set at a binder: the env it is set from and the name whose slot it sets.
    made_by: Vec<Option<(usize, Arc<str>)>>,
    /// The number of envs set from each env so far.
    children: Vec<u32>,
    /// Whether an update has passed over each env ([`Builder::update`]).
    passed: Vec<bool>,
    /// The name of each pair read inside an env, by the env and the number of the pair; each is
    /// written once, `envM = envN[b]`, just inside the definition of its env.
    prefixes: HashMap<(usize, usize), Arc<str>>,
    /// The definitions of those names for each env, each after the one it reads.
    prefix_defs: Vec<Vec<(Arc<str>, Term)>>,
    env_count: usize,
    /// The text of a node held in two places built in `Ctx::Free`.
    memo: Vec<Option<Term>>,
    /// The shared node of each labeled part, built at its first place.
    shared: Vec<Option<Shared>>,
    labels: HashSet<*const Term>,
}

impl<'a> Builder<'a, '_> {
    fn new_env(&mut self) -> usize {
        self.envs.push(None);
        self.made_by.push(None);
        self.children.push(0);
        self.passed.push(false);
        self.prefix_defs.push(Vec::new());
        self.envs.len() - 1
    }

    /// The pair numbered `p` inside env `e`: env `e` itself for the root, else a name for it,
    /// defined once (in [`Builder::prefix_defs`]) from the pair above it.
    fn pair(&mut self, e: usize, p: usize) -> Term {
        if p == 0 {
            return Term::Var(self.env_name(e));
        }
        if let Some(name) = self.prefixes.get(&(e, p)) {
            return Term::Var(name.clone());
        }
        let (above, b) = self.up[p];
        let def = index(self.pair(e, above), b);
        let name = self.fresh_env_name();
        self.prefix_defs[e].push((name.clone(), def));
        self.prefixes.insert((e, p), name.clone());
        Term::Var(name)
    }

    /// The item numbered `p` of env `e`: the env itself for the root, else `envM[b]`, `envM`
    /// the pair above it.
    fn item(&mut self, e: usize, p: usize) -> Term {
        match p {
            0 => Term::Var(self.env_name(e)),
            _ => {
                let (above, b) = self.up[p];
                index(self.pair(e, above), b)
            }
        }
    }

    /// `t` inside the definitions of the pairs read in env `e`.
    fn with_prefixes(&mut self, e: usize, mut t: Term) -> Term {
        for (name, def) in std::mem::take(&mut self.prefix_defs[e]).into_iter().rev() {
            t = Term::Let(name, Shared::new(def), Shared::new(t));
        }
        t
    }

    /// The name of env `e`, given now if it has none: the first `envN` not written in the term.
    fn env_name(&mut self, e: usize) -> Arc<str> {
        if self.envs[e].is_none() {
            self.envs[e] = Some(self.fresh_env_name());
        }
        self.envs[e].clone().expect("named above")
    }

    /// The first `envN` not written in the term and not given yet.
    fn fresh_env_name(&mut self) -> Arc<str> {
        loop {
            self.env_count += 1;
            let name = format!("env{}", self.env_count);
            if !self.written.contains(name.as_str()) {
                return name.into();
            }
        }
    }

    /// The env at the root over the slots `[lo, hi)`: each name that resolves there, and `0` in
    /// the slot of a name that does not, which no part reads before a binder of it sets it.
    fn tree(&self, lo: usize, hi: usize) -> Term {
        if hi - lo == 1 {
            let x = &self.slots[lo];
            let resolves = self.resolves.expect("an env only where names resolve");
            return match resolves(x) {
                true => Term::Var(x.clone()),
                false => Term::Lit(Value::Int(0)),
            };
        }
        let mid = lo.midpoint(hi);
        Term::Prim(Prim::Tuple, vec![self.tree(lo, mid), self.tree(mid, hi)])
    }

    /// The value of `x` read from env `e`: `x` itself where `e` is set at a binder of `x`, as
    /// that binder is written just above in the same text; else `envM[b]`, `envM` the pair
    /// above the slot ([`Builder::pair`]), each pair named once however many reads pass it.
    // Complexity tradeoff: writing the path at each read, `envN[i][j]…`, costs O(log k) text per
    // read and O(r log k) for r reads; with each pair named once the reads of an env cost the
    // pairs on the union of their paths, at most 2k, and O(1) more each.
    fn read(&mut self, e: usize, x: &str) -> Term {
        if let Some((_, y)) = &self.made_by[e]
            && **y == *x
        {
            return Term::Var(y.clone());
        }
        let p = self.leaf[self.slot[x]];
        self.item(e, p)
    }

    /// The definition of env `u.to`: the path to the slot of `u.x` rebuilt around `u.x`, the
    /// other item of each pair read from the env it is set from through the names of its pairs
    /// ([`Builder::pair`]), with the slots of a chain of envs no text reads set too (below).
    // Complexity tradeoff: rebuilding the env in full at each binder writes all k slots, O(k)
    // per binder and O(n k) in all; along the path it writes O(log k), each pair beside the path
    // read through the names before it, so no index is written twice. Layer L2's `with` would
    // write one slot of a record in O(1); this layer has none (plan row STAGE-print-with).
    //
    // Chains: the env an update is set from may be one no text has read, set at the binder just
    // above (`x1 = 1; x2 = 1; …; part(envK)` sets k envs and reads only the last). Such an env,
    // when it has no other env set from it and no update has passed it, is passed over: the
    // update is written from the nearest env above it that is named, has two envs set from it,
    // or was passed by an earlier update (the root or a parameter at the latest, which no
    // binder sets), with the slot of each name passed set, the inner binder of a name kept. Why
    // that means the env of the chain: an env passed over is set at a binder above this one in
    // the same text, and every binder of a name with a slot between them, under an env, sets
    // the next env of the chain, so each name passed resolves here to the binder that set its
    // slot last. The env the walk stops at is named where the update reads it
    // ([`Builder::pair`]), and an env named is written by its own binder, whose text is
    // finished after this one (its body holds this one), so its definition is above this one
    // in the text. That holds as well for an env passed over and named later, by a text built
    // after this one; an env no text names is not written.
    //
    // Cost: each env is passed by at most one update, as a walk stops at an env passed before,
    // so the walks cost O(envs + updates) in all. Without that stop (round 2 of
    // XR-lazy-and-kernel-batch-1, Claude C-1 and Gemini C.1) a walk passed envs that a text
    // built after it named while each still had one env set from it (the binder of the next
    // env built at its end, before the other places under the env began), and the update at
    // the next binder up walked the same chain again: `c -> { x1 = 1; if c { x2 = 2; … } else
    // { P } }`, `P` reading every `xj`, walked Θ(k²) envs for k names and its text was Θ(k²)
    // (`bench::print` `writing_chains_of_envs_passed_and_named_later_scales`). A chain of c
    // names costs the pairs on the union of their paths and the pairs beside them, in text and
    // in time (marked up to the first pair marked already, and no sort), at most 2k and at most
    // 2 (c log k + 1), so never more than the c updates written one by one, and the updates of
    // a term cost O((updates + envs) log k) text in all.
    fn update(&mut self, u: &Update) -> (Arc<str>, Term) {
        let to = self.envs[u.to].clone().expect("an env written is read");
        // The slots set and the numbers on their paths, marked from each slot up to the first
        // number marked already, so the marks cost the union of the paths; of two binders of
        // one name the inner, marked first, is kept.
        let mut marked = Vec::new();
        let mut slots_set = Vec::new();
        let mut mark = |b: &mut Self, x: &Arc<str>| {
            let i = b.slot[x];
            if b.set_to[i].is_some() {
                return;
            }
            b.set_to[i] = Some(x.clone());
            slots_set.push(i);
            let mut p = b.leaf[i];
            while !b.touched[p] {
                b.touched[p] = true;
                marked.push(p);
                if p == 0 {
                    break;
                }
                p = b.up[p].0;
            }
        };
        mark(self, &u.x);
        let mut from = u.from;
        while self.envs[from].is_none()
            && self.children[from] == 1
            && !self.passed[from]
            && let Some((above, x)) = self.made_by[from].clone()
        {
            mark(self, &x);
            self.passed[from] = true;
            from = above;
        }
        let t = self.set_slots(from, 0, 0, self.slots.len());
        for p in marked {
            self.touched[p] = false;
        }
        for i in slots_set {
            self.set_to[i] = None;
        }
        (to, t)
    }

    /// The item numbered `p` over the slots `[lo, hi)` of env `from`, with each slot marked in
    /// [`Builder::set_to`] set to its name: the item of `from` itself where no slot in the range
    /// is marked. The pairs are numbered in preorder, so the first item of `p` is `p + 1` and
    /// the second `p + 2 (mid - lo)`, after the `2 (mid - lo) - 1` numbers of the first.
    fn set_slots(&mut self, from: usize, p: usize, lo: usize, hi: usize) -> Term {
        if !self.touched[p] {
            return self.item(from, p);
        }
        if hi - lo == 1 {
            return Term::Var(self.set_to[lo].clone().expect("a slot marked is set"));
        }
        let mid = lo.midpoint(hi);
        let zero = self.set_slots(from, p + 1, lo, mid);
        let one = self.set_slots(from, p + 2 * (mid - lo), mid, hi);
        Term::Prim(Prim::Tuple, vec![zero, one])
    }

    /// Whether a part `c` of a node built in `ctx` is built with the env.
    fn wants(&self, c: usize, ctx: Ctx) -> bool {
        match ctx {
            Ctx::Free => false,
            Ctx::Root(_) => self.needs[c] || (self.named[c] && self.reads[c]),
            Ctx::Part(_) => self.reads[c],
        }
    }

    /// Whether a part `c` is built by a job of its own, not written as a name or a reference.
    fn built_alone(&self, c: usize) -> bool {
        !small(self.nodes[c].term) && (!self.named[c] || (self.resolves.is_none() && self.reads[c]))
    }

    /// The text at a place of the named part `c`: `partN`, or `partN(envN)` if it reads a
    /// rebound name.
    fn reference(&mut self, c: usize, ctx: Ctx) -> Term {
        let name = Term::Var(self.names[c].clone().expect("a part has a name"));
        match self.reads[c] {
            false => name,
            true => {
                let e = ctx
                    .env()
                    .expect("a part that reads a rebound name is called with an env");
                Term::App(Shared::new(name), vec![Term::Var(self.env_name(e))])
            }
        }
    }

    fn start(&mut self, v: usize, ctx: Ctx, todo: &mut Vec<Job>, vals: &mut Vec<Built>) {
        if let Some(s) = &self.shared[v] {
            vals.push(Built::Shared(s.clone()));
            return;
        }
        if let (Ctx::Free, Some(t)) = (ctx, &self.memo[v]) {
            vals.push(Built::Term(t.clone()));
            return;
        }
        let nodes = self.nodes;
        let mut kids = Vec::with_capacity(nodes[v].kids.len());
        let mut builds = Vec::new();
        for &(c, b) in &nodes[v].kids {
            let mut updates = Vec::new();
            let kid = match ctx.env() {
                Some(mut e) if self.wants(c, ctx) => {
                    let mut xs = Vec::new();
                    b.each(|x| {
                        if self.slot.contains_key(x) {
                            xs.push(x.clone());
                        }
                    });
                    for x in xs {
                        let to = self.new_env();
                        self.made_by[to] = Some((e, x.clone()));
                        self.children[e] += 1;
                        updates.push(Update { x, from: e, to });
                        e = to;
                    }
                    ctx.with(e)
                }
                _ => Ctx::Free,
            };
            if self.built_alone(c) {
                builds.push(Job::Build(c, kid));
            }
            kids.push((kid, updates));
        }
        let mut defs = Vec::with_capacity(self.at[v].len());
        for i in 0..self.at[v].len() {
            let p = self.at[v][i];
            let env = self.reads[p].then(|| self.new_env());
            defs.push((p, env));
        }
        let def_builds: Vec<Job> = defs
            .iter()
            .map(|&(p, env)| Job::Build(p, env.map_or(Ctx::Free, Ctx::Part)))
            .collect();
        todo.push(Job::Finish { v, ctx, kids, defs });
        todo.extend(def_builds.into_iter().rev());
        todo.extend(builds.into_iter().rev());
    }

    fn finish(
        &mut self,
        v: usize,
        ctx: Ctx,
        kids: Vec<(Ctx, Vec<Update>)>,
        defs: Vec<(usize, Option<usize>)>,
        vals: &mut Vec<Built>,
    ) {
        let nodes = self.nodes;
        let texts = vals.split_off(vals.len() - defs.len());
        let alone = nodes[v]
            .kids
            .iter()
            .filter(|&&(c, _)| self.built_alone(c))
            .count();
        let mut built = vals.split_off(vals.len() - alone).into_iter();
        let mut parts = Vec::with_capacity(kids.len());
        for (&(c, _), (kid, updates)) in nodes[v].kids.iter().zip(kids) {
            let mut part = if self.built_alone(c) {
                built.next().expect("a value for each job")
            } else if self.named[c] {
                Built::Term(self.reference(c, kid))
            } else {
                match (nodes[c].term, kid) {
                    (Term::Var(x), Ctx::Part(e)) if self.slot.contains_key(x) => {
                        Built::Term(self.read(e, x))
                    }
                    (t, _) => Built::Term(t.clone()),
                }
            };
            if !updates.is_empty() {
                let mut t = part.term();
                for u in updates.iter().rev() {
                    if self.envs[u.to].is_some() {
                        t = self.with_prefixes(u.to, t);
                        let (name, e) = self.update(u);
                        t = Term::Let(name, Shared::new(e), Shared::new(t));
                    }
                }
                part = Built::Term(t);
            }
            parts.push(part);
        }
        let mut t = rebuild(nodes[v].term, parts);
        if let (0, Ctx::Root(e)) = (v, ctx)
            && self.envs[e].is_some()
        {
            let name = self.env_name(e);
            t = self.with_prefixes(e, t);
            t = Term::Let(
                name,
                Shared::new(self.tree(0, self.slots.len())),
                Shared::new(t),
            );
        }
        for ((p, env), text) in defs.into_iter().zip(texts).rev() {
            let text = text.term();
            let def = match env {
                None => text,
                Some(e) => {
                    // A parameter no text reads is named too: `_ ->` is not a lambda.
                    let param = self.env_name(e);
                    let text = self.with_prefixes(e, text);
                    Term::Lam(vec![param], Shared::new(text))
                }
            };
            let name = self.names[p].clone().expect("a part has a name");
            t = Term::Let(name, Shared::new(def), Shared::new(t));
        }
        let out = if self.resolves.is_none() && self.named[v] && self.reads[v] {
            let s = Shared::new(t);
            self.labels.insert(&*s as *const Term);
            self.shared[v] = Some(s.clone());
            Built::Shared(s)
        } else {
            if let Ctx::Free = ctx
                && nodes[v].preds > 1
                && !self.named[v]
            {
                self.memo[v] = Some(t.clone());
            }
            Built::Term(t)
        };
        vals.push(out);
    }
}

/// The shape of an env of `k` slots, a balanced tree of pairs over the slots `[lo, hi)` split at
/// `(lo + hi) / 2`, a single slot its value itself, numbered in preorder from 0 at the root: for
/// each number the pair it is an item of and which item (`false` the first), the root's unused;
/// and the number of each slot.
fn env_tree(k: usize) -> (Vec<(usize, bool)>, Vec<usize>) {
    let mut up = Vec::with_capacity(2 * k);
    let mut leaf = vec![0; k];
    // The ranges to number, each with its parent and item, taken in preorder; none for no
    // slots, where no env is written.
    let mut todo = match k {
        0 => Vec::new(),
        _ => vec![(0, k, 0, false)],
    };
    while let Some((lo, hi, parent, b)) = todo.pop() {
        let p = up.len();
        up.push((parent, b));
        if hi - lo == 1 {
            leaf[lo] = p;
        } else {
            let mid = lo.midpoint(hi);
            todo.push((mid, hi, p, true));
            todo.push((lo, mid, p, false));
        }
    }
    (up, leaf)
}

/// `t[b]`, the first item of a pair for `false` and the second for `true`.
fn index(t: Term, b: bool) -> Term {
    Term::Prim(Prim::TupleGet, vec![t, Term::Lit(Value::Int(i64::from(b)))])
}

/// A term written with each part once: the term, and the shared nodes written with a label.
pub(super) struct Form {
    pub(super) term: Term,
    /// The nodes of the labeled parts, by address, for identity only: the first place of each
    /// writes `#n=` before its text and each other place `#n#`.
    pub(super) labels: HashSet<*const Term>,
}

/// `root` with each part written once: `None` when no part is named ([`choose`]), so the term is
/// written as it is. Otherwise a term that means what `root` means, with no named part held
/// twice but a labeled one: each part `p` defined as `partN = <p>;` in a block around a
/// dominator `d` of `p`, the parts at one node in the order that defines each before the parts
/// that hold it. The names `partN` are the first not written in `root`, counted from 1 in the
/// order the parts are first reached from the end of the text, so the text does not depend on
/// ids.
///
/// A part that reads a name [`rebound`] reads it where it is held, which its definition cannot
/// name. With `resolves`, the names that resolve where the term is written, each such name has
/// a slot in one value, the env, a balanced tree of pairs: the part is defined as
/// `partN = envP -> <p>;`, each rebound name in its text read from `envP` (`envP[1][0]`), and
/// each place writes `partN(envN)`, `envN` the env in scope there. At the root the env is
/// `envN = (…)`, each slot the name if it resolves there and `0` if it does not; below each
/// binder of a rebound name `x` a new env is the old one with the slot of `x` set to `x`. So
/// the slot of `x` in the env in scope anywhere holds what `x` means there: at the root, a
/// name that resolves means itself, and a name that does not has no meaning there and is read
/// only below one of its binders; each binder sets the slot to the value it binds; and a part
/// is passed the env of its place, so inside it the same holds by induction on the nesting of
/// parts. An env no text reads is not written, but for a parameter, which is named. Each
/// part that reads no rebound name is defined as before. A text written with the env costs
/// O(1) per name read and per binder, plus each pair of an env it reads named once and
/// O(log k) for an update written alone, `k` the rebound names ([`Builder::read`],
/// [`Builder::update`]).
///
/// Without `resolves` (`Display` and `Debug`, which have no scope), a part that reads a
/// rebound name is written in place at its first place, labeled `#n=`, and `#n#` at each other
/// place ([`Form::labels`]): that is not a program, but it reads at a glance and costs the
/// part's text once.
///
/// The node `d` is the lowest node at or above the immediate dominator of `p` in the tree of
/// dominators that is the root or the scope, held in one place, of a binder of a name not
/// rebound. A name the definition reads that is rebound is read from the env, so no binder of a
/// rebound name changes what the definition means, and `d` may be above it.
///
/// Why a name `y` not rebound means the same in the definition: `y` is bound in one place `b`
/// whose scope `s` holds every read of `y`, and no path reaches `s` but through `b`, so `s` is
/// held in one place. A read of `y` in the part `p` then lies below `s` on every path, so `s`
/// dominates `p`, and `s` is not `p`, since `p` is held in two places and `s` in one. The
/// dominators of `p` form a chain, so `s` is the immediate dominator of `p` or above it, and so
/// `s` is `d` or above `d`. The block around `d` is inside the scope of `b`, as each place of
/// `p` is.
///
/// Why a part `q` the definition of `p` holds is defined around it: the node `d` of `q` either
/// lies in the text of `p`, or dominates `p`; then it is `d` of `p` or above it, and at one node
/// `q` is defined first. The names `envN` and `partN` are written nowhere else, so no binder
/// captures them, and an env is defined in the scope of the binder that sets it, above every
/// place that reads it.
pub(super) fn shared_form(
    root: &Term,
    resolves: Option<&dyn Fn(&str) -> bool>,
    names: Option<fn(&str) -> &str>,
) -> Option<Form> {
    let nodes = graph(root);
    if !(1..nodes.len()).any(|v| nodes[v].preds > 1 && !small(nodes[v].term)) {
        return None;
    }
    let order = topological(&nodes);
    let (idom, dom) = dominators(&nodes, &order);
    let rebound = rebound(&nodes, &dom);
    // For each node, the lowest node at or above it in the tree of dominators that is the root
    // or the scope, held in one place, of a binder of a name not rebound: where a part it
    // dominates is defined. A scope held in two places binds no name that is read and not
    // rebound, and a block there would be written at each place.
    let mut stop = vec![false; nodes.len()];
    stop[0] = true;
    for v in &nodes {
        for &(c, b) in &v.kids {
            b.each(|x| stop[c] |= !rebound.contains(x) && nodes[c].preds == 1);
        }
    }
    let mut top = vec![0; nodes.len()];
    for &v in &order {
        top[v] = if stop[v] { v } else { top[idom[v]] };
    }
    let (named, reads) = choose(&nodes, &order, &rebound, &top, &idom);
    if !named.contains(&true) {
        return None;
    }
    let mut needs = vec![false; nodes.len()];
    for &v in order.iter().rev() {
        needs[v] = nodes[v].kids.iter().any(|&(c, _)| match named[c] {
            true => reads[c],
            false => needs[c],
        });
    }

    // Every name the term writes, as written (through `names` in a message), so that no name
    // of a part or an env is one of them.
    let mut written: HashSet<&str> = HashSet::new();
    for v in &nodes {
        if let Term::Var(x) = v.term {
            written.insert(names.map_or(x, |f| f(x)));
        }
        for &(_, b) in &v.kids {
            b.each(|x| {
                written.insert(names.map_or(x, |f| f(x)));
            });
        }
    }
    // The slots of the env, each rebound name in the order its first binder is reached.
    let mut slots: Vec<Arc<str>> = Vec::new();
    let mut slot: HashMap<Arc<str>, usize> = HashMap::new();
    if resolves.is_some() {
        for v in &nodes {
            for &(_, b) in &v.kids {
                b.each(|x| {
                    if rebound.contains(x) && !slot.contains_key(x) {
                        slot.insert(x.clone(), slots.len());
                        slots.push(x.clone());
                    }
                });
            }
        }
    }
    let labeled = |p: usize| resolves.is_none() && reads[p];
    let mut names: Vec<Option<Arc<str>>> = vec![None; nodes.len()];
    let mut count = 0usize;
    // The parts defined around each node, the parts held by others first.
    let mut at: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    for &p in order.iter().rev() {
        if named[p] && !labeled(p) {
            let name = loop {
                count += 1;
                let name = format!("part{count}");
                if !written.contains(name.as_str()) {
                    break name;
                }
            };
            names[p] = Some(name.into());
            at[top[idom[p]]].push(p);
        }
    }

    let n = nodes.len();
    let (up, leaf) = env_tree(slots.len());
    let mut b = Builder {
        nodes: &nodes,
        named,
        reads,
        needs,
        at,
        names,
        touched: vec![false; up.len()],
        set_to: vec![None; slots.len()],
        up,
        leaf,
        slots,
        slot,
        resolves,
        written,
        envs: Vec::new(),
        made_by: Vec::new(),
        children: Vec::new(),
        passed: Vec::new(),
        prefixes: HashMap::new(),
        prefix_defs: Vec::new(),
        env_count: 0,
        memo: (0..n).map(|_| None).collect(),
        shared: (0..n).map(|_| None).collect(),
        labels: HashSet::new(),
    };
    let ctx = match b.slots.is_empty() {
        true => Ctx::Free,
        false => Ctx::Root(b.new_env()),
    };
    let mut todo = vec![Job::Build(0, ctx)];
    let mut vals = Vec::new();
    while let Some(job) = todo.pop() {
        match job {
            Job::Build(v, ctx) => b.start(v, ctx, &mut todo, &mut vals),
            Job::Finish { v, ctx, kids, defs } => b.finish(v, ctx, kids, defs, &mut vals),
        }
    }
    let term = vals.pop().expect("the root is built").term();
    Some(Form {
        term,
        labels: b.labels,
    })
}
