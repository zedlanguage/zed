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

use crate::term::{Binds, Kid, Prim, Shared, Term, kids, small};
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
    let mut todo = vec![(0, 0)];
    done[0] = true;
    while let Some((v, i)) = todo.pop() {
        match nodes[v].kids.get(i) {
            Some(&(c, _)) => {
                todo.push((v, i + 1));
                if !done[c] {
                    done[c] = true;
                    todo.push((c, 0));
                }
            }
            None => finished.push(v),
        }
    }
    finished.reverse();
    finished
}

/// The immediate dominator of each node, the root its own: the lowest common ancestor, in the
/// tree of dominators built so far, of the nodes that hold it, taken in topological order,
/// which is exact on a graph without cycles. Also the depth of each node in that tree.
// Complexity tradeoff: the naive method walks every path from the root, 2^d of them for d
// nested `if`s over one shared arm; here each node is read once and each of its E holders costs
// one ancestor query by binary lifting, O(E log n) time and O(n log n) memory in all.
fn dominators(nodes: &[Node<'_>], order: &[usize]) -> Vec<usize> {
    let n = nodes.len();
    let levels = (usize::BITS - n.leading_zeros()).max(1) as usize;
    let mut up = vec![vec![0usize; n]; levels];
    let mut depth = vec![0usize; n];
    let mut idom = vec![usize::MAX; n];
    idom[0] = 0;
    let lca = |up: &[Vec<usize>], depth: &[usize], mut a: usize, mut b: usize| {
        if depth[a] < depth[b] {
            std::mem::swap(&mut a, &mut b);
        }
        let mut diff = depth[a] - depth[b];
        let mut j = 0;
        while diff > 0 {
            if diff & 1 == 1 {
                a = up[j][a];
            }
            diff >>= 1;
            j += 1;
        }
        if a == b {
            return a;
        }
        for j in (0..up.len()).rev() {
            if up[j][a] != up[j][b] {
                a = up[j][a];
                b = up[j][b];
            }
        }
        up[0][a]
    };
    let mut held_by = vec![usize::MAX; n];
    for &v in order {
        if v != 0 {
            idom[v] = held_by[v];
            depth[v] = depth[idom[v]] + 1;
            up[0][v] = idom[v];
            for j in 1..levels {
                up[j][v] = up[j - 1][up[j - 1][v]];
            }
        }
        for &(c, _) in &nodes[v].kids {
            held_by[c] = match held_by[c] {
                usize::MAX => v,
                u => lca(&up, &depth, u, v),
            };
        }
    }
    idom
}

/// When each node is entered and left by a depth-first walk of the tree of dominators: `a`
/// dominates `b` exactly when `a`'s span holds `b`'s.
fn spans(idom: &[usize]) -> Vec<(usize, usize)> {
    let n = idom.len();
    let mut children = vec![Vec::new(); n];
    for v in 1..n {
        children[idom[v]].push(v);
    }
    let mut span = vec![(0, 0); n];
    let mut clock = 0;
    let mut todo = vec![(0, 0)];
    while let Some((v, i)) = todo.pop() {
        if i == 0 {
            span[v].0 = clock;
            clock += 1;
        }
        match children[v].get(i) {
            Some(&c) => {
                todo.push((v, i + 1));
                todo.push((c, 0));
            }
            None => span[v].1 = clock,
        }
    }
    span
}

/// The names that may mean different things at the places of a part: each name bound in two or
/// more places, and each name bound in one place that is read where its binder's scope does
/// not dominate the read (or whose scope is also reached without the binder).
fn rebound(nodes: &[Node<'_>], idom: &[usize]) -> HashSet<Arc<str>> {
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
    let span = spans(idom);
    let mut out = HashSet::new();
    for (v, node) in nodes.iter().enumerate() {
        if let Term::Var(x) = node.term
            && let Some(&(count, scope)) = binders.get(x)
        {
            let inside = span[scope].0 <= span[v].0 && span[v].1 <= span[scope].1;
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
// passed at each place (see `Builder`), so what it reads is one yes or no.
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

/// A part built for [`rebuild`]: a term, or a shared node every place of a labeled part holds.
enum Built {
    Term(Term),
    Shared(Shared),
}

impl Built {
    fn term(self) -> Term {
        match self {
            Built::Term(t) => t,
            Built::Shared(_) => unreachable!("a labeled part is held in a shared node"),
        }
    }

    fn shared(self) -> Shared {
        match self {
            Built::Term(t) => Shared::new(t),
            Built::Shared(s) => s,
        }
    }
}

/// `t` with its parts replaced by `parts`, in the order [`kids`] gives them.
fn rebuild(t: &Term, parts: Vec<Built>) -> Term {
    type Parts = std::vec::IntoIter<Built>;
    let next = |ps: &mut Parts| ps.next().expect("a part for each part").term();
    let sh = |ps: &mut Parts| ps.next().expect("a part for each part").shared();
    let mut ps = parts.into_iter();
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
        Term::Lam(xs, _) => Term::Lam(xs.clone(), sh(&mut ps)),
        Term::Push(x, _) => Term::Push(x.clone(), sh(&mut ps)),
        Term::App(_, args) => {
            let f = sh(&mut ps);
            Term::App(f, args.iter().map(|_| next(&mut ps)).collect())
        }
        Term::Prim(p, args) => Term::Prim(*p, args.iter().map(|_| next(&mut ps)).collect()),
        Term::Let(x, _, _) => {
            let a = sh(&mut ps);
            Term::Let(x.clone(), a, sh(&mut ps))
        }
        Term::If(..) => {
            let (a, b) = (sh(&mut ps), sh(&mut ps));
            Term::If(a, b, sh(&mut ps))
        }
        Term::Match(_, arms) => {
            let e = sh(&mut ps);
            Term::Match(
                e,
                arms.iter()
                    .map(|(p, _)| (p.clone(), next(&mut ps)))
                    .collect(),
            )
        }
        Term::Fam { var, .. } => {
            let domain = sh(&mut ps);
            Term::Fam {
                domain,
                var: var.clone(),
                body: sh(&mut ps),
            }
        }
        Term::Reindex { witness, .. } => {
            let (family, kf) = (sh(&mut ps), sh(&mut ps));
            Term::Reindex {
                family,
                kf,
                vf: sh(&mut ps),
                witness: witness.clone(),
            }
        }
        Term::Discard { .. } => {
            let family = sh(&mut ps);
            Term::Discard {
                family,
                sel: sh(&mut ps),
            }
        }
        Term::Fold {
            identity,
            depth,
            ev,
            ..
        } => {
            let (family, op) = (sh(&mut ps), sh(&mut ps));
            Term::Fold {
                family,
                op,
                identity: identity.as_ref().map(|_| sh(&mut ps)),
                depth: *depth,
                ev: ev.clone(),
            }
        }
        Term::Fix {
            this,
            key,
            kind,
            ev,
            ..
        } => {
            let (init, step) = (sh(&mut ps), sh(&mut ps));
            let kind = match kind {
                crate::term::FixKind::Lattice { .. } => {
                    crate::term::FixKind::Lattice { join: sh(&mut ps) }
                }
                crate::term::FixKind::Definedness => crate::term::FixKind::Definedness,
            };
            Term::Fix {
                init,
                step,
                this: this.clone(),
                key: key.clone(),
                kind,
                ev: ev.clone(),
            }
        }
        Term::Gen { pos, .. } => {
            let (init, step) = (sh(&mut ps), sh(&mut ps));
            Term::Gen {
                init,
                step,
                guard: sh(&mut ps),
                pos: *pos,
            }
        }
    }
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
    /// The names that resolve where the term is written; `None` when no scope is given, and a
    /// part that reads a rebound name is then written once and labeled.
    resolves: Option<&'r dyn Fn(&str) -> bool>,
    written: HashSet<&'a str>,
    /// The name of each env, given when it is first read; an env never read is not written.
    envs: Vec<Option<Arc<str>>>,
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
        self.envs.len() - 1
    }

    /// The name of env `e`, given now if it has none: the first `envN` not written in the term.
    fn env_name(&mut self, e: usize) -> Arc<str> {
        if self.envs[e].is_none() {
            let name = loop {
                self.env_count += 1;
                let name = format!("env{}", self.env_count);
                if !self.written.contains(name.as_str()) {
                    break name;
                }
            };
            self.envs[e] = Some(name.into());
        }
        self.envs[e].clone().expect("named above")
    }

    /// The steps from the env to the slot of `x`: at each pair, the first item (`false`) or the
    /// second. The env is a balanced tree of pairs over the slots `[lo, hi)`, split at
    /// `(lo + hi) / 2`, a single slot its value itself.
    fn path(&self, x: &str) -> Vec<bool> {
        let i = self.slot[x];
        let (mut lo, mut hi) = (0, self.slots.len());
        let mut steps = Vec::new();
        while hi - lo > 1 {
            let mid = (lo + hi) / 2;
            steps.push(i >= mid);
            if i < mid {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        steps
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
        let mid = (lo + hi) / 2;
        Term::Prim(Prim::Tuple, vec![self.tree(lo, mid), self.tree(mid, hi)])
    }

    /// The value of `x` read from env `e`: `envN[i][j]…`, one index for each pair on the path.
    fn read(&mut self, e: usize, x: &str) -> Term {
        let mut t = Term::Var(self.env_name(e));
        for b in self.path(x) {
            t = index(t, b);
        }
        t
    }

    /// The definitions that write env `u.to`: a name for each pair on the path to the slot of
    /// `u.x` but the last, each read from the one before it, then the new env, the path rebuilt
    /// around `u.x` with the other item of each pair read from those names.
    // Complexity tradeoff: rebuilding the env in full at each binder writes all k slots, O(k)
    // per binder and O(n k) in all; along the path it writes O(log k), each pair beside the path
    // read through the names before it, so no index is written twice. Layer L2's `with` would
    // write one slot of a record in O(1); this layer has none (plan row STAGE-print-with).
    fn update(&mut self, u: &Update) -> Vec<(Arc<str>, Term)> {
        let path = self.path(&u.x);
        let to = self.envs[u.to].clone().expect("an env written is read");
        if path.is_empty() {
            return vec![(to, Term::Var(u.x.clone()))];
        }
        let mut defs = Vec::with_capacity(path.len());
        let mut on = vec![Term::Var(self.env_name(u.from))];
        for &b in &path[..path.len() - 1] {
            let e = self.new_env();
            let name = self.env_name(e);
            defs.push((
                name.clone(),
                index(on.last().expect("one at least").clone(), b),
            ));
            on.push(Term::Var(name));
        }
        let mut t = Term::Var(u.x.clone());
        for (b, at) in path.iter().zip(on).rev() {
            let other = index(at, !b);
            let pair = match b {
                false => vec![t, other],
                true => vec![other, t],
            };
            t = Term::Prim(Prim::Tuple, pair);
        }
        defs.push((to, t));
        defs
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
                        for (name, e) in self.update(u).into_iter().rev() {
                            t = Term::Let(name, Shared::new(e), Shared::new(t));
                        }
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
/// O(log k) per name read and per binder, `k` the rebound names.
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
    let idom = dominators(&nodes, &order);
    let rebound = rebound(&nodes, &idom);
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
    let mut b = Builder {
        nodes: &nodes,
        named,
        reads,
        needs,
        at,
        names,
        slots,
        slot,
        resolves,
        written,
        envs: Vec::new(),
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
