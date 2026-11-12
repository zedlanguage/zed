//! The sides of the hulls of atoms over one cluster of a part's rows (`Tier::Local` of
//! [`super::products`], plan row C2-local-tier), found through the block-cut tree of the
//! cluster rather than by one solver search over the whole cluster for each side.
//!
//! The cluster is read as a graph with a node for each atom and one for each row or
//! disjunction (an item), and an edge from each item to each of its atoms; a disjunction's
//! atoms are also joined in a cycle, so that all of them lie in one block with it. A block is a
//! biconnected component of that graph (Tarjan 1972), and a cut node lies in two or more
//! blocks; the blocks and cut nodes form a tree. Each block is asked about only through its own
//! items, the bounds of its atoms, and one constraint for each cut node it holds, which sums up
//! what the blocks on the cut node's other side allow:
//! - for a cut atom, an interval of its values, the meet of the intervals the other sides give;
//! - for a cut row `P_1 + ... + P_k + c >= 0`, where `P_j` is the part of the row whose atoms
//!   lie in block `j`, the row `P_B + c + Σ_{j ≠ B} sup P_j >= 0` on block `B`, and for an
//!   equality also `P_B + c + Σ_{j ≠ B} inf P_j <= 0`; the parts share no atom, so the sum of
//!   their greatest values is the greatest value of their sum.
//!
//! Two passes over the tree carry these: one from the leaves to a root block, and one back, in
//! which each block hears from the side of its parent what all other blocks allow. Each
//! constraint holds wherever the cluster does, so each side found is a bound of the atom over
//! the cluster, and it lies within the bound the cluster's rows give the atom alone. It is the
//! side over the cluster when the values of each cut atom over each side, and of each part of
//! a cut equality, have no gaps; where they have one, the side found may be wider, and
//! [`super::entails_inner`] then asks over the whole part as before.

use std::collections::HashMap;

use zedc_int::int::Int;

use super::formula::{Atom, Con, Ends, Formula, Lin, Model, Rel};

/// One cluster of a part ([`super::clusters`]): its general rows and disjunctions with the
/// difference rows on its atoms alone (`items`), and the bounds of each of its atoms (`ends`).
pub(super) struct Cluster {
    pub(super) items: Vec<Formula>,
    pub(super) ends: Vec<(Atom, Ends)>,
}

/// The clusters of a part, and the cluster of each atom of one.
#[derive(Default)]
pub(super) struct Clusters {
    pub(super) all: Vec<Cluster>,
    pub(super) of: HashMap<Atom, usize>,
}

/// What a block gives about a cut node: for an atom, its least and greatest value; for a row,
/// the least and greatest value of the row's part in the block. `None` is no bound.
type Msg = (Option<Int>, Option<Int>);

/// The bound of each side `asked` (an atom of `cl` and a direction, -1 for the least value and
/// 1 for the greatest) of the hull of the atom over `cl`, given `m`, a point of `cl`; `None`
/// where none is found. Each bound holds at every point of `cl` (see the module comment).
///
/// `and` is [`Formula::and`], and `side` is the solver's search for one side of the hull of an
/// atom over a formula, given a point of it (the parent module's `hull_side`). Both are written
/// in the parent module and passed in, since called from here they would make an import cycle
/// of this file and the parent (step S.1f).
///
/// Complexity tradeoff: one solver search for a side over the whole cluster cost
/// O(sides × cluster) (one cluster of k links joined by a sum of one atom of each: 234 sides at
/// k = 64, 41 times the instructions of k = 8). Here each block `B` is searched once for the
/// message to its parent cut node, and, on the second pass, once for each child cut node and
/// each side asked inside it, each search over `B`'s items and one constraint for each of its
/// cut nodes: O(Σ_B (cuts(B) + sides(B)) × |B|) searches' work in all, with O(n) for the
/// blocks (Tarjan's pass and the tree) and O(deg) for the exclusive meets at a cut node of
/// degree deg (prefix and suffix meets). That is linear in the cluster when its blocks are
/// small, as in links joined by rows or atoms. Residual: a block of size b with s open sides
/// or child cut nodes costs O(s × b), quadratic for one large biconnected block with many open
/// sides. Why: the hull of one atom of a general integer system is an integer program, NP-hard,
/// so no method finds every side of a large block in O(b log b) unless P = NP; the block-cut
/// tree shares the work only across blocks. Trigger: `Tier::Local`, a goal not proved from the
/// cheap bounds. Test: `l01_38_presburger::ladder::products_whose_factors_one_sum_joins_scale`.
/// COMPLEXITY.md row C2.
pub(super) fn cluster_sides(
    cl: &Cluster,
    m: &Model,
    asked: &[(Atom, i64)],
    and: impl Fn(Vec<Formula>) -> Formula,
    side: impl Fn(&Formula, &Atom, &Model, i64) -> Option<Int>,
) -> HashMap<(Atom, i64), Option<Int>> {
    let n_atoms = cl.ends.len();
    let index: HashMap<&Atom, usize> = (cl.ends.iter().enumerate())
        .map(|(i, (a, _))| (a, i))
        .collect();
    let n = n_atoms + cl.items.len();
    // The edges, each with its two nodes, and each node's edges.
    let mut edges: Vec<(usize, usize)> = Vec::new();
    let mut adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    let mut add = |u: usize, v: usize, edges: &mut Vec<(usize, usize)>| {
        adj[u].push((v, edges.len()));
        adj[v].push((u, edges.len()));
        edges.push((u, v));
    };
    for (i, f) in cl.items.iter().enumerate() {
        let v = n_atoms + i;
        let atoms: Vec<usize> = match f {
            Formula::Con(c) => (c.lin.terms.keys())
                .filter_map(|a| index.get(a).copied())
                .collect(),
            _ => (f.atoms().iter())
                .filter_map(|a| index.get(a).copied())
                .collect(),
        };
        for &a in &atoms {
            add(v, a, &mut edges);
        }
        // A disjunction is never a cut node: its atoms are joined in a cycle, one edge for two.
        if !matches!(f, Formula::Con(_)) && atoms.len() >= 2 {
            let k = if atoms.len() == 2 { 1 } else { atoms.len() };
            for j in 0..k {
                add(atoms[j], atoms[(j + 1) % atoms.len()], &mut edges);
            }
        }
    }
    let (blocks, block_of_edge) = biconnected(&adj, edges.len());
    // The nodes of each block, and the blocks of each node, block by block.
    let mut edges_of: Vec<Vec<usize>> = vec![Vec::new(); blocks];
    for (e, &b) in block_of_edge.iter().enumerate() {
        edges_of[b].push(e);
    }
    let mut nodes: Vec<Vec<usize>> = vec![Vec::new(); blocks];
    let mut blocks_of: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, es) in edges_of.iter().enumerate() {
        for &e in es {
            let (u, v) = edges[e];
            for x in [u, v] {
                if blocks_of[x].last() != Some(&b) {
                    blocks_of[x].push(b);
                    nodes[b].push(x);
                }
            }
        }
    }
    let is_cut = |x: usize| blocks_of[x].len() >= 2;
    // The row of a cut item, and its part in each of its blocks.
    let row = |x: usize| match &cl.items[x - n_atoms] {
        Formula::Con(c) => Some(c),
        _ => None,
    };
    let mut part: HashMap<(usize, usize), Lin> = HashMap::new();
    for (e, &(u, v)) in edges.iter().enumerate() {
        let (item, atom) = if u >= n_atoms { (u, v) } else { (v, u) };
        if item < n_atoms || atom >= n_atoms || !is_cut(item) {
            continue;
        }
        if let Some(c) = row(item) {
            let a = &cl.ends[atom].0;
            let lin =
                (part.entry((item, block_of_edge[e]))).or_insert_with(|| Lin::constant(Int::ZERO));
            lin.terms.insert(a.clone(), c.lin.terms[a].clone());
        }
    }
    // The block-cut tree, from each block not yet reached, breadth first: each block's parent
    // cut node and child cut nodes, and each cut node's child blocks.
    let mut parent_cut: Vec<Option<usize>> = vec![None; blocks];
    let mut child_cuts: Vec<Vec<usize>> = vec![Vec::new(); blocks];
    let mut child_blocks: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut seen = vec![false; blocks];
    let mut order: Vec<usize> = Vec::with_capacity(blocks);
    for b0 in 0..blocks {
        if seen[b0] {
            continue;
        }
        seen[b0] = true;
        let mut next = order.len();
        order.push(b0);
        while next < order.len() {
            let b = order[next];
            next += 1;
            for &x in &nodes[b] {
                if !is_cut(x) || parent_cut[b] == Some(x) {
                    continue;
                }
                child_cuts[b].push(x);
                let kids = child_blocks.entry(x).or_default();
                for &c in &blocks_of[x] {
                    if !seen[c] {
                        seen[c] = true;
                        parent_cut[c] = Some(x);
                        kids.push(c);
                        order.push(c);
                    }
                }
            }
        }
    }
    // A cut node's kind: an atom meets intervals; a row sums its parts' spans.
    let is_row = |x: usize| x >= n_atoms;
    let unit = |x: usize| -> Msg {
        if is_row(x) {
            (Some(Int::ZERO), Some(Int::ZERO))
        } else {
            (None, None)
        }
    };
    let meet = |x: usize, a: &Msg, b: &Msg| -> Msg {
        if is_row(x) {
            let sum = |p: &Option<Int>, q: &Option<Int>| match (p, q) {
                (Some(p), Some(q)) => Some(p + q),
                _ => None,
            };
            return (sum(&a.0, &b.0), sum(&a.1, &b.1));
        }
        let lo = match (&a.0, &b.0) {
            (Some(p), Some(q)) => Some(p.max(q).clone()),
            (p, q) => p.clone().or_else(|| q.clone()),
        };
        let hi = match (&a.1, &b.1) {
            (Some(p), Some(q)) => Some(p.min(q).clone()),
            (p, q) => p.clone().or_else(|| q.clone()),
        };
        (lo, hi)
    };
    // The constraints on block `b` that `info`, what the other sides of cut node `x` allow,
    // gives.
    let constrain = |b: usize, x: usize, info: &Msg, out: &mut Vec<Formula>| {
        if !is_row(x) {
            let a = Lin::atom(cl.ends[x].0.clone());
            if let Some(lo) = &info.0 {
                out.push(Formula::Con(Con::ge(&a, &Lin::constant(lo.clone()))));
            }
            if let Some(hi) = &info.1 {
                out.push(Formula::Con(Con::ge(&Lin::constant(hi.clone()), &a)));
            }
            return;
        }
        let (Some(c), Some(p)) = (row(x), part.get(&(x, b))) else {
            return;
        };
        if let Some(sup) = &info.1 {
            let lin = p.plus(&Lin::constant(&c.lin.constant + sup));
            out.push(Formula::Con(Con { lin, rel: Rel::Ge }));
        }
        if c.rel == Rel::Eq
            && let Some(inf) = &info.0
        {
            let lin = p.plus(&Lin::constant(&c.lin.constant + inf)).times(-1);
            out.push(Formula::Con(Con { lin, rel: Rel::Ge }));
        }
    };
    // Each block's own items and the bounds of its atoms.
    let base = |b: usize| -> Vec<Formula> {
        let mut out = Vec::new();
        for &x in &nodes[b] {
            if x >= n_atoms {
                if !is_cut(x) {
                    out.push(cl.items[x - n_atoms].clone());
                }
                continue;
            }
            let (a, (lo, hi)) = &cl.ends[x];
            let a = Lin::atom(a.clone());
            if let Some(lo) = lo {
                out.push(Formula::Con(Con::ge(&a, &Lin::constant(lo.clone()))));
            }
            if let Some(hi) = hi {
                out.push(Formula::Con(Con::ge(&Lin::constant(hi.clone()), &a)));
            }
        }
        out
    };
    // A fresh atom for the value of a row's part, past every auxiliary atom of the cluster.
    let fresh = Atom::Aux(
        (cl.ends.iter())
            .filter_map(|(a, _)| match a {
                Atom::Aux(k) => Some(*k),
                _ => None,
            })
            .max()
            .map_or(0, |k| k + 1),
    );
    // What block `b`, with the constraints `fs`, gives about its cut node `x`.
    let message = |b: usize, x: usize, fs: &[Formula]| -> Msg {
        if !is_row(x) {
            let f = and(fs.to_vec());
            let a = &cl.ends[x].0;
            return (side(&f, a, m, -1), side(&f, a, m, 1));
        }
        let (Some(c), Some(p)) = (row(x), part.get(&(x, b))) else {
            return (None, None);
        };
        let mut fs = fs.to_vec();
        fs.push(Formula::Con(Con {
            lin: Lin::atom(fresh.clone()).minus(p),
            rel: Rel::Eq,
        }));
        let f = and(fs);
        let at: Model = [(fresh.clone(), p.eval_linear(m))].into_iter().collect();
        let inf = if c.rel == Rel::Eq {
            side(&f, &fresh, &at, -1)
        } else {
            None
        };
        (inf, side(&f, &fresh, &at, 1))
    };
    // Which sides are asked, of an atom in one block or of a cut atom; which blocks hold an
    // asked side in their subtree, and which cut nodes need the message of their parent block.
    let mut want_side: HashMap<usize, Vec<i64>> = HashMap::new();
    for (a, dir) in asked {
        if let Some(&i) = index.get(a) {
            want_side.entry(i).or_default().push(*dir);
        }
    }
    let mut wanted = vec![false; blocks];
    let mut need_down = vec![false; n];
    // Children first: a block's child blocks come after it in `order`.
    for &b in order.iter().rev() {
        for &x in &child_cuts[b] {
            need_down[x] |= !is_row(x) && want_side.contains_key(&x);
        }
        wanted[b] = (nodes[b].iter()).any(|&x| !is_cut(x) && want_side.contains_key(&x))
            || child_cuts[b].iter().any(|&x| need_down[x]);
        if let Some(x) = parent_cut[b]
            && wanted[b]
        {
            need_down[x] = true;
        }
    }
    // From the leaves up: each block's message to its parent cut node, and what each cut
    // node's child blocks together allow.
    let mut up: Vec<Msg> = vec![(None, None); blocks];
    let mut child_info: HashMap<usize, Msg> = HashMap::new();
    for &b in order.iter().rev() {
        let Some(x) = parent_cut[b] else { continue };
        let mut fs = base(b);
        for &y in &child_cuts[b] {
            constrain(b, y, &child_info[&y], &mut fs);
        }
        up[b] = message(b, x, &fs);
        let joined = match child_info.get(&x) {
            Some(i) => meet(x, i, &up[b]),
            None => up[b].clone(),
        };
        child_info.insert(x, joined);
    }
    // From the root down: what the other sides of its parent cut node allow each block, the
    // sides asked inside it, and the messages to its child cut nodes.
    let mut info: Vec<Option<Msg>> = vec![None; blocks];
    let mut down: HashMap<usize, Msg> = HashMap::new();
    let mut out: HashMap<(Atom, i64), Option<Int>> = HashMap::new();
    for &b in &order {
        if !wanted[b] {
            continue;
        }
        let mut fs = base(b);
        if let (Some(x), Some(i)) = (parent_cut[b], &info[b]) {
            constrain(b, x, i, &mut fs);
        }
        for &y in &child_cuts[b] {
            constrain(b, y, &child_info[&y], &mut fs);
        }
        let f = and(fs.clone());
        for &x in &nodes[b] {
            if is_cut(x) {
                continue;
            }
            for &dir in want_side.get(&x).into_iter().flatten() {
                let a = &cl.ends[x].0;
                out.insert((a.clone(), dir), side(&f, a, m, dir));
            }
        }
        for &x in child_cuts[b].iter().filter(|&&x| need_down[x]) {
            let d = message(b, x, &fs);
            // Each child block hears the meet of the parent block's message and its siblings'.
            let cs = &child_blocks[&x];
            let mut suffix = vec![unit(x); cs.len() + 1];
            for i in (0..cs.len()).rev() {
                suffix[i] = meet(x, &up[cs[i]], &suffix[i + 1]);
            }
            let mut prefix = d.clone();
            for (i, &c) in cs.iter().enumerate() {
                if wanted[c] {
                    info[c] = Some(meet(x, &prefix, &suffix[i + 1]));
                }
                prefix = meet(x, &prefix, &up[c]);
            }
            down.insert(x, d);
        }
    }
    for (x, dirs) in &want_side {
        let (Some(d), Some(i)) = (down.get(x), child_info.get(x)) else {
            continue;
        };
        let (lo, hi) = meet(*x, d, i);
        for &dir in dirs {
            let a = &cl.ends[*x].0;
            out.insert(
                (a.clone(), dir),
                if dir < 0 { lo.clone() } else { hi.clone() },
            );
        }
    }
    out
}

/// The biconnected components of the graph with adjacency `adj` (each entry a neighbor and the
/// edge's number) and `edges` edges: their number, and the component of each edge. Tarjan's
/// depth-first pass with a stack of edges, with an explicit stack of nodes, so a long path
/// does not deepen the call stack; O(nodes + edges).
fn biconnected(adj: &[Vec<(usize, usize)>], edges: usize) -> (usize, Vec<usize>) {
    let n = adj.len();
    let (mut disc, mut low) = (vec![usize::MAX; n], vec![0; n]);
    let mut block_of = vec![usize::MAX; edges];
    let mut on_stack: Vec<usize> = Vec::new();
    let (mut blocks, mut time) = (0, 0);
    for s in 0..n {
        if disc[s] != usize::MAX {
            continue;
        }
        disc[s] = time;
        low[s] = time;
        time += 1;
        // Each frame: a node, the edge it was reached by, and its next edge to read.
        let mut stack: Vec<(usize, usize, usize)> = vec![(s, usize::MAX, 0)];
        while let Some(top) = stack.last_mut() {
            let (v, by, k) = *top;
            if let Some(&(w, e)) = adj[v].get(k) {
                top.2 += 1;
                if e == by {
                    continue;
                }
                if disc[w] == usize::MAX {
                    on_stack.push(e);
                    disc[w] = time;
                    low[w] = time;
                    time += 1;
                    stack.push((w, e, 0));
                } else if disc[w] < disc[v] {
                    on_stack.push(e);
                    low[v] = low[v].min(disc[w]);
                }
                continue;
            }
            stack.pop();
            let Some(&(u, _, _)) = stack.last() else {
                continue;
            };
            low[u] = low[u].min(low[v]);
            if low[v] >= disc[u] {
                while let Some(f) = on_stack.pop() {
                    block_of[f] = blocks;
                    if f == by {
                        break;
                    }
                }
                blocks += 1;
            }
        }
    }
    (blocks, block_of)
}
