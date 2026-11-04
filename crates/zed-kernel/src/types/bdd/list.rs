//! A diagram as a decision list in its one form, which does not depend on the order of the
//! atoms (step BDD-atom-order): the printers show a diagram from it, since the atom order
//! follows the digests, and the digests differ between builds.
//!
//! Only chains grow a diagram (`Part::zip`), so every diagram is a decision list: literals in
//! turn, the first that holds giving the value, and a default when none holds. Its one form
//! has blocks: the first block holds every literal under which the function is constant, all
//! with one value; each later block holds every literal under which the function is constant
//! once the literals of the blocks before are false; the values alternate, and the default is
//! the value left. A literal is in the first block with value `v` exactly when every path to
//! the leaf `!v` takes the opposite literal, so a block is the atoms forced on the paths to
//! one leaf ([`Bdd::forced_to`]), the next block those forced on the paths to the other leaf
//! once the block's literals are set false, and so on.
//!
//! Setting literals false only deletes edges, so the paths to each leaf are kept as live
//! edges, deleted as the blocks are found: an edge dies when it is set false, when no live
//! edge is left into its source, or when no live edge is left out of its target. A place in
//! the order of atoms is forced on the paths to a leaf when no live edge passes over it and
//! its nodes go on one way only. Each edge dies once, and its death updates a tree over the
//! places, so the time is `O(n log n)` in the nodes however many blocks there are; finding
//! the blocks one by one with [`Bdd::forced_to`] took a pass over the nodes per block.

use std::collections::HashMap;

use super::{Bdd, Branch, Literal};

/// A diagram as a decision list in its one form (module comment).
#[derive(Debug)]
pub(in crate::types) struct List<A: Literal> {
    /// The blocks in order, each its value and its literals: an atom and whether it is
    /// taken. The literals of a block are in no order that means anything.
    pub(in crate::types) blocks: Vec<(bool, Vec<(A, bool)>)>,
    /// The value when no literal holds; or, should the diagram not be a decision list, the
    /// diagram left once every literal of the blocks is false.
    pub(in crate::types) tail: Result<bool, Bdd<A>>,
}

/// Where an edge leads.
#[derive(Clone, Copy)]
enum To {
    Node(usize),
    Leaf(bool),
}

/// The nodes of a diagram, numbered with the root `0`; edge `2u` is the `hi` of node `u` and
/// `2u + 1` its `lo`.
struct Graph<'a, A: Literal> {
    /// The atoms of the nodes, sorted: an atom's index is its place.
    atoms: Vec<&'a A>,
    place: Vec<usize>,
    to: Vec<To>,
    /// The edges into each node.
    into: Vec<Vec<usize>>,
    /// The edges out of the nodes at each place.
    at: Vec<Vec<usize>>,
    /// The nodes, each after its children.
    post: Vec<usize>,
}

impl<'a, A: Literal> Graph<'a, A> {
    fn new(root: &'a Branch<A>) -> Graph<'a, A> {
        // A node is numbered when first entered, so the root is `0`, and leaves the walk after
        // every node below it.
        let mut index: HashMap<u64, usize> = HashMap::new();
        let mut nodes: Vec<&'a Branch<A>> = Vec::new();
        let mut post = Vec::new();
        let mut stack = vec![(root, false)];
        while let Some((n, below)) = stack.pop() {
            if below {
                post.push(index[&n.id]);
                continue;
            }
            if index.contains_key(&n.id) {
                continue;
            }
            index.insert(n.id, nodes.len());
            nodes.push(n);
            stack.push((n, true));
            for c in [&n.lo, &n.hi] {
                if let Bdd::Node(m) = c
                    && !index.contains_key(&m.id)
                {
                    stack.push((m, false));
                }
            }
        }
        let mut atoms: Vec<&A> = nodes.iter().map(|n| &n.atom).collect();
        atoms.sort();
        atoms.dedup();
        let place: Vec<usize> = nodes
            .iter()
            .map(|n| {
                atoms
                    .binary_search(&&n.atom)
                    .expect("the atom of a node is placed")
            })
            .collect();
        let mut to = Vec::with_capacity(2 * nodes.len());
        let mut into = vec![Vec::new(); nodes.len()];
        let mut at = vec![Vec::new(); atoms.len()];
        for (u, n) in nodes.iter().enumerate() {
            for (w, c) in [&n.hi, &n.lo].into_iter().enumerate() {
                let e = 2 * u + w;
                to.push(match c {
                    Bdd::Leaf(v) => To::Leaf(*v),
                    Bdd::Node(m) => {
                        let v = index[&m.id];
                        into[v].push(e);
                        To::Node(v)
                    }
                });
                at[place[u]].push(e);
            }
        }
        Graph {
            atoms,
            place,
            to,
            into,
            at,
            post,
        }
    }

    /// The place an edge leads to: its target's, or past every place for a leaf.
    fn end(&self, e: usize) -> usize {
        match self.to[e] {
            To::Node(v) => self.place[v],
            To::Leaf(_) => self.atoms.len(),
        }
    }
}

/// A count at a place no longer counted: its count fell to 0, and counts only fall.
const RETIRED: i64 = i64::MAX / 2;

/// The number of live edges over each place, as a tree of minima with additions over ranges,
/// which reports each place when its count falls to 0.
struct Over {
    len: usize,
    min: Vec<i64>,
    add: Vec<i64>,
}

impl Over {
    /// The tree of `counts`; the places whose count is 0 are pushed to `zero`.
    fn new(counts: &[i64], zero: &mut Vec<usize>) -> Over {
        let len = counts.len();
        let mut o = Over {
            len,
            min: vec![0; 4 * len.max(1)],
            add: vec![0; 4 * len.max(1)],
        };
        if len > 0 {
            o.build(1, 0, len, counts);
            if o.min[1] == 0 {
                o.zeros(1, 0, len, zero);
            }
        }
        o
    }

    fn build(&mut self, node: usize, lo: usize, hi: usize, counts: &[i64]) {
        if hi - lo == 1 {
            self.min[node] = counts[lo];
            return;
        }
        let mid = (lo + hi) / 2;
        self.build(2 * node, lo, mid, counts);
        self.build(2 * node + 1, mid, hi, counts);
        self.min[node] = self.min[2 * node].min(self.min[2 * node + 1]);
    }

    fn push(&mut self, node: usize) {
        let d = std::mem::take(&mut self.add[node]);
        for c in [2 * node, 2 * node + 1] {
            self.min[c] += d;
            self.add[c] += d;
        }
    }

    /// Takes 1 from the count of each place in `from..to`; the places whose count falls to 0
    /// are pushed to `zero`.
    fn fall(&mut self, from: usize, to: usize, zero: &mut Vec<usize>) {
        if from < to {
            self.fall_in(1, 0, self.len, from, to, zero);
        }
    }

    fn fall_in(
        &mut self,
        node: usize,
        lo: usize,
        hi: usize,
        from: usize,
        to: usize,
        zero: &mut Vec<usize>,
    ) {
        if to <= lo || hi <= from {
            return;
        }
        if from <= lo && hi <= to {
            self.min[node] -= 1;
            self.add[node] -= 1;
            if self.min[node] == 0 {
                self.zeros(node, lo, hi, zero);
            }
            return;
        }
        self.push(node);
        let mid = (lo + hi) / 2;
        self.fall_in(2 * node, lo, mid, from, to, zero);
        self.fall_in(2 * node + 1, mid, hi, from, to, zero);
        self.min[node] = self.min[2 * node].min(self.min[2 * node + 1]);
    }

    /// Retires the places under `node` whose count is 0, pushing them to `zero`.
    fn zeros(&mut self, node: usize, lo: usize, hi: usize, zero: &mut Vec<usize>) {
        if hi - lo == 1 {
            self.min[node] = RETIRED;
            zero.push(lo);
            return;
        }
        self.push(node);
        let mid = (lo + hi) / 2;
        for (c, l, h) in [(2 * node, lo, mid), (2 * node + 1, mid, hi)] {
            if self.min[c] == 0 {
                self.zeros(c, l, h, zero);
            }
        }
        self.min[node] = self.min[2 * node].min(self.min[2 * node + 1]);
    }
}

/// The paths from the root to one leaf, as their live edges.
struct Side {
    live: Vec<bool>,
    /// The live edges out of each node, and into it.
    out: Vec<u8>,
    inn: Vec<u32>,
    over: Over,
    /// Whether no live edge passes over each place.
    unpassed: Vec<bool>,
    /// The live edges on each way, `hi` then `lo`, out of the nodes at each place.
    ways: Vec<[u32; 2]>,
    /// The places whose counts changed since they were last looked at.
    queue: Vec<usize>,
}

impl Side {
    fn new<A: Literal>(g: &Graph<'_, A>, leaf: bool) -> Side {
        let nodes = g.place.len();
        // Whether each node reaches `leaf`, children first.
        let mut reaches = vec![false; nodes];
        for &u in &g.post {
            reaches[u] = (0..2).any(|w| match g.to[2 * u + w] {
                To::Leaf(v) => v == leaf,
                To::Node(v) => reaches[v],
            });
        }
        let count = g.atoms.len();
        let mut s = Side {
            live: vec![false; 2 * nodes],
            out: vec![0; nodes],
            inn: vec![0; nodes],
            over: Over::new(&[], &mut Vec::new()),
            unpassed: vec![false; count],
            ways: vec![[0, 0]; count],
            queue: (0..count).collect(),
        };
        // `passed[i] - passed[i - 1]` live edges pass over place `i`.
        let mut passed = vec![0i64; count + 1];
        for u in (0..nodes).filter(|&u| reaches[u]) {
            for w in 0..2 {
                let e = 2 * u + w;
                let on = match g.to[e] {
                    To::Leaf(v) => v == leaf,
                    To::Node(v) => reaches[v],
                };
                if !on {
                    continue;
                }
                s.live[e] = true;
                s.out[u] += 1;
                if let To::Node(v) = g.to[e] {
                    s.inn[v] += 1;
                }
                s.ways[g.place[u]][w] += 1;
                let (from, to) = (g.place[u] + 1, g.end(e));
                if from < to {
                    passed[from] += 1;
                    passed[to] -= 1;
                }
            }
        }
        let mut counts = Vec::with_capacity(count);
        let mut over = 0;
        for p in &passed[..count] {
            over += p;
            counts.push(over);
        }
        let mut zero = Vec::new();
        s.over = Over::new(&counts, &mut zero);
        for p in zero {
            s.unpassed[p] = true;
        }
        s
    }

    /// Whether no path is left.
    fn empty(&self) -> bool {
        self.out[0] == 0
    }

    /// Deletes edge `e`, and every edge left on no path with it.
    fn kill<A: Literal>(&mut self, g: &Graph<'_, A>, e: usize) {
        let mut work = vec![e];
        let mut zero = Vec::new();
        while let Some(e) = work.pop() {
            if !self.live[e] {
                continue;
            }
            self.live[e] = false;
            let (u, w) = (e / 2, e % 2);
            let p = g.place[u];
            self.out[u] -= 1;
            self.ways[p][w] -= 1;
            if self.ways[p][w] == 0 {
                self.queue.push(p);
            }
            if let To::Node(v) = g.to[e] {
                self.inn[v] -= 1;
                if self.inn[v] == 0 {
                    work.extend([2 * v, 2 * v + 1]);
                }
            }
            self.over.fall(p + 1, g.end(e), &mut zero);
            for q in zero.drain(..) {
                self.unpassed[q] = true;
                self.queue.push(q);
            }
            if self.out[u] == 0 && u != 0 {
                work.extend(g.into[u].iter().copied());
            }
        }
    }

    /// The literals not yet `emitted` under which no path to the leaf is left: each place
    /// whose nodes the paths pass, all going on one way, as its literal the other way.
    fn forced(&mut self, emitted: &[bool]) -> Vec<(usize, bool)> {
        let mut found: Vec<(usize, bool)> = Vec::new();
        for p in std::mem::take(&mut self.queue) {
            if emitted[p] || !self.unpassed[p] {
                continue;
            }
            match self.ways[p] {
                [h, 0] if h > 0 => found.push((p, false)),
                [0, l] if l > 0 => found.push((p, true)),
                _ => {}
            }
        }
        found.sort_unstable();
        found.dedup();
        found
    }
}

impl<A: Literal> Bdd<A> {
    /// The diagram as a decision list in its one form (module comment).
    pub(in crate::types) fn list(&self) -> List<A> {
        let root = match self {
            Bdd::Leaf(v) => {
                return List {
                    blocks: Vec::new(),
                    tail: Ok(*v),
                };
            }
            Bdd::Node(n) => n,
        };
        let g = Graph::new(root);
        let mut sides = [Side::new(&g, false), Side::new(&g, true)];
        if sides[0].empty() || sides[1].empty() {
            return List {
                blocks: Vec::new(),
                tail: Ok(sides[0].empty()),
            };
        }
        let mut emitted = vec![false; g.atoms.len()];
        // The value each emitted atom is fixed to: the one that makes its literal false.
        let mut fixed = vec![false; g.atoms.len()];
        // The first block may have either value: when both have literals, the function is
        // one literal, and its block of value `true` is taken.
        let mut lits = sides[0].forced(&emitted);
        let mut value = true;
        if lits.is_empty() {
            lits = sides[1].forced(&emitted);
            value = false;
        }
        let mut blocks = Vec::new();
        let tail = loop {
            if lits.is_empty() {
                break Err(self.restrict(
                    &|a: &A| {
                        let p = g
                            .atoms
                            .binary_search(&a)
                            .expect("an atom of the diagram is placed");
                        emitted[p].then_some(fixed[p])
                    },
                    &mut HashMap::new(),
                ));
            }
            // The block's literals made false: the paths to leaf `value` lose the edges that
            // take them; the paths to the other leaf took none of them.
            let side = &mut sides[usize::from(value)];
            for &(p, taken) in &lits {
                emitted[p] = true;
                fixed[p] = !taken;
                for &e in &g.at[p] {
                    if (e % 2 == 0) == taken {
                        side.kill(&g, e);
                    }
                }
            }
            blocks.push((
                value,
                lits.iter()
                    .map(|&(p, taken)| (g.atoms[p].clone(), taken))
                    .collect(),
            ));
            if side.empty() {
                break Ok(!value);
            }
            lits = side.forced(&emitted);
            value = !value;
        };
        List { blocks, tail }
    }
}
