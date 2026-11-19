//! A rooted tree grown leaf by leaf, with each node's ancestors at powers of two (binary
//! lifting; M. Bender and M. Farach-Colton, "The LCA Problem Revisited", LATIN 2000, section
//! 2), for lowest common ancestors and ancestors at a given depth in O(log n), and the
//! immediate dominators of a directed acyclic graph built on it.

/// A tree over the nodes `0..n` and one more, the root `n`, grown leaf by leaf: a node not yet
/// attached hangs from nothing and must not be asked about.
// Complexity tradeoff: binary lifting costs O(log n) per query and O(n log n) words, against an
// Euler tour with a sparse table (O(1) per query) which needs the whole tree first; the trees
// here are grown while they are queried (a node's parent is the answer of a query on the nodes
// before it, as in [`dag_idom`]), which binary lifting allows and the Euler tour does not. A
// node's ancestors are stored together (`up[v * levels + j]`), one cache line for the first
// eight levels of a query. The words are `u32`, half the memory of `usize`: `n` is checked
// below `u32::MAX` in [`Lift::new`], which no tree reaches before memory runs out (the table
// alone would take more than 4 * 2^32 * 33 bytes, 528 GB).
pub struct Lift {
    /// The number of ancestors kept per node, `j = 0..levels` for the ancestor `2^j` up.
    levels: usize,
    depth: Vec<u32>,
    /// The ancestor `2^j` above node `v` at `v * levels + j`, the root above the root.
    up: Vec<u32>,
}

impl Lift {
    /// The tree of the root `n` alone, with room for the nodes `0..n` at depths up to `n`.
    pub fn new(n: usize) -> Self {
        Lift::with_depth(n, n)
    }

    /// The tree of the root `n` alone, with room for the nodes `0..n` at depths up to
    /// `deepest`: a caller who knows its tree is shallow keeps fewer levels.
    ///
    /// # Panics
    ///
    /// If `n` is `u32::MAX` or more (see the type's comment).
    pub fn with_depth(n: usize, deepest: usize) -> Self {
        assert!(
            n < u32::MAX as usize,
            "a tree of {n} nodes does not fit in memory"
        );
        // Enough levels that `2^levels > deepest`, so a rise of up to `deepest` is a sum of
        // the kept powers; at least one, the parent. `BITS - leading_zeros` is
        // `zed_kernel::bits::BitLen::bit_len`, written out because zed-graph sits below
        // zed-kernel (DRY-numeric-shared).
        let levels = (usize::BITS - deepest.leading_zeros()).max(1) as usize;
        let mut up = vec![0; (n + 1) * levels];
        up[n * levels..].fill(n as u32);
        Lift {
            levels,
            depth: vec![0; n + 1],
            up,
        }
    }

    /// The root.
    pub fn root(&self) -> usize {
        self.depth.len() - 1
    }

    /// Hangs `v` from `parent`, the root or a node already attached. O(log n).
    pub fn attach(&mut self, v: usize, parent: usize) {
        let l = self.levels;
        self.depth[v] = self.depth[parent] + 1;
        debug_assert!(
            (self.depth[v] as usize) < 1 << l,
            "node {v} is deeper than the depth the tree was made for"
        );
        self.up[v * l] = parent as u32;
        for j in 1..l {
            self.up[v * l + j] = self.up[self.up[v * l + j - 1] as usize * l + j - 1];
        }
    }

    /// The parent of `v`; the root's is the root.
    pub fn parent(&self, v: usize) -> usize {
        self.up[v * self.levels] as usize
    }

    /// The depth of `v`, the root's 0.
    pub fn depth(&self, v: usize) -> usize {
        self.depth[v] as usize
    }

    /// The ancestor of `v` at depth `d`, or `v` itself when it is at depth `d` or above it.
    /// O(log n).
    pub fn up_to(&self, mut v: usize, d: usize) -> usize {
        let l = self.levels;
        let mut rise = self.depth(v).saturating_sub(d);
        let mut j = 0;
        while rise > 0 {
            if rise & 1 == 1 {
                v = self.up[v * l + j] as usize;
            }
            rise >>= 1;
            j += 1;
        }
        v
    }

    /// The lowest common ancestor of `a` and `b`. O(log n).
    pub fn lca(&self, a: usize, b: usize) -> usize {
        let l = self.levels;
        let (mut a, mut b) = (self.up_to(a, self.depth(b)), self.up_to(b, self.depth(a)));
        if a == b {
            return a;
        }
        for j in (0..l).rev() {
            let (x, y) = (self.up[a * l + j], self.up[b * l + j]);
            if x != y {
                (a, b) = (x as usize, y as usize);
            }
        }
        self.parent(a)
    }

    /// Each node's preorder number in a walk from the root, and the largest in its subtree,
    /// children in any order: `w` is in `v`'s subtree when `pre[v] <= pre[w] <= last[v]`. Only
    /// nodes attached are numbered. O(n).
    pub fn intervals(&self) -> Intervals {
        let n = self.depth.len();
        let root = n - 1;
        // The children of each node, in one list grouped by parent (counting sort), so a node
        // costs no list of its own.
        let attached = |v: usize| v == root || self.depth[v] > 0;
        let mut start = vec![0usize; n + 1];
        for v in (0..root).filter(|&v| attached(v)) {
            start[self.parent(v) + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let mut kids = vec![0u32; start[n]];
        let mut fill = start.clone();
        for v in (0..root).filter(|&v| attached(v)) {
            let p = self.parent(v);
            kids[fill[p]] = v as u32;
            fill[p] += 1;
        }
        let (mut pre, mut last) = (vec![0u32; n], vec![0u32; n]);
        let (mut next, mut stack) = (0u32, vec![(root as u32, false)]);
        while let Some((v, closing)) = stack.pop() {
            let v = v as usize;
            if closing {
                last[v] = next - 1;
                continue;
            }
            pre[v] = next;
            next += 1;
            stack.push((v as u32, true));
            stack.extend(kids[start[v]..start[v + 1]].iter().map(|&c| (c, false)));
        }
        Intervals { pre, last }
    }
}

/// A tree's preorder numbers: `w` is in `v`'s subtree when `pre[v] <= pre[w] <= last[v]`.
pub struct Intervals {
    /// Each node's preorder number.
    pub pre: Vec<u32>,
    /// The largest preorder number in each node's subtree.
    pub last: Vec<u32>,
}

impl Intervals {
    /// Whether `a` is `v` or an ancestor of it.
    pub fn holds(&self, a: usize, v: usize) -> bool {
        self.pre[a] <= self.pre[v] && self.pre[v] <= self.last[a]
    }
}

/// The tree of immediate dominators of the acyclic graph over `0..n` whose edges out of `v` are
/// `kids(v)`, `order` listing the nodes each after every node with an edge to it: each node with
/// no edge into it hangs from the root `n`, and every other node from the lowest common
/// ancestor, in the tree built so far, of the nodes with an edge to it. The tree does not
/// depend on which such order is given. Nodes left out of `order` are left out of the tree.
///
/// Exact on an acyclic graph (K. Cooper, T. Harvey and K. Kennedy, "A Simple, Fast Dominance
/// Algorithm", 2001, section 3: in topological order one pass of their intersection reaches
/// the fixed point): the dominators of `v` other than `v` are the nodes on every path from the
/// root to `v`, the common dominators of its predecessors, and those of a node form the chain
/// of its ancestors in the tree, so the common ones are the ancestors of the predecessors'
/// lowest common ancestor and that ancestor is the lowest.
// Complexity tradeoff: each edge costs one lowest common ancestor query, O((n + e) log n) time
// and O(n log n) words, against O(n e) for the iterative data-flow method on bit sets, or
// Lengauer-Tarjan's O(e α(e, n)) which needs no order but much more code and a depth-first
// numbering; on an acyclic graph the order makes one pass enough. The edges are read forward,
// each node passing itself to its children's running common ancestor (`held`), so a caller
// need not build the lists of edges into each node.
pub fn dag_idom<I: IntoIterator<Item = usize>>(
    n: usize,
    order: &[usize],
    mut kids: impl FnMut(usize) -> I,
) -> Lift {
    // No node read yet with an edge to the node. Not the root: the common ancestor of two
    // holders may be the root, and must stay the root when a third is read.
    const NONE: usize = usize::MAX;
    let mut tree = Lift::new(n);
    let root = tree.root();
    // The lowest common ancestor of the nodes read so far with an edge to each node.
    let mut held = vec![NONE; n];
    for &v in order {
        tree.attach(v, if held[v] == NONE { root } else { held[v] });
        for c in kids(v) {
            held[c] = if held[c] == NONE {
                v
            } else {
                tree.lca(held[c], v)
            };
        }
    }
    tree
}

#[cfg(test)]
mod tests {
    use super::{Lift, dag_idom};

    /// A step of xorshift64; started at a value that is not 0.
    fn next(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    #[test]
    fn the_lowest_common_ancestor_agrees_with_the_walk_up_the_parents() {
        let mut state =
            crate::seed::seed("the_lowest_common_ancestor_agrees_with_the_walk_up_the_parents") | 1;
        for _ in 0..300 {
            let n = 1 + (next(&mut state) % 40) as usize;
            let mut tree = Lift::new(n);
            let mut parent = Vec::with_capacity(n);
            for v in 0..n {
                // Each node hangs from the root or a node before it.
                let p = (next(&mut state) as usize) % (v + 1);
                let p = if p == v { n } else { p };
                parent.push(p);
                tree.attach(v, p);
            }
            let path = |mut v: usize| {
                let mut p = vec![v];
                while v != n {
                    v = parent[v];
                    p.push(v);
                }
                p
            };
            let iv = tree.intervals();
            for a in 0..=n {
                for b in 0..=n {
                    let (pa, pb) = (path(a), path(b));
                    let expected = *pa.iter().find(|x| pb.contains(x)).expect("the root");
                    assert_eq!(tree.lca(a, b), expected, "lca({a}, {b})");
                    assert_eq!(iv.holds(a, b), pb.contains(&a), "{a} above {b}");
                }
                // `path(a)` runs from `a` at depth `len - 1` up to the root at depth 0.
                let p = path(a);
                for d in 0..=p.len() {
                    let expected = if d + 1 >= p.len() {
                        a
                    } else {
                        p[p.len() - 1 - d]
                    };
                    assert_eq!(tree.up_to(a, d), expected, "up_to({a}, {d})");
                }
            }
        }
    }

    /// Item TEST-kernel-unreached-paths-6 (moved from zed-kernel's `types/empty/names.rs` with
    /// its copy of [`Lift`]): the lowest common ancestor agrees with the walk up the parents on
    /// every pair of a tree of 200 nodes whose branches part at many depths, so the climb of two
    /// nodes of one depth by their ancestors 2^j above (the line `(a, b) = (x, y)`) runs.
    #[test]
    fn the_lowest_common_ancestor_by_doubling_agrees_on_a_tree_parting_at_many_depths() {
        let k = 200;
        let mut tree = Lift::new(k);
        let mut parent = Vec::with_capacity(k);
        // Nodes 0 to 2 hang from the root and node `v` from node `(v - 3) / 3`: three children
        // each, so the depth grows with the logarithm of `v`.
        for v in 0..k {
            let p = if v < 3 { k } else { (v - 3) / 3 };
            parent.push(p);
            tree.attach(v, p);
        }
        let ancestors = |mut v: usize| {
            let mut up = vec![v];
            while v != k {
                v = parent[v];
                up.push(v);
            }
            up
        };
        for a in 0..=k {
            let ua = ancestors(a);
            for c in 0..=k {
                let uc = ancestors(c);
                let expected = *ua.iter().find(|x| uc.contains(x)).expect("the root");
                assert_eq!(tree.lca(a, c), expected, "lca({a}, {c})");
            }
        }
    }

    /// The dominators of each node of the acyclic graph `kids` over `0..n` by definition: `d`
    /// dominates `v` when `v` is not reached from a node with no edge into it once `d` is
    /// removed (`d == v` included).
    fn dominators_by_removal(n: usize, kids: &[Vec<usize>]) -> Vec<Vec<bool>> {
        let mut has_in = vec![false; n];
        for ks in kids {
            for &c in ks {
                has_in[c] = true;
            }
        }
        let mut dom = vec![vec![false; n]; n];
        for d in 0..n {
            let mut seen = vec![false; n];
            let mut todo: Vec<usize> = (0..n).filter(|&s| !has_in[s] && s != d).collect();
            for &s in &todo {
                seen[s] = true;
            }
            while let Some(v) = todo.pop() {
                for &c in &kids[v] {
                    if c != d && !seen[c] {
                        seen[c] = true;
                        todo.push(c);
                    }
                }
            }
            for (v, row) in dom.iter_mut().enumerate() {
                row[d] = !seen[v];
            }
        }
        dom
    }

    #[test]
    fn immediate_dominators_do_not_depend_on_the_topological_order_on_random_dags() {
        let mut state = crate::seed::seed(
            "immediate_dominators_do_not_depend_on_the_topological_order_on_random_dags",
        ) | 1;
        for _ in 0..500 {
            let n = 1 + (next(&mut state) % 12) as usize;
            // Edges only from a lower number to a higher one under a random relabeling.
            let mut label: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                label.swap(i, next(&mut state) as usize % (i + 1));
            }
            let mut kids = vec![Vec::new(); n];
            for a in 0..n {
                for b in a + 1..n {
                    if next(&mut state) % 3 == 0 {
                        kids[label[a]].push(label[b]);
                    }
                }
            }
            let dom = dominators_by_removal(n, &kids);
            // Several topological orders: Kahn's, taking a random ready node each time.
            let mut first: Option<Vec<usize>> = None;
            for _ in 0..4 {
                let mut need = vec![0; n];
                for ks in &kids {
                    for &c in ks {
                        need[c] += 1;
                    }
                }
                let mut ready: Vec<usize> = (0..n).filter(|&v| need[v] == 0).collect();
                let mut order = Vec::new();
                while !ready.is_empty() {
                    let v = ready.swap_remove(next(&mut state) as usize % ready.len());
                    order.push(v);
                    for &c in &kids[v] {
                        need[c] -= 1;
                        if need[c] == 0 {
                            ready.push(c);
                        }
                    }
                }
                let tree = dag_idom(n, &order, |v| kids[v].iter().copied());
                let idom: Vec<usize> = (0..n).map(|v| tree.parent(v)).collect();
                for v in 0..n {
                    // The immediate dominator: the strict dominator that every other strict
                    // dominator dominates, or the root when there is none.
                    let strict: Vec<usize> = (0..n).filter(|&d| d != v && dom[v][d]).collect();
                    let expected = (strict.iter().copied())
                        .find(|&d| strict.iter().all(|&e| dom[d][e]))
                        .unwrap_or(n);
                    assert_eq!(idom[v], expected, "{kids:?} in order {order:?}: node {v}");
                }
                match &first {
                    None => first = Some(idom),
                    Some(f) => assert_eq!(f, &idom, "{kids:?}: order {order:?}"),
                }
            }
        }
    }
}
