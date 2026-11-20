//! The biconnected components of an undirected graph (R. Tarjan, "Depth-First Search and Linear
//! Graph Algorithms", SIAM Journal on Computing 1(2), 146-160, 1972, doi:10.1137/0201010;
//! J. Hopcroft and R. Tarjan, "Algorithm 447: efficient algorithms for graph manipulation",
//! CACM 16(6), 372-378, 1973, doi:10.1145/362248.362272), as a partition of the edges: one
//! depth-first pass keeps a stack of edges and the low point of each node, and pops a block
//! when a child's low point does not reach above its parent. Checked 2026-11-20: both DOIs and
//! titles on Crossref (the second title was given without "Algorithm 447"); the papers not
//! read, the method from memory.
//! `blocks_are_the_classes_no_cut_node_separates_on_random_multigraphs` checks the blocks
//! against their definition on random multigraphs.

/// Calls `found` with the edges of each biconnected component (block) of the undirected graph
/// `adj`, each block once: a set of edges in which any two lie on a common simple cycle, or a
/// single edge on no cycle. `adj[v]` lists the edges at node `v`, each as the node at its other
/// end and its number, below `edges`; an edge between two nodes is listed at both, so parallel
/// edges are told apart by their numbers. A self-loop (listed twice at its node) is a block of
/// its own, given once. The nodes `0..adj.len()` are searched in order, each row in its
/// order; the blocks come in the order the search completes them, a block after every block
/// found below it in the search tree, and each block's edges in the order the search first
/// read them (a tree edge before the edges found from its lower end).
///
/// `excluded`, if given, is a node removed from the graph with every edge at it: those edges
/// are in no block.
///
/// A node lies in two or more blocks exactly when it is a cut node (its removal leaves more
/// connected components), with one exception: a node with a self-loop also lies in the loop's
/// block, so a caller that reads cut nodes from block membership leaves self-loops out first.
// Complexity tradeoff: Tarjan's single depth-first pass with a stack of edges, O(n + e) time and
// O(n + e) space, on an explicit stack of frames so a long path does not deepen the call stack.
// Naive alternative: remove each node and count components, O(n (n + e)). The edge that reached
// a node is skipped by its number, not by its other end: skipping every edge back to the parent
// node (as the copy in zedc-presburger's modular/brooks.rs did before DRY-graph-shared) drops
// the second of two parallel edges from its block, since it is read as an edge to the parent.
pub fn biconnected(
    adj: &[Vec<(usize, usize)>],
    edges: usize,
    excluded: Option<usize>,
    mut found: impl FnMut(&[usize]),
) {
    const NEW: usize = usize::MAX;
    let n = adj.len();
    // The time each node was reached, and the least time of a node reached from its subtree
    // by one back edge (the low link).
    let (mut disc, mut low) = (vec![NEW; n], vec![0; n]);
    // Self-loops already given as a block: each is read twice at its node.
    let mut looped = vec![false; edges];
    // The edges read and not yet in a block.
    let mut open: Vec<usize> = Vec::new();
    let mut time = 0;
    for s in 0..n {
        if Some(s) == excluded || disc[s] != NEW {
            continue;
        }
        disc[s] = time;
        low[s] = time;
        time += 1;
        // Each frame: a node, the number of the edge it was reached by, and its next edge.
        let mut stack: Vec<(usize, usize, usize)> = vec![(s, NEW, 0)];
        while let Some(top) = stack.last_mut() {
            let (v, by, k) = *top;
            if let Some(&(w, e)) = adj[v].get(k) {
                top.2 += 1;
                if e == by || Some(w) == excluded {
                    continue;
                }
                if w == v {
                    if !looped[e] {
                        looped[e] = true;
                        found(&[e]);
                    }
                } else if disc[w] == NEW {
                    open.push(e);
                    disc[w] = time;
                    low[w] = time;
                    time += 1;
                    stack.push((w, e, 0));
                } else if disc[w] < disc[v] {
                    // A back edge to an ancestor; read again from the ancestor's side, where
                    // `disc[w] > disc[v]`, it is not pushed a second time.
                    open.push(e);
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
                // `v`'s subtree hangs from `u` alone: its edges above `by` on the stack, and
                // `by`, are one block.
                let at = open
                    .iter()
                    .rposition(|&f| f == by)
                    .expect("the edge that reached a node is open until its block is given");
                found(&open[at..]);
                open.truncate(at);
            }
        }
    }
}

/// The number of blocks of [`biconnected`] and the block of each edge, the blocks numbered from
/// 0 in the order found; an edge at `excluded` is in block `usize::MAX`.
pub fn block_of_edges(
    adj: &[Vec<(usize, usize)>],
    edges: usize,
    excluded: Option<usize>,
) -> (usize, Vec<usize>) {
    let mut block_of = vec![usize::MAX; edges];
    let mut blocks = 0;
    biconnected(adj, edges, excluded, |es| {
        for &e in es {
            block_of[e] = blocks;
        }
        blocks += 1;
    });
    (blocks, block_of)
}

#[cfg(test)]
mod tests {
    use super::{biconnected, block_of_edges};

    /// The adjacency of the undirected graph with edges `ends` over `n` nodes, each edge listed
    /// at both ends (a self-loop twice at its node) under its place in `ends`.
    fn adjacency(n: usize, ends: &[(usize, usize)]) -> Vec<Vec<(usize, usize)>> {
        let mut adj = vec![Vec::new(); n];
        for (e, &(a, b)) in ends.iter().enumerate() {
            adj[a].push((b, e));
            adj[b].push((a, e));
        }
        adj
    }

    /// The component of each node of `ends` over `n` nodes with node `gone` and its edges
    /// removed, by repeated search: the plain method the oracle below uses.
    fn components_without(n: usize, ends: &[(usize, usize)], gone: Option<usize>) -> Vec<usize> {
        let adj = adjacency(n, ends);
        let mut comp = vec![usize::MAX; n];
        let mut count = 0;
        for s in 0..n {
            if Some(s) == gone || comp[s] != usize::MAX {
                continue;
            }
            comp[s] = count;
            let mut todo = vec![s];
            while let Some(v) = todo.pop() {
                for &(w, _) in &adj[v] {
                    if Some(w) != gone && comp[w] == usize::MAX {
                        comp[w] = count;
                        todo.push(w);
                    }
                }
            }
            count += 1;
        }
        comp
    }

    /// Whether the two edges `e` and `f` (neither a self-loop) are in one block, by the
    /// definition through cut nodes, O(n (n + e)): they are when they are in one connected
    /// component and no node `x` separates them, `x` separating them when the ends of `e` and
    /// of `f` other than `x` lie in different components of the graph without `x`. Proof: the
    /// blocks and cut nodes of a connected graph form a tree, and two edges of different blocks
    /// have a cut node on the tree's path between their blocks, whose removal leaves the two
    /// blocks' other nodes apart; two edges of one block stay joined after any one node is
    /// removed, as a block with three nodes or more stays connected without any one node, and a
    /// block of two nodes (one edge or several parallel ones) keeps its other node.
    fn same_block_by_cuts(
        n: usize,
        ends: &[(usize, usize)],
        gone: Option<usize>,
        e: usize,
        f: usize,
    ) -> bool {
        let whole = components_without(n, ends, gone);
        if whole[ends[e].0] != whole[ends[f].0] {
            return false;
        }
        (0..n).filter(|&x| Some(x) != gone).all(|x| {
            let mut without: Vec<(usize, usize)> = ends.to_vec();
            // `x` keeps its number but loses every edge, so it is removed in effect.
            without.retain(|&(a, b)| a != x && b != x);
            let comp = components_without(n, &without, gone);
            let other = |(a, b): (usize, usize)| if a == x { b } else { a };
            comp[other(ends[e])] == comp[other(ends[f])]
        })
    }

    /// Checks [`block_of_edges`] on `ends` over `n` nodes without `gone` against the oracle:
    /// every edge not at `gone` in exactly one block, a self-loop alone, two other edges in one
    /// block exactly when no node separates them. Returns the pairs of edges put together and
    /// those put apart.
    fn blocks_agree(n: usize, ends: &[(usize, usize)], gone: Option<usize>) -> (usize, usize) {
        let adj = adjacency(n, ends);
        let (blocks, block_of) = block_of_edges(&adj, ends.len(), gone);
        let mut given = vec![0; ends.len()];
        biconnected(&adj, ends.len(), gone, |es| {
            for &e in es {
                given[e] += 1;
            }
        });
        let (mut together, mut apart) = (0, 0);
        for (e, &(a, b)) in ends.iter().enumerate() {
            let at_gone = Some(a) == gone || Some(b) == gone;
            assert_eq!(
                given[e],
                usize::from(!at_gone),
                "{ends:?} without {gone:?}: edge {e}"
            );
            assert_eq!(block_of[e] == usize::MAX, at_gone, "{ends:?}: edge {e}");
            if at_gone {
                continue;
            }
            assert!(block_of[e] < blocks);
            for (f, &(c, d)) in ends.iter().enumerate().skip(e + 1) {
                if Some(c) == gone || Some(d) == gone {
                    continue;
                }
                let same = if a == b || c == d {
                    false
                } else {
                    same_block_by_cuts(n, ends, gone, e, f)
                };
                assert_eq!(
                    block_of[e] == block_of[f],
                    same,
                    "{ends:?} without {gone:?}: edges {e} and {f}"
                );
                if same { together += 1 } else { apart += 1 }
            }
        }
        (together, apart)
    }

    #[test]
    fn parallel_edges_share_a_block_and_a_self_loop_is_a_block_of_its_own() {
        // Edges 0 and 1 join nodes 0 and 1 twice, so they lie on the cycle 0 -1- 1 -0- 0, one
        // block; edge 2 (1 - 2) is on no cycle, a block alone; edge 3 is a self-loop at 2. A
        // search that skips every edge back to the parent node, as modular/brooks.rs did, reads
        // edge 1 from node 1 as the edge back to node 0 and leaves it out of every block.
        let ends = [(0, 1), (0, 1), (1, 2), (2, 2)];
        let adj = adjacency(3, &ends);
        let mut found: Vec<Vec<usize>> = Vec::new();
        biconnected(&adj, ends.len(), None, |es| {
            let mut es = es.to_vec();
            es.sort_unstable();
            found.push(es);
        });
        found.sort();
        assert_eq!(found, [vec![0, 1], vec![2], vec![3]]);
        let (together, apart) = blocks_agree(3, &ends, None);
        assert!(together > 0 && apart > 0);
    }

    #[test]
    fn an_excluded_node_takes_its_edges_out_of_every_block() {
        // A triangle 0 1 2 is one block; without node 0, edges 1 - 2 and 2 - 3 are blocks alone.
        let ends = [(0, 1), (1, 2), (2, 0), (2, 3)];
        let adj = adjacency(4, &ends);
        let (blocks, block_of) = block_of_edges(&adj, ends.len(), None);
        assert_eq!(blocks, 2);
        assert_eq!(block_of[0], block_of[1]);
        assert_eq!(block_of[1], block_of[2]);
        assert_ne!(block_of[2], block_of[3]);
        let (blocks, block_of) = block_of_edges(&adj, ends.len(), Some(0));
        assert_eq!(blocks, 2);
        assert_eq!((block_of[0], block_of[2]), (usize::MAX, usize::MAX));
        assert_ne!(block_of[1], block_of[3]);
    }

    /// A step of xorshift64, which stays at 0 once there; [`random_multigraph`] starts it at a
    /// value that is not 0. The shifts 13, 7, 17 are Marsaglia's (G. Marsaglia, "Xorshift
    /// RNGs", J. Stat. Softw. 8(14), 2003, doi:10.18637/jss.v008.i14); the full comment is in
    /// tests/src `seed.rs`, struct `Xorshift64`.
    fn next(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    /// A multigraph of 1 to 9 nodes and up to 2n edges, parallel edges and self-loops among
    /// them, and maybe a node to exclude.
    fn random_multigraph(state: &mut u64) -> (usize, Vec<(usize, usize)>, Option<usize>) {
        let n = 1 + (next(state) % 9) as usize;
        let e = (next(state) % (2 * n as u64 + 1)) as usize;
        let ends = (0..e)
            .map(|_| (next(state) as usize % n, next(state) as usize % n))
            .collect();
        let gone = (next(state) % 3 == 0).then(|| next(state) as usize % n);
        (n, ends, gone)
    }

    #[test]
    fn blocks_are_the_classes_no_cut_node_separates_on_random_multigraphs() {
        let mut state =
            crate::seed::seed("blocks_are_the_classes_no_cut_node_separates_on_random_multigraphs")
                | 1;
        for _ in 0..3000 {
            let (n, ends, gone) = random_multigraph(&mut state);
            blocks_agree(n, &ends, gone);
        }
    }

    /// A path of `n` nodes is `n - 1` blocks, searched without deepening the call stack.
    #[test]
    fn a_long_path_is_one_block_per_edge() {
        let n = 200_000;
        let ends: Vec<(usize, usize)> = (1..n).map(|v| (v - 1, v)).collect();
        let adj = adjacency(n, &ends);
        let (blocks, _) = block_of_edges(&adj, ends.len(), None);
        assert_eq!(blocks, n - 1);
    }
}
