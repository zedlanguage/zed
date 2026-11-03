//! Integer feasibility of rows `±x ± y + k >= 0` and `±x + k >= 0` (DESIGN.md sec:domains, step
//! L1.38), by the test of Lahiri and Musuvathi [UTVPI]: such rows have an integer point exactly
//! when their constraint graph has no negative cycle and no zero-weight cycle through both
//! literals of a variable whose part from `+x` to `-x` has odd weight.
//!
//! The graph has a node for each literal, `+x` at `2j` and `-x` at `2j + 1`. The row
//! `l1 + l2 <= k`, with `l1` and `l2` literals, is the two edges `¬l1 → l2` and `¬l2 → l1` of
//! weight `k`, and `l1 <= k` is the edge `¬l1 → l1` of weight `2k`. The graph has a negative
//! cycle exactly when it has no potential, an integer `p` at each node under which no edge
//! `u → v` of weight `w` has `p(v) > p(u) + w`; the shortest paths from a source joined to
//! every node by an edge of weight 0 give one when there is. Its zero-weight cycles are then
//! exactly the cycles of its tight edges, those with `p(v) = p(u) + w`, since the slacks of a
//! cycle sum to its weight and none is below zero; and along tight edges the path from `+x` to
//! `-x` weighs `p(-x) - p(+x)`. The test is then one shortest-path search and one strongly
//! connected components pass over the tight edges. No rational arithmetic is needed.
//!
//! When the graph has no cycle the distances are taken in one pass over its nodes in topological
//! order, in time linear in the nodes and edges. Otherwise the search is the Bellman–Ford–Moore
//! queue with Tarjan's subtree disassembly [BFCT]: when a node's distance falls, the subtree
//! below it in the shortest-path tree is taken out of the tree, since each of its distances will
//! fall with it, and the edge's tail lying in that subtree closes a negative cycle. Its work is
//! at most the nodes times the edges, and in the tests near the edges; a near-linear bound for
//! graphs with cycles is open (COMPLEXITY.md, S18).
//!
//! [UTVPI]: S. K. Lahiri and M. Musuvathi, "An Efficient Decision Procedure for UTVPI
//! Constraints", FroCoS 2005.
//! [BFCT]: B. V. Cherkassky and A. V. Goldberg, "Negative-cycle detection algorithms",
//! Mathematical Programming 85 (1999), 277–311.

use std::collections::VecDeque;

use super::int::Int;
use super::simplex::Term;

/// Whether the rows, each of one or two terms with unit coefficients, over `n` variables, have
/// no integer point.
pub fn integer_empty(n: usize, rows: &[(&[Term], &Int)]) -> bool {
    // The literal `-c·x` of a term `c·x`, as a node.
    let lit = |(j, c): &Term| if c.is_negative() { 2 * j } else { 2 * j + 1 };
    let mut out: Vec<Vec<(usize, Int)>> = vec![Vec::new(); 2 * n];
    for (a, k) in rows {
        match a {
            [t] => {
                let l = lit(t);
                out[l ^ 1].push((l, *k + *k));
            }
            [s, t] => {
                let (l1, l2) = (lit(s), lit(t));
                out[l1 ^ 1].push((l2, (*k).clone()));
                out[l2 ^ 1].push((l1, (*k).clone()));
            }
            _ => unreachable!("a row of one or two terms"),
        }
    }
    let Some(p) = potential(&out) else {
        return true;
    };
    let tight: Vec<Vec<usize>> = out
        .iter()
        .zip(&p)
        .map(|(es, pu)| {
            es.iter()
                .filter(|(v, w)| p[*v] == pu + w)
                .map(|(v, _)| *v)
                .collect()
        })
        .collect();
    let comp = components(&tight);
    let two = Int::from(2);
    (0..n).any(|j| {
        comp[2 * j] == comp[2 * j + 1] && !(&p[2 * j + 1] - &p[2 * j]).mod_floor(&two).is_zero()
    })
}

/// A potential of the graph `out`, its edges `u → (v, w)`, or `None` when it has a negative
/// cycle: the distances from a source joined to each node by an edge of weight 0.
fn potential(out: &[Vec<(usize, Int)>]) -> Option<Vec<Int>> {
    let n = out.len();
    // When the graph has no cycle, its nodes in topological order (Kahn) relax each edge once,
    // whatever the signs of the weights, in O(V + E). Whether there is a cycle depends only on
    // the graph, so the search below is taken exactly when one exists.
    let mut indegree = vec![0usize; n];
    for edges in out {
        for (v, _) in edges {
            indegree[*v] += 1;
        }
    }
    let mut ready: VecDeque<usize> = indegree
        .iter()
        .enumerate()
        .filter_map(|(v, &degree)| (degree == 0).then_some(v))
        .collect();
    let mut order = Vec::with_capacity(n);
    while let Some(u) = ready.pop_front() {
        order.push(u);
        for (v, _) in &out[u] {
            indegree[*v] -= 1;
            if indegree[*v] == 0 {
                ready.push_back(*v);
            }
        }
    }
    if order.len() == n {
        let mut distance = vec![Int::ZERO; n];
        for u in order {
            for (v, weight) in &out[u] {
                let candidate = &distance[u] + weight;
                if candidate < distance[*v] {
                    distance[*v] = candidate;
                }
            }
        }
        return Some(distance);
    }
    let root = n;
    let mut d = vec![Int::ZERO; n];
    // The shortest-path tree in preorder, as a ring through `next` and `prev`, the source
    // first, with each node's depth; at first each node is a child of the source.
    let mut next: Vec<usize> = (1..=n).chain([0]).collect();
    let mut prev: Vec<usize> = [n].into_iter().chain(0..n).collect();
    let mut depth = vec![1usize; n + 1];
    depth[root] = 0;
    let mut in_tree = vec![true; n];
    let mut queued = vec![true; n];
    let mut queue: VecDeque<usize> = (0..n).collect();
    while let Some(u) = queue.pop_front() {
        queued[u] = false;
        if !in_tree[u] {
            continue;
        }
        for (v, w) in &out[u] {
            let v = *v;
            let to = &d[u] + w;
            if to >= d[v] {
                continue;
            }
            if v == u {
                return None;
            }
            // Takes `v` and its subtree out of the tree; `u` among them closes a negative cycle.
            if in_tree[v] {
                let mut c = next[v];
                while depth[c] > depth[v] {
                    if c == u {
                        return None;
                    }
                    in_tree[c] = false;
                    c = next[c];
                }
                next[prev[v]] = c;
                prev[c] = prev[v];
            }
            // `v` becomes the first child of `u`.
            depth[v] = depth[u] + 1;
            next[v] = next[u];
            prev[next[u]] = v;
            next[u] = v;
            prev[v] = u;
            in_tree[v] = true;
            d[v] = to;
            if !queued[v] {
                queued[v] = true;
                queue.push_back(v);
            }
        }
    }
    Some(d)
}

/// The strongly connected component of each node (Tarjan), with an explicit stack.
fn components(out: &[Vec<usize>]) -> Vec<usize> {
    const NONE: usize = usize::MAX;
    let n = out.len();
    let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0; n], vec![NONE; n]);
    let (mut next, mut comps) = (0, 0);
    let mut held: Vec<usize> = Vec::new();
    // Each frame is a node and the place of the next edge to follow.
    let mut frames: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if index[root] != NONE {
            continue;
        }
        frames.push((root, 0));
        index[root] = next;
        low[root] = next;
        next += 1;
        held.push(root);
        while let Some(&mut (v, ref mut e)) = frames.last_mut() {
            if let Some(&w) = out[v].get(*e) {
                *e += 1;
                if index[w] == NONE {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    held.push(w);
                    frames.push((w, 0));
                } else if comp[w] == NONE {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(u, _)) = frames.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                loop {
                    let w = held.pop().expect("held");
                    comp[w] = comps;
                    if w == v {
                        break;
                    }
                }
                comps += 1;
            }
        }
    }
    comp
}

#[cfg(test)]
mod tests {
    use super::{Int, potential};

    #[test]
    fn acyclic_signed_edges_have_an_exact_potential() {
        let graph = vec![
            vec![(1, Int::from(-7)), (2, Int::from(-1))],
            vec![(2, Int::from(-3))],
            vec![],
        ];
        let distance = potential(&graph).expect("an acyclic graph has no negative cycle");
        assert_eq!(distance, vec![Int::ZERO, Int::from(-7), Int::from(-10)]);
    }

    #[test]
    fn a_negative_cycle_is_still_rejected() {
        let graph = vec![vec![(1, Int::from(-1))], vec![(0, Int::ZERO)]];
        assert!(potential(&graph).is_none());
        let feasible = vec![vec![(1, Int::from(-1))], vec![(0, Int::ONE)]];
        assert!(potential(&feasible).is_some());
    }
}
