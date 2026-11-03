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
//! order, in time linear in the nodes and edges. Otherwise the search is Goldberg and Radzik's
//! [GR] (the algorithm GOR of [BFCT]): each pass orders the nodes reached from those whose
//! distance fell in the last pass, along edges of negative reduced cost, topologically, and
//! relaxes their edges in that order; a cycle of such edges is a negative cycle. On the tests'
//! graphs it takes two or three passes at every size; its worst case is the nodes times the
//! edges (COMPLEXITY.md, C24).
//!
//! [UTVPI]: S. K. Lahiri and M. Musuvathi, "An Efficient Decision Procedure for UTVPI
//! Constraints", FroCoS 2005.
//! [GR]: A. V. Goldberg and T. Radzik, "A heuristic improvement of the Bellman-Ford
//! algorithm", Applied Mathematics Letters 6 (1993), 3–6.
//! [BFCT]: B. V. Cherkassky and A. V. Goldberg, "Negative-cycle detection algorithms",
//! Mathematical Programming 85 (1999), 277–311.

use std::collections::VecDeque;

use super::int::Int;
use super::linear::Term;

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
    match potential(&out) {
        Some(p) => odd_zero_cycle(n, &out, &p),
        None => true,
    }
}

/// Whether a zero-weight cycle of the graph `out` over the literals of `n` variables passes
/// through both literals of a variable with a part of odd weight from `+x` to `-x`, read off the
/// tight edges under the potential `p`. Every potential gives the same answer: the tight edges
/// that lie on cycles are those of the zero-weight cycles, and a path along them weighs the
/// difference of the potentials at its ends.
fn odd_zero_cycle(n: usize, out: &[Vec<(usize, Int)>], p: &[Int]) -> bool {
    let tight: Vec<Vec<usize>> = out
        .iter()
        .zip(p)
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
    // Complexity tradeoff: nothing is refused and every answer is exact, but the search below
    // takes up to one pass per node, O(V·E) in all, against the O(E log V) the rule allows.
    // A pass reaches every node whose distance may fall and orders them, so most graphs settle
    // in a few passes (two or three on the tests' hubs and paths at every size, XT3); the passes
    // grow with the nodes only when the topological order of the edges of negative reduced
    // cost moves one step per pass, as on BAD-GOR of Cherkassky and Goldberg augmented with
    // heavy random edges and permuted labels (Cassis et al. 2025, arXiv 2502.11999, appendix):
    // 129 passes at k = 256 and 1,026 at k = 2,048 (XT3), 58.4 times the work from k to 8k. A
    // negative cycle that no cycle of edges of negative reduced cost shows is found by the bound
    // on the passes below, in the same worst case. The complete algorithms, deterministic negative-weight shortest
    // paths in near-linear time (Duong 2026, arXiv 2609.05590), are large and unimplemented
    // here. Test: `l01_38_presburger::stages::bad_gor_scales` (ignored, it fails the limit);
    // COMPLEXITY.md C24. Complete solution: item UTVPI-NEAR, running such an algorithm beside
    // this search and taking the first to finish, which gives the same decisions since every
    // potential does (`odd_zero_cycle`).
    //
    // Goldberg and Radzik. `fell` lists the nodes whose distance fell in the last pass, at first
    // every node at its distance 0 from the source, and `in_fell` marks them.
    let mut d = vec![Int::ZERO; n];
    let mut fell: Vec<usize> = (0..n).collect();
    let mut in_fell = vec![true; n];
    // The visited set of each pass's search: the pass in which a node was last reached, and
    // whether the search is still below it.
    let mut reached = vec![0usize; n];
    let mut open = vec![false; n];
    let mut stack: Vec<(usize, usize)> = Vec::new();
    let mut postorder: Vec<usize> = Vec::with_capacity(n);
    // Whether the edge `u → (v, w)` has negative reduced cost.
    let falls = |d: &[Int], u: usize, v: usize, w: &Int| &d[u] + w < d[v];
    let mut pass = 0;
    loop {
        pass += 1;
        // The nodes reached from those in `fell` along edges of negative reduced cost, in
        // postorder of a depth-first search with an explicit stack; each frame is a node and
        // the place of its next edge.
        postorder.clear();
        for &s in &fell {
            in_fell[s] = false;
            if reached[s] == pass || !out[s].iter().any(|(v, w)| falls(&d, s, *v, w)) {
                continue;
            }
            // Without a negative cycle, the distances after pass k are at most those of the
            // paths of k edges (Bellman and Ford's argument: each node whose distance fell is
            // searched from in the next pass), and a shortest path has at most n - 1 edges. So
            // an edge left to relax in pass n shows a negative cycle.
            if pass >= n {
                return None;
            }
            reached[s] = pass;
            open[s] = true;
            stack.push((s, 0));
            while let Some((u, e)) = stack.last_mut() {
                let u = *u;
                let Some((v, w)) = out[u].get(*e) else {
                    open[u] = false;
                    postorder.push(u);
                    stack.pop();
                    continue;
                };
                *e += 1;
                if !falls(&d, u, *v, w) {
                    continue;
                }
                if reached[*v] != pass {
                    reached[*v] = pass;
                    open[*v] = true;
                    stack.push((*v, 0));
                } else if open[*v] {
                    // A cycle of edges of negative reduced cost, so of negative weight.
                    return None;
                }
            }
        }
        fell.clear();
        if postorder.is_empty() {
            return Some(d);
        }
        // Relaxed in topological order, so a fall travels along a whole path in one pass.
        for &u in postorder.iter().rev() {
            for (v, w) in &out[u] {
                let to = &d[u] + w;
                if to < d[*v] {
                    d[*v] = to;
                    if !in_fell[*v] {
                        in_fell[*v] = true;
                        fell.push(*v);
                    }
                }
            }
        }
    }
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
    use std::collections::VecDeque;

    use super::{Int, odd_zero_cycle, potential};

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

    /// The reference search: Bellman–Ford–Moore with a first-in first-out queue, which has
    /// found a negative cycle when a node is taken from the queue for the n + 1st time.
    fn bellman_ford_moore(out: &[Vec<(usize, Int)>]) -> Option<Vec<Int>> {
        let n = out.len();
        let mut d = vec![Int::ZERO; n];
        let mut queued = vec![true; n];
        let mut taken = vec![0usize; n];
        let mut queue: VecDeque<usize> = (0..n).collect();
        while let Some(u) = queue.pop_front() {
            queued[u] = false;
            taken[u] += 1;
            if taken[u] > n {
                return None;
            }
            for (v, w) in &out[u] {
                let to = &d[u] + w;
                if to < d[*v] {
                    d[*v] = to;
                    if !queued[*v] {
                        queued[*v] = true;
                        queue.push_back(*v);
                    }
                }
            }
        }
        Some(d)
    }

    /// splitmix64, so the graphs are the same on every run.
    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    #[test]
    fn random_graphs_get_the_decisions_of_bellman_ford_moore() {
        // 1,000 graphs of the rows of 25 variables, so 50 literals, with 10 to 109 rows of one
        // or two literals `l1 + l2 <= k` and constants -5 to 20, built as `integer_empty`
        // builds them. Both
        // searches must agree on a negative cycle, give potentials that hold on every edge, and
        // give the same parity decision. The counts show that each answer occurs.
        let (vars, mut state) = (25usize, 1u64);
        let (mut negative, mut odd, mut point) = (0, 0, 0);
        for _ in 0..1000 {
            let mut out: Vec<Vec<(usize, Int)>> = vec![Vec::new(); 2 * vars];
            let rows = 10 + next(&mut state) % 100;
            for _ in 0..rows {
                let k = Int::from((next(&mut state) % 26) as i64 - 5);
                let l1 = (next(&mut state) % (2 * vars as u64)) as usize;
                if next(&mut state).is_multiple_of(4) {
                    out[l1 ^ 1].push((l1, &k + &k));
                } else {
                    let l2 = (next(&mut state) % (2 * vars as u64)) as usize;
                    // A third of the rows with a constant up to 5 are equalities, the row and
                    // its opposite `¬l1 + ¬l2 <= -k`, which make the zero-weight cycles.
                    if k <= Int::from(5) && next(&mut state).is_multiple_of(3) {
                        out[l1].push((l2 ^ 1, -&k));
                        out[l2].push((l1 ^ 1, -&k));
                    }
                    out[l1 ^ 1].push((l2, k.clone()));
                    out[l2 ^ 1].push((l1, k));
                }
            }
            let found = potential(&out);
            let reference = bellman_ford_moore(&out);
            assert_eq!(found.is_some(), reference.is_some(), "graph {out:?}");
            let (Some(p), Some(q)) = (found, reference) else {
                negative += 1;
                continue;
            };
            for (u, edges) in out.iter().enumerate() {
                for (v, w) in edges {
                    assert!(
                        p[*v] <= &p[u] + w,
                        "edge {u} → {v} of weight {w:?} in {out:?}"
                    );
                }
            }
            let decision = odd_zero_cycle(vars, &out, &p);
            assert_eq!(decision, odd_zero_cycle(vars, &out, &q), "graph {out:?}");
            if decision {
                odd += 1;
            } else {
                point += 1;
            }
        }
        assert!(
            negative > 0 && odd > 0 && point > 0,
            "{negative} {odd} {point}"
        );
    }

    #[test]
    fn bad_gor_augmented_has_a_potential_that_holds_on_every_edge() {
        // BAD-GOR of Cherkassky and Goldberg as Cassis et al. 2025 (arXiv 2502.11999, appendix)
        // give it, k = 64, with its nodes 1 to 2k + 1 at 0 to 2k: the graph on which the passes
        // of Goldberg and Radzik grow with the nodes (COMPLEXITY.md C24). Augmented as there,
        // with 5m random edges of one large weight and the labels permuted, from seed 1 as
        // `l01_38_presburger::stages::bad_gor` builds it.
        let k = 64usize;
        let n = 2 * k + 1;
        let mut edges: Vec<(usize, usize, i64)> = vec![(0, 1, -3 * k as i64), (0, k, -1)];
        edges.extend((1..k - 1).map(|i| (i, i + 1, 1)));
        edges.extend((1..=k).map(|i| (k, k + i, -1)));
        edges.extend((1..k).map(|i| (i, k, 2 * (k - 1 - i) as i64)));
        let heavy = n as i64 + 1 + edges.iter().map(|e| e.2.abs()).sum::<i64>();
        let mut state = 1u64;
        let mut below = |m: usize| (next(&mut state) % m as u64) as usize;
        for _ in 0..5 * edges.len() {
            let (a, b) = (below(n), below(n));
            if a != b {
                edges.push((a, b, heavy));
            }
        }
        let mut label: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            label.swap(i, below(i + 1));
        }
        let mut out: Vec<Vec<(usize, Int)>> = vec![Vec::new(); n];
        for (u, v, w) in edges {
            out[label[u]].push((label[v], Int::from(w)));
        }
        let p = potential(&out).expect("BAD-GOR has no negative cycle");
        assert!(bellman_ford_moore(&out).is_some());
        for (u, es) in out.iter().enumerate() {
            for (v, w) in es {
                assert!(p[*v] <= &p[u] + w, "edge {u} → {v} of weight {w:?}");
            }
        }
    }
}
