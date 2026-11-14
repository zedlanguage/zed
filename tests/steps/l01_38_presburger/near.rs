//! Duong's near-linear search for a potential (`zedc::store::negsssp`, item UTVPI-NEAR) against
//! Bellman–Ford–Moore on small random graphs, and its scaling alone.

use std::collections::VecDeque;

use zed_tests::instances::Rng;
use zedc::store::int::Int;
use zedc::store::negsssp::potential_alone;

type Graph = Vec<Vec<(usize, Int)>>;

/// The reference: Bellman–Ford–Moore with a first-in first-out queue, from a source joined to
/// each node by an edge of weight 0; a node taken from the queue for the n + 1st time shows a
/// negative cycle.
fn bellman_ford_moore(out: &Graph) -> Option<Vec<Int>> {
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

/// Whether `p` holds on every edge of `out`.
pub(super) fn holds(out: &Graph, p: &[Int]) -> bool {
    out.iter()
        .enumerate()
        .all(|(u, edges)| edges.iter().all(|(v, w)| p[*v] <= &p[u] + w))
}

/// A graph of 1 to 12 nodes and up to three edges per node, self loops among them, weights
/// -8 to 12.
fn small(g: &mut Rng) -> Graph {
    let n = 1 + g.below(12);
    let mut out: Graph = vec![Vec::new(); n];
    for _ in 0..g.below(3 * n + 1) {
        let (u, v) = (g.below(n), g.below(n));
        out[u].push((v, Int::from(g.below(21) as i64 - 8)));
    }
    out
}

/// `count` small graphs from `g`: Duong's search finds a negative cycle exactly when the
/// reference does, and otherwise a potential that holds on every edge. The counts of graphs
/// with a negative cycle and with a potential.
pub(super) fn against_the_reference(g: &mut Rng, count: usize) -> (usize, usize) {
    let (mut negative, mut feasible) = (0, 0);
    for _ in 0..count {
        let out = small(g);
        let found = potential_alone(&out);
        assert_eq!(
            found.is_some(),
            bellman_ford_moore(&out).is_some(),
            "graph {out:?}"
        );
        match found {
            Some(p) => {
                assert!(holds(&out, &p), "potential {p:?} of graph {out:?}");
                feasible += 1;
            }
            None => negative += 1,
        }
    }
    (negative, feasible)
}

/// 10,000 small graphs of a new seed each run against the reference; both answers occur more
/// than 3000 times (about 4400 and 5600 on 2026-11-14). The 300,000 graphs of seeds 1 to 6
/// (about 1.5 s per seed at load 25) are in `bench::near`.
#[test]
fn small_graphs_match_the_reference() {
    let (mut g, seed) = Rng::fresh("near small graphs");
    let (negative, feasible) = against_the_reference(&mut g, 10_000);
    assert!(
        negative > 3000 && feasible > 3000,
        "seed {seed}: {negative} with a negative cycle, {feasible} with a potential"
    );
}

/// The graphs at the edges of what `small` draws, and below it: no nodes; one node with no
/// edge, and with a self loop of weight -1, 0 and 1 (a negative loop is a negative cycle); two
/// nodes whose cycle weighs -1, 0 and 1.
#[test]
fn the_empty_graph_and_single_loops_are_answered() {
    let w = Int::from;
    let cases: Vec<(Graph, bool)> = vec![
        (vec![], true),
        (vec![vec![]], true),
        (vec![vec![(0, w(-1))]], false),
        (vec![vec![(0, w(0))]], true),
        (vec![vec![(0, w(1))]], true),
        (vec![vec![(1, w(3))], vec![(0, w(-4))]], false),
        (vec![vec![(1, w(3))], vec![(0, w(-3))]], true),
        (vec![vec![(1, w(3))], vec![(0, w(-2))]], true),
    ];
    for (out, has) in cases {
        let found = potential_alone(&out);
        assert_eq!(
            bellman_ford_moore(&out).is_some(),
            has,
            "reference on {out:?}"
        );
        assert_eq!(found.is_some(), has, "graph {out:?}");
        if let Some(p) = found {
            assert_eq!(p.len(), out.len(), "graph {out:?}");
            assert!(holds(&out, &p), "potential {p:?} of graph {out:?}");
        }
    }
}

/// A graph of `n` nodes and `4n` random edges, weights -5 to 20, with no negative cycle: each
/// weight is raised to keep it at least the difference of a hidden potential of values 0 to
/// `n`, so that the scaling steps and the merges all have work to do.
pub(super) fn feasible(n: usize, seed: u64) -> Graph {
    let mut g = Rng::new(seed);
    let hidden: Vec<i64> = (0..n).map(|_| g.below(n + 1) as i64).collect();
    let mut out: Graph = vec![Vec::new(); n];
    for _ in 0..4 * n {
        let (u, v) = (g.below(n), g.below(n));
        let w = (g.below(26) as i64 - 5).max(hidden[v] - hidden[u]);
        out[u].push((v, Int::from(w)));
    }
    out
}
