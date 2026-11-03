//! Duong's near-linear search for a potential (`zedc::store::negsssp`, item UTVPI-NEAR) against
//! Bellman–Ford–Moore on small random graphs, and its scaling alone.

use std::collections::VecDeque;

use zed_tests::instances::Rng;
use zed_tests::scaling;
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
fn holds(out: &Graph, p: &[Int]) -> bool {
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

/// 50,000 small graphs from `seed`: Duong's search finds a negative cycle exactly when the
/// reference does, and otherwise a potential that holds on every edge. Both answers occur.
fn against_the_reference(seed: u64) {
    let mut g = Rng::new(seed);
    let (mut negative, mut feasible) = (0, 0);
    for _ in 0..50_000 {
        let out = small(&mut g);
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
    assert!(negative > 1000 && feasible > 1000, "{negative} {feasible}");
}

// 300,000 graphs in six tests, so that each runs well within the time limit.
#[test]
fn small_graphs_1() {
    against_the_reference(1);
}

#[test]
fn small_graphs_2() {
    against_the_reference(2);
}

#[test]
fn small_graphs_3() {
    against_the_reference(3);
}

#[test]
fn small_graphs_4() {
    against_the_reference(4);
}

#[test]
fn small_graphs_5() {
    against_the_reference(5);
}

#[test]
fn small_graphs_6() {
    against_the_reference(6);
}

/// A graph of `n` nodes and `4n` random edges, weights -5 to 20, with no negative cycle: each
/// weight is raised to keep it at least the difference of a hidden potential of values 0 to
/// `n`, so that the scaling steps and the merges all have work to do.
fn feasible(n: usize, seed: u64) -> Graph {
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

#[test]
fn duong_scales_alone() {
    let (small, large) = (feasible(512, 1), feasible(scaling::FACTOR * 512, 1));
    for out in [&small, &large] {
        let p = potential_alone(out).expect("no negative cycle");
        assert!(holds(out, &p));
    }
    scaling::check("Duong's search, random graphs by n", 512, |n| {
        let out = if n == 512 { &small } else { &large };
        std::hint::black_box(potential_alone(out));
    });
}
