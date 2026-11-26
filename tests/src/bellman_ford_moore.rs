//! The reference searches for a potential that the negative-cycle searches are tested against,
//! shared by the tests of `zedc-solvers` and `zedc-presburger` (through `#[path]`) and the step
//! tests.

use std::ops::Add;

use zed_graph::{Order, Worklist};
use zedc_int::int::Int;

/// Bellman–Ford–Moore with a first-in first-out queue, from a source joined to each node by an
/// edge of weight 0: the potentials, or `None` on a negative cycle, which it has found when a
/// node is taken from the queue for the n + 1st time. `out[u]` holds the edges `(v, w)` from
/// `u`. O(n·m) for n nodes and m edges. Bellman–Ford–Moore: R. Bellman, Quart. Appl. Math.
/// 16(1), 1958, doi:10.1090/qam/102435, with Ford 1956 and Moore 1959; the full comment is at
/// the head of zed-graph `worklist.rs`.
pub fn bellman_ford_moore(out: &[Vec<(usize, Int)>]) -> Option<Vec<Int>> {
    let n = out.len();
    let mut d = vec![Int::ZERO; n];
    let mut taken = vec![0usize; n];
    let mut queue = Worklist::all(n, Order::Fifo);
    while let Some(u) = queue.pop() {
        taken[u] += 1;
        if taken[u] > n {
            return None;
        }
        for (v, w) in &out[u] {
            let to = &d[u] + w;
            if to < d[*v] {
                d[*v] = to;
                queue.push(*v);
            }
        }
    }
    Some(d)
}

/// Bellman–Ford in its plain form, from a source joined to each node by an edge of weight 0:
/// `n` passes over every edge in order; the labels, each the least weight of a walk ending at
/// its node, or `None` when a label still falls in pass `n`, which shows a negative cycle.
/// Proof, for `n` nodes: (a) a pass with no change leaves `d[v] <= d[u] + w` on every edge;
/// summed round a cycle this says its weight is at least 0, so a pass with no change means no
/// negative cycle, and each label, the weight of some walk, is then the least. (b) After pass
/// `r` each `d[v]` is at most the least weight of a walk of at most `r` edges ending at `v`;
/// with no negative cycle the least walk weight is reached by a simple path, of at most `n - 1`
/// edges, so pass `n` changes nothing. So `None` exactly on a negative cycle. O(n·m). The
/// plain form, not the queue of [`bellman_ford_moore`], so that the two oracles share no
/// code; it is easy to check by eye. Generic over the weight, for the tests that build graphs
/// of machine integers.
pub fn bellman_ford<W>(out: &[Vec<(usize, W)>]) -> Option<Vec<W>>
where
    W: Clone + Ord + From<i32>,
    for<'a> &'a W: Add<&'a W, Output = W>,
{
    let n = out.len();
    let mut d = vec![W::from(0); n];
    for _ in 0..n {
        let mut fell = false;
        for (u, edges) in out.iter().enumerate() {
            for (v, w) in edges {
                let to = &d[u] + w;
                if to < d[*v] {
                    d[*v] = to;
                    fell = true;
                }
            }
        }
        if !fell {
            return Some(d);
        }
    }
    (n == 0).then_some(d)
}

/// Whether `p` is a potential of `out`: `p(v) <= p(u) + w` on every edge `u → (v, w)`.
pub fn holds<W>(out: &[Vec<(usize, W)>], p: &[W]) -> bool
where
    W: Ord,
    for<'a> &'a W: Add<&'a W, Output = W>,
{
    out.iter()
        .enumerate()
        .all(|(u, edges)| edges.iter().all(|(v, w)| p[*v] <= &p[u] + w))
}

/// Whether the graph of `n` nodes and the edges `(u, v, w)` has a negative cycle, by
/// [`bellman_ford`].
pub fn negative_cycle<W>(n: usize, edges: &[(usize, usize, W)]) -> bool
where
    W: Clone + Ord + From<i32>,
    for<'a> &'a W: Add<&'a W, Output = W>,
{
    let mut out = vec![Vec::new(); n];
    for (u, v, w) in edges {
        out[*u].push((*v, w.clone()));
    }
    bellman_ford(&out).is_none()
}
