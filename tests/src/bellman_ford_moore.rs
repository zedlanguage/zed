//! The reference search for a potential that the negative-cycle searches are tested against,
//! shared by the tests of `zedc-solvers` (through `#[path]`) and the step tests.

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
