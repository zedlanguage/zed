//! The benchmarks of the strongly connected components, run by `tools/run_tests.sh --bench` and
//! left out of its default run. Their small instances are the correctness tests in `tests.rs`.

use std::collections::BTreeMap;

use super::{components, on_cycle};
use crate::scaling;

/// A graph of `n` nodes and `4n` edges, from node `v` to `3v + 1`, `5v + 2`, `v + 1` and
/// `v / 2`, wrapped modulo `n`: long cycles and many components of one node.
fn spread(n: usize) -> Vec<Vec<usize>> {
    (0..n)
        .map(|v| vec![(3 * v + 1) % n, (5 * v + 2) % n, (v + 1) % n, v / 2])
        .collect()
}

/// Small instances: `components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order`.
#[test]
fn the_components_of_a_large_graph_take_linear_time() {
    let n = 200_000;
    let built: BTreeMap<usize, Vec<Vec<usize>>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, spread(m)))
        .collect();
    scaling::check(
        "the components of a graph of n nodes and 4n edges",
        n,
        |m| {
            let comp = components(&built[&m], |&w| w);
            assert_eq!(comp.len(), m);
        },
    );
}

/// Small instances: `a_node_is_on_a_cycle_exactly_when_it_reaches_itself`.
#[test]
fn the_cycles_of_a_long_chain_take_linear_time() {
    let n = 200_000;
    let built: BTreeMap<usize, Vec<Vec<usize>>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            (
                m,
                (0..m)
                    .map(|v| vec![v + 1].into_iter().filter(|&w| w < m).collect())
                    .collect(),
            )
        })
        .collect();
    scaling::check("the nodes on a cycle of a chain of n nodes", n, |m| {
        assert!(on_cycle(&built[&m]).iter().all(|&c| !c));
    });
}
