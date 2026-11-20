//! The benchmarks of the strongly connected components, run by `tools/run_tests.sh --bench` and
//! left out of its default run. Their small instances are the correctness tests in `tests.rs`.

use std::collections::{BTreeMap, HashMap};

use super::{Search, Walk, components, on_cycle};
use crate::scaling;

mod units;

/// A graph of `n` nodes and `4n` edges, from node `v` to `3v + 1`, `5v + 2`, `v + 1` and
/// `v / 2`, wrapped modulo `n`: long cycles and many components of one node.
fn spread(n: usize) -> Vec<Vec<usize>> {
    (0..n)
        .map(|v| vec![(3 * v + 1) % n, (5 * v + 2) % n, (v + 1) % n, v / 2])
        .collect()
}

/// Small instances:
/// `components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order`.
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

/// The graph of [`spread`] with nodes labeled by numbers spread over `u64`, which the walk
/// numbers as it meets them, as [`crate::Walk`] lets a caller with no numbering do.
struct Spread<'g> {
    edges: &'g HashMap<u64, [u64; 4]>,
    number: HashMap<u64, usize>,
    label: Vec<u64>,
    count: usize,
}

impl Walk for Spread<'_> {
    type At = usize;

    fn next(&mut self, v: usize, k: &mut usize) -> Option<usize> {
        let w = *self.edges[&self.label[v]].get(*k)?;
        *k += 1;
        Some(*self.number.entry(w).or_insert_with(|| {
            self.label.push(w);
            self.label.len() - 1
        }))
    }

    fn found(&mut self, members: &mut [usize], _from: Option<usize>) {
        self.count += members.len();
    }
}

fn spread_label(v: usize) -> u64 {
    (v as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// Small instances: `a_search_over_nodes_numbered_as_met_finds_the_classes_of_mutual_reach`.
#[test]
fn a_search_over_nodes_numbered_as_met_takes_linear_time() {
    let n = 200_000;
    let built: BTreeMap<usize, HashMap<u64, [u64; 4]>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let edges = spread(m).into_iter().enumerate().map(|(v, out)| {
                (
                    spread_label(v),
                    <[usize; 4]>::try_from(out).unwrap().map(spread_label),
                )
            });
            (m, edges.collect())
        })
        .collect();
    scaling::check(
        "the components of a graph of n labeled nodes and 4n edges, numbered as met",
        n,
        |m| {
            let mut walk = Spread {
                edges: &built[&m],
                number: HashMap::from([(spread_label(0), 0)]),
                label: vec![spread_label(0)],
                count: 0,
            };
            Search::new().run(&mut walk, [0]);
            assert!(walk.count > 0 && walk.count <= m);
        },
    );
}

/// A graph of `n` nodes added in blocks of [`BLOCK`]: node `v` of the block starting at `b`
/// has edges to the next node of its block (the last to `b`, so each block is a cycle), to
/// `v / 2` and to `(3v + 1) mod (b + BLOCK)`, all below the end of its block, so no node gets
/// an edge to a later block.
fn blocks(n: usize) -> Vec<Vec<usize>> {
    (0..n)
        .map(|v| {
            let b = v - v % BLOCK;
            let end = (b + BLOCK).min(n);
            vec![
                if v + 1 < end { v + 1 } else { b },
                v / 2,
                (3 * v + 1) % end,
            ]
        })
        .collect()
}

/// The nodes a graph of [`blocks`] gains at a time. Any size well below the benchmark's `n`
/// serves; it is not tuned. What relies on it: the search runs `n / BLOCK` times (200 at
/// `n` = 200,000, 1600 at 8n), so a search that read the whole graph again at each run would
/// cost O(n² / BLOCK) and its ratio at 8n would be near 64, far past the limit, where the
/// search that reads only the new nodes stays near 8. The test's description string names the
/// same 1000.
const BLOCK: usize = 1000;

/// The edges of a graph as lists, numbered `0..n`, counting the nodes found.
struct Grown<'g> {
    edges: &'g [Vec<usize>],
    count: usize,
}

impl Walk for Grown<'_> {
    type At = usize;

    fn next(&mut self, v: usize, k: &mut usize) -> Option<usize> {
        let w = *self.edges[v].get(*k)?;
        *k += 1;
        Some(w)
    }

    fn found(&mut self, members: &mut [usize], _from: Option<usize>) {
        self.count += members.len();
    }
}

/// Small instances: `a_search_run_again_after_its_graph_grows_reads_only_the_new_nodes`. A
/// search from scratch after each block would read the whole graph again, O(n² / BLOCK).
#[test]
fn a_search_run_again_after_each_block_its_graph_grows_by_takes_linear_time() {
    let n = 200_000;
    let built: BTreeMap<usize, Vec<Vec<usize>>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, blocks(m)))
        .collect();
    scaling::check(
        "the components of a graph of n nodes grown in blocks of 1000, searched after each",
        n,
        |m| {
            let mut walk = Grown {
                edges: &built[&m],
                count: 0,
            };
            let mut search = Search::new();
            for b in (0..m).step_by(BLOCK) {
                search.run(&mut walk, b..(b + BLOCK).min(m));
            }
            assert_eq!(walk.count, m);
        },
    );
}
