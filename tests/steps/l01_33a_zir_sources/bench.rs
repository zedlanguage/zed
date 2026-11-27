//! The benchmark of the map (DESIGN.md step L1.33a), run by `tools/run_tests.sh --bench` and
//! left out of its default run. Its other checks are made at a small size by
//! `sources::each_line_of_a_chain_has_one_sum_with_both_copies`.

use zed_tests::scaling;
use zedc::zir::lower::lower_debug;

use super::shared_chain;

/// Building the map, the parse of the text and the walk of its tree, is O(t + p log p) for t
/// parse tree nodes and p pairs of node and source, of order n log n: held to
/// [`scaling::check_n_log_n`]. At m lines a program has about 3m nodes, two of each line's
/// five terms with sites being copies, and about 9m pairs; m = 1000 and 8000 give some
/// 3 × 10^3 and 2.4 × 10^4 nodes, the testkit's two sizes in place of the step's three.
#[test]
fn building_the_map_scales() {
    let n = 1000;
    let lowered = scaling::inputs(n, |m| {
        let p = zedc::run::load(shared_chain(m).as_bytes()).unwrap();
        let (_, sited) = lower_debug(&p.term(), Some(p.sites())).unwrap();
        (p, sited)
    });
    scaling::check_n_log_n("building the map of n lines of shared sums", n, |m| {
        let (p, sited) = &lowered[&m];
        let map = p.source_map(&sited.sources);
        assert!(map.len() >= 5 * m, "{}", map.len());
    });
}
