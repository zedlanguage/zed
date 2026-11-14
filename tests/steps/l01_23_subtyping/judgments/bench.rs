//! The benchmarks of `judgments.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `judgments.rs`.

use super::*;

/// A ring of `n` definitions, each a morphism type into a pair of the next and `int`, decided
/// in time linear in `n`. Neither ring is decided before the check: a group makes its canonical
/// form on first use and keeps it, so the first run of each size makes it, and the check holds
/// those first runs to the limit, both cold. Deciding the smaller ring once before (as this test
/// did until GROUP-decide-bytes) left the first larger run alone to make its form, and the
/// first runs then compared 1,504,930 bytes with 17,071,066, 11.3 times, where cold against
/// cold they are 2,141,806 and 17,071,066, 8.0 times.
#[test]
fn deciding_a_group_scales() {
    let (n, small, large) = (256, pair_ring(256), pair_ring(scaling::FACTOR * 256));
    let run = |g: &Group| {
        Type::forget_emptiness();
        let types = g.instance(vec![]);
        assert!(types.iter().all(|t| !t.is_empty()));
    };
    scaling::check_order("deciding a ring of definitions", n, 1, |m| {
        run(if m == n { &small } else { &large })
    });
}

/// The canonical form of one component of `n` members, each its own class, is made in
/// O(n log n): each group is new, so no table holds its form.
#[test]
fn the_canonical_form_of_a_component_scales() {
    let (n, (small_runs, large_runs)) = (2048, scaling::Meter::new().runs());
    let pool = |m: usize, runs: usize| {
        std::sync::Mutex::new((0..runs).map(|_| marked_ring(m)).collect::<Vec<_>>())
    };
    let (small, large) = (pool(n, small_runs), pool(scaling::FACTOR * n, large_runs));
    scaling::check("the canonical form of a ring of definitions", n, |m| {
        let pool = if m == n { &small } else { &large };
        let g = pool
            .lock()
            .expect("the pool of groups")
            .pop()
            .expect("one group per run");
        let types = g.instance(vec![]);
        assert_eq!(types.len(), m);
    });
}

#[test]
fn a_nest_of_key_types_is_decided_in_one_search() {
    let n = 128;
    let nests = scaling::inputs(n, key_nest);
    scaling::check("the verdict of a nest of n key types", n, |m| {
        Type::forget_emptiness();
        let verdict = if m % 2 == 0 {
            Verdict::Empty
        } else {
            Verdict::Inhabited
        };
        assert_eq!(nests[&m].verdict(), verdict);
    });
}
