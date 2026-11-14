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
    // TEST-bench-move-l0123, author P169: n 256 before, now 32768; 1x 0.20 s by `ns`, load 33.
    let (n, small, large) = (32768, pair_ring(32768), pair_ring(scaling::FACTOR * 32768));
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
    // TEST-bench-move-l0123, author P169: n 2048 before, now 65536; 1x 0.31 s by `ns`, load 36.
    let (n, (small_runs, large_runs)) = (65536, scaling::Meter::new().runs());
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
    // TEST-bench-move-l0123, author P169: n 128 before, now 40_000; 1x 0.47 s by `ns`, load 36.
    let n = 40_000;
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

/// `order_free` over many seeds: the correctness test runs one new seed each run, so a corpus
/// on which an answer depends on the queries before it is found only now and then (FAIL row
/// FAIL-judgments-query-order-seed was one such seed). Each test sweeps 50 seeds.
fn order_free_sweep(from: u64) {
    for seed in from..from + 50 {
        order_free(seed);
    }
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_0_to_49() {
    order_free_sweep(0);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_50_to_99() {
    order_free_sweep(50);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_100_to_149() {
    order_free_sweep(100);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_150_to_199() {
    order_free_sweep(150);
}
