//! The benchmarks of `listing.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `listing.rs`.

use super::*;

/// Takes the first `k` values of `t`, which has at least `k`.
fn take(t: &Type, k: usize) {
    assert_eq!(t.each_value().expect("finite").take(k).count(), k);
}

#[test]
fn finiteness_scales_with_the_types_not_the_values() {
    // Each type is visited once, on an explicit stack: one with no visited set takes `2^d`
    // steps.
    // TEST-bench-move-l0123, author P169: depth 500 before, now 64_000; 1x 0.26 s by `ns`,
    // load 36. The listing of a square of literals, checked here before, is
    // `listing_a_square_of_literals_scales_with_its_values`.
    let d = 64_000;
    let built: std::collections::HashMap<usize, Type> = scaling::inputs(d, doubling);
    scaling::check_order("the finite test on doubling types, by depth", d, 1, |d| {
        assert!(built[&d].finite());
    });
}

#[test]
fn listing_a_square_of_literals_scales_with_its_values() {
    // Split from `finiteness_scales_with_the_types_not_the_values` (TEST-bench-move-l0123,
    // author P169): n 100 before, now 128; 1x 0.078 s by `ns`, load 33.
    let n = 128;
    let squares = scaling::inputs(n, |n| {
        let s = Type::union_all((0..n).map(lit));
        Type::tuple(vec![s.clone(), s])
    });
    // The square of `n` literals has `n²` values: listing them is of order `n²`.
    scaling::check_order("listing a square of literals, by n", n, 2, |n| {
        assert_eq!(squares[&n].each_value().map(|v| v.count()), Some(n * n));
    });
}

#[test]
fn taking_k_values_costs_k_times_the_depth() {
    // Each value of every type is made once and kept for the pairs that read it, so taking
    // `k` values of `doubling(d)` makes about `k` values at each depth; a value is checked
    // against its row without walking the parts the types below it made.
    // TEST-bench-move-l0123, author P169: k 500 before, now 2000; 1x 0.40 s by `ns`, load
    // 33. The check by depth is `taking_k_values_costs_k_times_the_depth_by_depth`.
    let t = doubling(48);
    scaling::check(
        "taking the first k values of doubling(48), by k",
        2000,
        |k| take(&t, k),
    );
}

#[test]
fn taking_k_values_costs_k_times_the_depth_by_depth() {
    // Split from `taking_k_values_costs_k_times_the_depth` (TEST-bench-move-l0123, author
    // P169). Left at its old size, depth 12, as a finding (TEST-bench-move-l0123): the ratio
    // grows with the depth, so the cost is not linear in it. Instructions at d and 8d, load
    // 27 to 40: d 12, 49444361 and 488534612, 9.880 (bytes 9.38); d 48, 232411461 and
    // 2337583030, 10.058 (bytes 8.30); d 96, 488539406 and 5640883776, 11.546 (bytes 8.15),
    // over the limit 10.5; d 300, 1761426468 and 30524334961, 17.329 (bytes 8.04). The 1x at
    // depth 12 took 10.5 ms by `ns`. The bytes ratio stays near 8: the growth is in the
    // instructions, not in the memory allocated. Not profiled: perf cannot open events here.
    let built = scaling::inputs(12, doubling);
    scaling::check(
        "taking the first 500 values of doubling(d), by d",
        12,
        |d| take(&built[&d], 500),
    );
}

#[test]
fn a_tuple_is_found_tried_in_the_time_of_its_length() {
    // Each tuple tried is looked up by its components' numbers, so its depth is not read
    // again at each level; one compared by its values cost the depth at each of the `d`
    // levels, order `d²` per value.
    // TEST-bench-move-l0123, author P169: k 500 before, now 4000; 1x 0.61 s by `ns`, load
    // 36. The check by depth is
    // `a_tuple_is_found_tried_in_the_time_of_its_length_by_depth`.
    let t = doubling_two_boxes(48);
    scaling::check(
        "taking the first k values of a type of two boxes at each of 48 depths, by k",
        4000,
        |k| take(&t, k),
    );
}

#[test]
fn a_tuple_is_found_tried_in_the_time_of_its_length_by_depth() {
    // Split from `a_tuple_is_found_tried_in_the_time_of_its_length` (TEST-bench-move-l0123,
    // author P169): depth 12 before, now 200; 1x 0.33 s by `ns`, load 35.
    let built = scaling::inputs(200, doubling_two_boxes);
    scaling::check(
        "taking the first 500 values of a type of two boxes at each depth, by depth",
        200,
        |d| take(&built[&d], 500),
    );
}

/// Each component of a wide tuple is made on demand, and the maker of the tuple waits for
/// each in turn; the scan of the components resumes where it waited (PERF-tuple-print), so
/// the boxes are entered and left with each component checked a bounded number of times.
#[test]
fn listing_one_wide_tuple_scales() {
    // TEST-bench-move-l0123, author P169: n 400 before, now 40_000; 1x 0.23 s by `ns`, load 35.
    let n = 40_000;
    let built = scaling::inputs(n, wide);
    scaling::check("listing the one value of a tuple of n literals", n, |m| {
        let values = built[&m].values_listed().unwrap();
        assert_eq!(values.len(), 1);
    });
}
