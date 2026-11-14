//! The benchmarks of `value`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). What the table benchmark checks besides the ratio, that each
//! pair enters once, that the half taken out are entered again and the rest are found, is
//! checked at small sizes by `the_pairs_of_one_comparison_are_entered_taken_out_and_met_again`
//! in the tests of `value.rs`; the deep value is digested at 12 and 64 levels by
//! `a_deep_shared_value_is_digested_once_per_sequence`.

use super::tests::{drawn_pairs, shared};
use super::*;

#[test]
fn the_table_of_pairs_scales() {
    // n pairs entered, every other one taken out again, as a walk that ends at a difference
    // inside another comparison does, and all n met again. Each step is O(1) on average:
    // the slots are at most half full and the hash spreads ids drawn in order.
    let inputs: HashMap<usize, Vec<Pair>> = [1_280_000, 10_240_000]
        .into_iter()
        .map(|n| (n, drawn_pairs(n)))
        .collect();
    crate::scaling::check_order(
        "the table of pairs: n entered, n/2 taken out, n met again",
        1_280_000,
        1,
        |n| {
            let pairs = &inputs[&n];
            let mut table = ReadSet::new();
            for &p in pairs {
                assert!(table.insert(p));
            }
            for &p in pairs.iter().step_by(2) {
                table.remove(p);
            }
            let again = pairs.iter().filter(|&&p| table.insert(p)).count();
            assert_eq!(again, n.div_ceil(2));
            table.clear();
        },
    );
}

/// A value 200,000 levels deep, each level holding the one below twice, is digested: the walk
/// keeps its own stack, so the depth is not limited by the thread's (author P178: an unusual
/// depth is a benchmark).
#[test]
fn a_value_200000_levels_deep_is_digested() {
    let deep = shared(200_000);
    let _ = digest(&deep);
}
