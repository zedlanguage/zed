//! The benchmarks of `rec_order.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `rec_order.rs`.

use super::*;

#[test]
fn the_members_of_a_group_are_ordered_in_n_log_n() {
    // Input Θ(n): a group of n definitions. Its n members are built, sorted and their 1-tuples
    // united; each comparison of two members is decided by their keys, so the order costs
    // O(n log n) comparisons of constant cost, and the whole O(n log n). It runs on the default
    // stack of a test thread.
    // TEST-bench-move-l0123, author P169: n 512 before, now 8192; 1x 0.44 s by `ns`, load 39.
    let tag = AtomicUsize::new(0);
    scaling::check(
        "a group's members, built, sorted and united, by n",
        8192,
        |n| {
            let cell = format!("scale{}", tag.fetch_add(1, Relaxed));
            let ts = periods(&cell, n, 0);
            let sorted: BTreeSet<&Type> = ts.iter().collect();
            assert_eq!(sorted.len(), n);
            let u = Type::union_all(ts.iter().map(|t| Type::tuple(vec![t.clone()])));
            assert!(!u.is_empty());
        },
    );
}
