//! The benchmark of [`Map`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). Besides the ratio it checks that each key inserted is found and
//! that a copy with one value changed differs from the map at that key alone; the correctness
//! tests `random_changes_agree_with_the_model_and_keep_old_versions` and
//! `shared_subtrees_are_passed_over` in `tests.rs` check both at small sizes.

use super::tests::{Draw, M};
use std::collections::HashMap;

#[test]
fn insertion_lookup_and_difference_scale_as_n_log_n() {
    // n keys inserted in a scattered order, each looked up, and n differences between the map
    // and a copy with one key changed, each of which reads only the changed path: O(n log n).
    let inputs: HashMap<usize, Vec<u64>> = [100_000, 800_000]
        .into_iter()
        .map(|n| {
            let mut d = Draw(n as u64);
            (n, (0..n).map(|_| d.next()).collect())
        })
        .collect();
    crate::scaling::check_order(
        "a B-tree: n insertions, n lookups and n one-change differences",
        100_000,
        1,
        |n| {
            let keys = &inputs[&n];
            let mut m = M::default();
            for &k in keys {
                m.insert(k, k);
            }
            for k in keys {
                assert_eq!(m.get(k), Some(k));
            }
            for &k in keys {
                let mut c = m.clone();
                c.insert(k, 0);
                assert_eq!(c.diff(&m).count(), usize::from(k != 0));
            }
        },
    );
}
