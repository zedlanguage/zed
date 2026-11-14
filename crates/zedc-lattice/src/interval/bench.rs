//! The benchmark of `interval`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P178: a test that needs an unusual size is a benchmark).
//! It runs the set operations on random sets of up to 400 raw pieces in `-1500..=1500`, whose
//! trees are deep; `set_operations_agree_with_the_vec_version_on_random_sets` in the tests of
//! `interval.rs` runs the same checks on sets of up to 6 and 60 pieces, and
//! `lost_to_gives_the_members_minus_gives` runs `lost_to` on a few sets of 400 pieces.

use super::tests::{Rng, operations_agree};

/// meet, join, minus, complement_in and is_subset on 40 pairs of random sets of up to 400 raw
/// pieces with ends in `-1500..=1500`, against the Vec version built from members.
#[test]
fn set_operations_agree_on_large_random_sets() {
    let seed = crate::seed::seed("set_operations_agree_on_large_random_sets");
    operations_agree(&mut Rng(seed | 1), 40, 400, 1500);
}
