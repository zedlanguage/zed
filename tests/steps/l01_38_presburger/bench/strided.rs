//! The benchmarks of `strided.rs` (row PERF-exact-strided-unlisted), run by
//! `tools/run_tests.sh --bench`.

use crate::strided::*;
use zed_tests::scaling;

/// The hub of [`hub`] at box bounds 125,000 and 1,000,000, at modulus 2: the work is of order
/// 1 in the bound (power 0), since the set of `w` is one class within one range and no value
/// of it needs listing.
#[test]
fn a_hub_held_to_a_class_scales_with_the_box_bound() {
    scaling::check_order(
        "the exact projection of a hub held to a class, by the box bound",
        125_000,
        0,
        |r| check_hub(r as i64, 2),
    );
}

/// The hub of [`hub`] boxed with no value listed (`project_each_boxed_classed`, the call of
/// `preimage::boxed_projections`), at box bounds 125,000 and 1,000,000, at modulus 2: the one
/// class of `w` fixed, its range from n to 8n, the work of order 1 in the bound (power 0).
/// Negative control: `project_each_boxed`, which lists each multiple, O(r).
#[test]
fn a_boxed_class_is_not_listed_scales() {
    scaling::check_order(
        "the boxed projection of a hub held to a class, by the box bound",
        125_000,
        0,
        |r| check_boxed_hub(r as i64, 2),
    );
}
