//! The benchmark of `values::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness tests that keep a small instance of
//! what it checks besides the ratio are `removals_run_along_a_chain_in_any_order` and
//! `values_in_the_gaps_of_one_form_are_removed`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

/// Both families at `n` and `8n`: O(r log r) in the `r` ranges, a removal at a time along
/// the chain and many gaps on one form.
#[test]
fn removals_scale() {
    scaling::check_order("removals by the values of each form", 20_000, 1, |n| {
        let mut ors = chain(n);
        assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
        let mut ors = wide(i128::try_from(n).expect("a size fits"));
        assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
    });
}
