//! `sum` over `n` components, failing at the first `+`, at `n` and `8n` (`sum_plus.rs`).

use zed_tests::scaling;

use crate::sum_plus::{
    components_failing_at_the_first_plus, components_failing_at_the_last_plus,
    sum_failing_at_the_first_plus_rejected, sum_failing_at_the_last_plus_rejected,
};

/// The running total's note (row MSG-sum-running-total-note) costs O(1) at the refused `+`,
/// with no walk back into the `n` components already added.
#[test]
fn checking_sum_failing_at_the_last_plus_scales() {
    let n = 2000;
    let inputs = scaling::inputs(n, components_failing_at_the_last_plus);
    scaling::check(
        "checking `sum` of n components, failing at the last `+`",
        n,
        |k| {
            sum_failing_at_the_last_plus_rejected(&inputs[&k]);
        },
    );
}

#[test]
fn checking_sum_failing_at_the_first_plus_scales() {
    let n = 7400;
    let inputs = scaling::inputs(n, components_failing_at_the_first_plus);
    scaling::check(
        "checking `sum` of n components, failing at the first `+`",
        n,
        |k| {
            sum_failing_at_the_first_plus_rejected(&inputs[&k]);
        },
    );
}
