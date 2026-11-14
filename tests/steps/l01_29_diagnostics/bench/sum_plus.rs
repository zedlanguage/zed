//! `sum` over `n` components, failing at the first `+`, at `n` and `8n` (`sum_plus.rs`).

use zed_tests::scaling;

use crate::sum_plus::{
    components_failing_at_the_first_plus, sum_failing_at_the_first_plus_rejected,
};

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
