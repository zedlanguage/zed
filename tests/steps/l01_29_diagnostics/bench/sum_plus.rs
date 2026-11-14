//! `sum` over `n` components, the first `_`, at `n` and `8n` (`sum_plus.rs`).

use zed_tests::scaling;

use crate::sum_plus::{sum_over_untracked_components_rejected, untracked_components};

#[test]
fn checking_sum_over_untracked_components_scales() {
    let n = 400;
    let inputs = scaling::inputs(n, untracked_components);
    scaling::check("checking `sum` of n components, the first `_`", n, |k| {
        sum_over_untracked_components_rejected(&inputs[&k]);
    });
}
