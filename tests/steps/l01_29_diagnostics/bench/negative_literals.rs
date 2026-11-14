//! The check of `2n` negative literals rejected at their minus, at `n` and `8n`
//! (`negative_literals.rs`).

use zed_tests::scaling;

use crate::negative_literals::{negatives_rejected_at_their_minus, resolved_negatives};

#[test]
fn rejecting_negative_literals_at_their_minus_scales() {
    let n = 256;
    // The inputs are built before the timing.
    let units = scaling::inputs(n, resolved_negatives);
    scaling::on_a_thread(1 << 29, || {
        scaling::check_order(
            "rejecting n negative literals at a parameter and n compared with a class",
            n,
            1,
            |m| negatives_rejected_at_their_minus(&units[&m], m),
        );
    });
}
