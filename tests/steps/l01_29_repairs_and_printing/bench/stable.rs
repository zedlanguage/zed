//! The printed types of a batch of `n` units, at `n` and `8n` (`stable.rs`).

use zed_tests::scaling;

use crate::stable::{batch, printed_types_stable_over};

/// The types printed by a batch of `n` units, each checked after the others, then checked again
/// and with a comment and a binding added, in work linear in the units. The units are built
/// before the timing.
#[test]
fn checking_printed_types_over_a_batch_scales() {
    let n = 30;
    let batches = scaling::inputs(n, batch);
    scaling::check_order("printed types over a batch of n units", n, 1, |m| {
        printed_types_stable_over(&batches[&m]);
    });
}
