//! The printed types of a batch of `n` units, at `n` and `8n` (`stable.rs`).

use zed_tests::scaling;

use crate::stable::{batch, printed_types_stable_over};

/// The types printed by a batch of `n` units, each checked after the others, then checked again
/// and with a comment and a binding added, in work linear in the units. At 777, the size from
/// which n log n stays under the limit (DESIGN sec:plan; SCALE-small-n-rest), with each batch
/// built only in the process that runs its size (`scaling::check_order_inputs`).
#[test]
fn checking_printed_types_over_a_batch_scales() {
    scaling::check_order_inputs(
        "printed types over a batch of n units",
        777,
        1,
        batch,
        |units| printed_types_stable_over(units),
    );
}
