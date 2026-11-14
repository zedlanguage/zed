//! `zedc test` on `n` warnings and on a batch of `n` units, at `n` and `8n`
//! (`widen_test.rs`).

use zed_tests::scaling;

use crate::widen_test::{
    a_batch_of_halves, a_batch_of_halves_printed, a_unit_of_warnings, many_warnings_printed,
};

/// `zedc test` on a unit of `n` warnings, each written once: the run, compilation and
/// printing together, is within n log n. The files are written before the timing.
#[test]
fn printing_many_warnings_scales() {
    let n = 2600;
    let files = scaling::inputs(n, a_unit_of_warnings);
    scaling::check("zedc test on a unit of n warnings", n, |m| {
        many_warnings_printed(&files[&m], m);
    });
}

/// `zedc test` on a batch of `n` units, each with its own side, half rejected and half
/// repaired: each rejected unit prints its rejection alone and each repaired one its notice,
/// in work linear in the units. The files are written before the timing.
#[test]
fn a_batch_of_rejected_and_repaired_units_scales() {
    let n = 240;
    let batches = scaling::inputs(n, a_batch_of_halves);
    scaling::check_order("zedc test on a batch of n units", n, 1, |m| {
        a_batch_of_halves_printed(&batches[&m], m);
    });
}
