//! The scaling check of `refold.rs`. Each program is loaded before the timing.

use zed_tests::scaling;
use zedc::run::load;

use crate::refold::nots;

/// Evaluating a term whose parts mixing made literals costs O(1) more per term built (plan
/// row STAGE-refold-mixed): `n` nested `!`s around `d && b` fold one by one, each from a
/// literal part, and `n` nested `!`s around `b && d` are each built once, never evaluated.
#[test]
fn nots_around_a_mixed_term_stage_in_linear_time() {
    let n = 100;
    for inner in ["d && b", "b && d"] {
        let programs = scaling::inputs(n, |k| load(nots(k, inner).as_bytes()).unwrap());
        let what = format!("staging `main` with n nested `!`s around `{inner}`");
        scaling::check(&what, n, |k| {
            std::hint::black_box(programs[&k].stage());
        });
    }
}
