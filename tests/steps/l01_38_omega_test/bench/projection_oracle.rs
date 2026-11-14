//! The large fixed-seed suite of `projection_oracle.rs` (TEST-corr-slow-l0138), run by
//! `tools/run_tests.sh --bench`.

use crate::projection_oracle::*;

/// `projection_oracle::each_answer_of_a_random_unit_through_projected_callees_is_the_interpreters_on_a_box`
/// as first written, 6.7 s (2026-11-14, load 25): the 60 programs of the seeds from `SEED` on.
#[test]
fn each_answer_of_60_random_units_through_projected_callees_is_the_interpreters_on_a_box() {
    let (decided, refused) = random_units_are_the_interpreters(SEED, 60);
    // Most questions are decided, so the answers are compared, not only the refusals.
    assert!(
        decided >= 1000,
        "{decided} answers decided, {refused} refused"
    );
}
