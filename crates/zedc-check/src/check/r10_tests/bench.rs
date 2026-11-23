//! The scaling tests of `check::r10_tests` (author P178), run by `tools/run_tests.sh --bench` as
//! pieces of their own and left out of its default run. They were correctness tests, so they ran
//! in the zedc_check unit piece, which stopped at its 20 s limit
//! (FAIL-zedc-check-unit-piece-past-20s). Timed alone with tools/time_tests.sh on Colab VM std1
//! (2 cores, load 4.3, 2026-11-23), `r10_chain2_siblings_wide_skip_set_scale` ran past its limit
//! of 20 s (rc=124, 43.1 s).
//! The correctness tests that keep what these check at small sizes are
//! `r10_generalize_runs_against_a_wide_skip_set` and `r10_chain2_siblings_name_as_e_does`.

use super::*;

/// Step 1 of the closed-sibling repair: `generalize` names each internal run of a forward in
/// one step against the signature's skip set. Reading the whole skip set at each run made n
/// runs against n skipped names cost O(n^2); the set is now sorted once per signature.
#[test]
fn r10_generalize_runs_against_a_wide_skip_set_scale() {
    let inputs = crate::scaling::inputs(400, many_runs_wide_skip_src);
    crate::scaling::check(
        "generalize naming n internal runs against n skipped names",
        400,
        |n| {
            let (d, _) = run_with_cfg(&inputs[&n], R10Config::default());
            assert!(d.errors.is_empty(), "errors {:?}", d.errors);
        },
    );
}

/// Step 4 of the closed-sibling repair: naming n sibling forwards' runs apart against a skip
/// set of n names cuts each run only where it meets a name given before, so the whole costs
/// O(n log n), not one name at a time per run.
#[test]
fn r10_chain2_siblings_wide_skip_set_scale() {
    let inputs = crate::scaling::inputs(200, chain2_siblings_src);
    crate::scaling::check(
        "finishing n sibling chain-2 forwards against n skipped names",
        200,
        |n| {
            let (d, _) = run_with_cfg(&inputs[&n], R10Config::default());
            assert!(d.errors.is_empty(), "errors {:?}", d.errors);
        },
    );
}
