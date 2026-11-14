//! The benchmarks of `exclusive_cases.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::exclusive_cases::*;
use zedc::store::interval::IntervalSet;

#[test]
fn a_match_of_m_cases_is_projected_in_n_log_n() {
    projects("a match of m cases", 690, cases, |m| {
        IntervalSet::of(0, 109 + m as i64)
    });
}

#[test]
fn a_match_of_m_cases_on_one_stage_of_a_chain_is_projected_in_n_log_n() {
    projects("a match of m cases on the middle stage", 460, middle, |m| {
        let h = (m / 2) as i64;
        IntervalSet::of(h, 4 * m as i64 + h + 10)
    });
}

#[test]
fn a_match_of_m_cases_each_on_its_own_stage_is_projected_in_n_log_n() {
    projects(
        "a match of m cases on their own stages",
        340,
        own_stage,
        |m| IntervalSet::of(0, 5 * m as i64 + 9),
    );
}
