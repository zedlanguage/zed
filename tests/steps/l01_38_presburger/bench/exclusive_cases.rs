//! The benchmarks of `exclusive_cases.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::exclusive_cases::*;

#[test]
fn a_match_of_m_cases_is_projected_in_n_log_n() {
    projects("a match of m cases", 690, cases, cases_z);
}

#[test]
fn a_match_of_m_cases_on_one_stage_of_a_chain_is_projected_in_n_log_n() {
    projects("a match of m cases on the middle stage", 460, middle, middle_z);
}

#[test]
fn a_match_of_m_cases_each_on_its_own_stage_is_projected_in_n_log_n() {
    projects(
        "a match of m cases on their own stages",
        340,
        own_stage,
        own_stage_z,
    );
}
