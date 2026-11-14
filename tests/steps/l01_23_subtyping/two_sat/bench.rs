//! The benchmarks of `two_sat.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `two_sat.rs`.

use super::*;

#[test]
fn a_chain_is_decided_in_the_size_of_its_type() {
    scales("chain");
}

#[test]
fn an_open_chain_is_decided_in_the_size_of_its_type() {
    scales("chainsat");
}

#[test]
fn a_parity_cycle_is_decided_in_the_size_of_its_type() {
    scales("xorcycle");
}

/// The parity cycle at 11 and 88 variables, within 24 times: linear in the clauses, a smaller
/// measure than the type, whose size grows 64 times. The search before item T6-2sat costs about
/// `vars^3` here, which is `n^1.5` in the type's size: 22 times at 8 times the size, inside the
/// limit of [`scales`], so only this test tells it from the 2-CNF reading (it allocated 446
/// times the bytes from 11 to 88 variables).
#[test]
fn a_parity_cycle_is_decided_in_time_linear_in_its_clauses() {
    let types = scaling::inputs(11, |m| instance("xorcycle", m));
    scaling::check("2-CNF xorcycle, by variables", 11, |m| {
        decide("xorcycle", m, &types[&m]);
    });
}
