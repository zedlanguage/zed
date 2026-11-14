//! The benchmarks of `refusal_cost.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `refusal_cost.rs`.

use super::*;

#[test]
fn the_verdict_of_the_x_tail_family_is_refused_in_its_size() {
    refusal_scales(
        "verdict of the x_tail family, n places",
        16,
        Refusal::Fork,
        false,
        x_tail,
    );
}

#[test]
fn the_subtype_verdict_of_the_x_tail_family_is_refused_in_its_size() {
    refusal_scales(
        "subtype_verdict of the x_tail family, n places",
        16,
        Refusal::Fork,
        true,
        x_tail,
    );
}

#[test]
fn the_verdict_of_random_3_cnf_is_refused_in_its_size() {
    refusal_scales(
        "verdict of random 3-CNF, n bits",
        8,
        Refusal::SharedCells(0),
        false,
        |n, _| r3(n, 2),
    );
}

#[test]
fn the_subtype_verdict_of_random_3_cnf_is_refused_in_its_size() {
    refusal_scales(
        "subtype_verdict of random 3-CNF, n bits",
        8,
        Refusal::SharedCells(0),
        true,
        |n, _| r3(n, 2),
    );
}
