//! The benchmarks of `refusal_cost.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `refusal_cost.rs`.

use super::*;

#[test]
fn the_verdict_of_the_x_tail_family_is_refused_in_its_size() {
    // TEST-bench-move-l0123, author P169: n 16 before, now 32; 1x 0.18 s by `ns`, load 52.
    // Power 2; 8x took 4.5 s, so 1x cannot reach 0.5 s inside 15 s.
    refusal_scales(
        "verdict of the x_tail family, n places",
        32,
        Refusal::Fork,
        false,
        x_tail,
    );
}

#[test]
fn the_subtype_verdict_of_the_x_tail_family_is_refused_in_its_size() {
    // TEST-bench-move-l0123, author P169: n 16 before, now 32; 1x 0.17 s by `ns`, load 52.
    // Power 2; 8x took 4.0 s, so 1x cannot reach 0.5 s inside 15 s.
    refusal_scales(
        "subtype_verdict of the x_tail family, n places",
        32,
        Refusal::Fork,
        true,
        x_tail,
    );
}

#[test]
fn the_verdict_of_random_3_cnf_is_refused_in_its_size() {
    // TEST-bench-move-l0123, author P169: n 8 before, now 16; 1x 0.10 s by `ns`, load 52.
    // Power 2; 8x took 4.6 s, so 1x cannot reach 0.5 s inside 15 s. Seed 2 is refused at 16
    // and 128 alike (the assert of `refusal_scales`).
    refusal_scales(
        "verdict of random 3-CNF, n bits",
        16,
        Refusal::SharedCells(0),
        false,
        |n, _| r3(n, 2),
    );
}

#[test]
fn the_subtype_verdict_of_random_3_cnf_is_refused_in_its_size() {
    // TEST-bench-move-l0123, author P169: n 8 before, now 16; 1x 0.081 s by `ns`, load 52.
    // Power 2; 8x took 4.5 s, so 1x cannot reach 0.5 s inside 15 s. Seed 2 is refused at 16
    // and 128 alike (the assert of `refusal_scales`).
    refusal_scales(
        "subtype_verdict of random 3-CNF, n bits",
        16,
        Refusal::SharedCells(0),
        true,
        |n, _| r3(n, 2),
    );
}
