//! The benchmarks of `admission_sweep.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `admission_sweep.rs`.

use super::*;

/// The admission of a group of n definitions costs time linear in n.
/// TEST-bench-move-l0123, author P169: n was 256, now 33_000; 1x 0.30 s at load 25.
#[test]
fn admitting_a_group_scales() {
    let n = 33_000;
    let groups = scaling::inputs(n, ring);
    scaling::check("admitting a ring group of n definitions", n, |m| {
        Group::new(groups[&m].clone()).expect("a ring group is accepted");
    });
}

/// The evaluator on a group of three definitions costs time linear in the size of the bodies.
/// TEST-bench-move-l0123, author P169: n was 1024, now 250_000; 1x 0.28 s at load 25.
#[test]
fn the_evaluator_scales() {
    let n = 250_000;
    let groups = scaling::inputs(n, |m| Flat::of(&wide(m)));
    scaling::check("the evaluator on bodies of n types", n, |m| {
        std::hint::black_box(groups[&m].monotone().is_ok());
    });
}

/// The exact sweeps `random_groups_admitted_are_monotone` replaced (TEST-bench-move-l0123):
/// every seed of 0..25,000 and of 25,000..50,000, each held to the false rejections its seeds
/// gave, 14,200 and 14,263, so that one false rejection more fails, where the draw of
/// `DRAWN` seeds lets a rise of some 9% pass (TEST-l0123-leftovers). They are the cases of
/// that test in full, so they run here (author P178: many cases make a benchmark); about
/// 2.2 s each alone.
#[test]
fn every_group_of_the_first_half_of_the_seeds_admitted_is_monotone() {
    sweep(
        "sweep of seeds 0..25,000",
        0..SWEPT / 2,
        FALSE_IN_FIRST_HALF,
    );
}

/// The second half of the exact sweep; see the first.
#[test]
fn every_group_of_the_second_half_of_the_seeds_admitted_is_monotone() {
    sweep(
        "sweep of seeds 25,000..50,000",
        SWEPT / 2..SWEPT,
        FALSE_IN_SECOND_HALF,
    );
}
