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
    // Built by `check_inputs`, only at the sizes each process runs: built at both sizes before
    // the first run (`scaling::inputs`), they took the whole first phase where each run is
    // counted under DynamoRIO in a new process that builds its input again; it stopped at its
    // 20 s limit on hm4 (job f25 on main b43e6d8bb), and with no limit counted 8.00 times the
    // instructions at 8n in 40 s (job f27; BENCH-main-43-pieces-v5e4).
    let n = 250_000;
    scaling::check_inputs(
        "the evaluator on bodies of n types",
        n,
        |m| Flat::of(&wide(m)),
        |group| {
            std::hint::black_box(group.monotone().is_ok());
        },
    );
}

/// The exact sweeps `random_groups_admitted_are_monotone` replaced (TEST-bench-move-l0123):
/// every seed of 0..25,000 and of 25,000..50,000, each held to the false rejections its seeds
/// gave, 14,081 and 14,142 (GROUP-admit-precision, `rec::holds` steps 3 and 4, b22-ref3,
/// 2026-11-23; were 14,093 and 14,158), so that one false rejection
/// more fails, where the draw of
/// `DRAWN` seeds is held to no count (TEST-l0123-leftovers, PROOF-test-count-thresholds).
/// They are the cases of that test in full, so they run here (author P178: many cases make a
/// benchmark); about 2.2 s each alone.
#[test]
fn every_group_of_the_first_half_of_the_seeds_admitted_is_monotone() {
    sweep(
        "sweep of seeds 0..25,000",
        0..SWEPT / 2,
        Some(FALSE_IN_FIRST_HALF),
    );
}

/// The second half of the exact sweep; see the first.
#[test]
fn every_group_of_the_second_half_of_the_seeds_admitted_is_monotone() {
    sweep(
        "sweep of seeds 25,000..50,000",
        SWEPT / 2..SWEPT,
        Some(FALSE_IN_SECOND_HALF),
    );
}
