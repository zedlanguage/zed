//! The benchmarks of `admission_sweep.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `admission_sweep.rs`.

use super::*;

/// The admission of a group of n definitions costs time linear in n.
#[test]
fn admitting_a_group_scales() {
    let n = 256;
    let groups = scaling::inputs(n, ring);
    scaling::check("admitting a ring group of n definitions", n, |m| {
        Group::new(groups[&m].clone()).expect("a ring group is accepted");
    });
}

/// The evaluator on a group of three definitions costs time linear in the size of the bodies.
#[test]
fn the_evaluator_scales() {
    let n = 1024;
    let groups = scaling::inputs(n, |m| Flat::of(&wide(m)));
    scaling::check("the evaluator on bodies of n types", n, |m| {
        std::hint::black_box(groups[&m].monotone().is_ok());
    });
}
