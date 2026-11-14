//! The benchmarks of `near.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::near::*;
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::negsssp::potential_alone;

#[test]
fn duong_scales_alone() {
    let (small, large) = (feasible(10000, 1), feasible(scaling::FACTOR * 10000, 1));
    for out in [&small, &large] {
        let p = potential_alone(out).expect("no negative cycle");
        assert!(holds(out, &p));
    }
    scaling::check("Duong's search, random graphs by n", 10000, |n| {
        let out = if n == 10000 { &small } else { &large };
        std::hint::black_box(potential_alone(out));
    });
}

/// 50,000 small graphs of `seed` against the reference, both answers more than 1000 times: one
/// of `near::small_graphs_1` to `small_graphs_6` as first written, about 1.5 s each
/// (2026-11-14, load 25), one test per seed so that each runs well within the time limit.
fn small_graphs_of(seed: u64) {
    let (negative, feasible) = against_the_reference(&mut Rng::new(seed), 50_000);
    assert!(
        negative > 1000 && feasible > 1000,
        "seed {seed}: {negative} {feasible}"
    );
}

#[test]
fn small_graphs_1() {
    small_graphs_of(1);
}

#[test]
fn small_graphs_2() {
    small_graphs_of(2);
}

#[test]
fn small_graphs_3() {
    small_graphs_of(3);
}

#[test]
fn small_graphs_4() {
    small_graphs_of(4);
}

#[test]
fn small_graphs_5() {
    small_graphs_of(5);
}

#[test]
fn small_graphs_6() {
    small_graphs_of(6);
}
