//! Benchmarks of `lazy`: each times the work at a size and at 8 times it, run apart from the
//! correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// A constraint written after a kept test whose case fixes one of its names and leaves
/// another open is asked at the case's point (`Scope::written_dead`, `Scope::no_point_at`):
/// k groups of [`points_asked`], eager and lazy, at k and 8k, the answers checked at each size
/// as in `points_asked_after_a_disjunction_are_answered`. Moved here from the correctness
/// tests, whose piece it took past 20 s (TEST-vm-pieces-over-20s, 2026-11-22).
#[test]
fn points_asked_after_a_disjunction_scale() {
    let made = zed_tests::scaling::inputs(64, |k| (points_asked_scope(k), points_asked(k)));
    for lazy in [false, true] {
        let what = format!("constraints asked at kept points, lazy: {lazy}");
        zed_tests::scaling::check(&what, 64, |k| {
            let (s, ts) = &made[&k];
            std::hint::black_box(points_asked_settled(s, ts, k, lazy));
        });
    }
}
