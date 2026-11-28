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

/// [`three_cases_at`] at r = 1,000·n for n and 8n, eager and lazy: the cases' classes 0 and 1
/// modulo 3 hold 2r + 2 values, joined as one set per class in the product
/// (LIMITS-classed-listing-per-set). Measured at r = 10^6 and 8·10^6, eager: instructions 1.54
/// times and bytes 7.3 times (about 200 instructions and 143 bytes per unit of r over a fixed
/// 2.6·10^9 instructions). By callgrind (DECIDE-perf-cover-site-split) the fixed part was
/// `exact::guarded::two_pins::u_runs` trying each value of a case's strip; read by the strip's
/// equation since PERF-cover-union-of-classes-listed (two_pins part), the same sizes take
/// 227,358,694 and 1,640,999,236 instructions (7.22 times; bytes 148,387,876 and 1,143,523,404,
/// local run, 2026-11-27): about 25·10^6 fixed and the same 200 a unit of r, not yet profiled
/// (callgrind of 2026-11-27 before that change put 8% in `row_sums::project`, which answers
/// with each value listed). So both are held to `scaling::limit(1)` until the row's row_sums
/// part is done. Negative control: the same values listed one range a value (`Classed::met` of
/// `Product::classed`, the form the cases had below the old listing limit) are 8 times as many
/// ranges at 8n, over that limit.
#[test]
fn three_cases_of_two_classes_scale() {
    let listed = |r: i64| three_cases_at(r, false).classed().met().len() as u64;
    let (small, large) = (listed(1_000), listed(8_000));
    assert!(
        large as f64 / small as f64 >= zed_tests::scaling::limit(0),
        "control: {small} and {large} ranges listed"
    );
    for lazy in [false, true] {
        let what = format!("three cases of two classes past the old listing limit, lazy: {lazy}");
        zed_tests::scaling::check_order(&what, 1_000, 0, |n| {
            std::hint::black_box(three_cases_at(1_000 * n as i64, lazy));
        });
    }
}
