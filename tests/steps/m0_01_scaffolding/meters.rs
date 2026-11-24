//! BENCH-meters-outside-bench: a test whose path holds no `bench::` may not hold measured work to
//! a limit, since tools/run_tests.sh runs it in a correctness piece, 8 tests at a time, where the
//! meter counts processor time and load can fail a ratio. `zed_tests::scaling`'s
//! `refuse_outside_a_bench` stops it as the comparison starts; its list of the tests allowed
//! anyway, each with its reason, is `MEASURED_OUTSIDE_A_BENCH` there.

use zed_tests::scaling;

/// A comparison of two runs made by a test outside `bench::` (this one, `meters::...`) stops the
/// test, with a message that says where to move it. Before the check this test compared the two
/// runs and passed.
#[test]
#[should_panic(expected = "holds measured work to a limit, but its path holds no `bench::`")]
fn a_comparison_made_outside_a_bench_path_is_refused() {
    scaling::compare_costs(
        "two empty runs",
        "a test of the refusal",
        10.0,
        || {},
        || {},
    );
}

/// A bound on the time per unit of work is refused the same way.
#[test]
#[should_panic(expected = "holds measured work to a limit, but its path holds no `bench::`")]
fn a_time_per_unit_held_outside_a_bench_path_is_refused() {
    scaling::per_unit_bound("one case", &[("a".to_string(), 1, 1)], 1, 1);
}

/// A meter made outside `bench::` is not refused: a correctness test at small sizes may run a
/// benchmark's helper, which makes one and prints its readings.
#[test]
fn a_meter_made_outside_a_bench_path_is_allowed() {
    let mut meter = scaling::Meter::new();
    let _ = meter.read();
}
