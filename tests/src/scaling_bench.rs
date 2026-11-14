//! The two self-tests of [`super`] that time work at two sizes on purpose and expect a ratio
//! far past the limit, so they take seconds (TEST-bench-move-crates, author P169): benchmarks,
//! run with `tools/run_tests.sh --bench`. The checks of the meters and the limit in small
//! steps are in `super::tests`: `a_reading_grows_by_the_work_between` and
//! `work_a_power_of_n_above_the_order_given_fails` (instructions),
//! `the_processor_time_of_a_thread_leaves_out_its_sleep` (processor time),
//! `a_meter_counts_the_work_of_a_run_and_not_the_time_it_sleeps` and
//! `the_bytes_of_a_bare_thread_a_run_starts_count` (a thread a run starts).

use super::tests::{fails, work};
use super::*;

/// Linear work passes and cubic work fails by processor time, at 100 and 800, where the
/// limit is 10.5 (21 by time): 8 and 512 times the work. Measured at load about 25
/// (2026-11-12, three runs): linear 6.6 to 7.4 times, 2.8 times under the allowance of 21; cubic
/// 217 to 501 times, 10.3 times over it. The linear runs are 1 and 8 million passes, as
/// before. This test ran quadratic work at 1000 and 8000 before, 64 times the work against
/// 22.9 by time: measured 42.4 to 58.8 times, only 1.85 times over the allowance, and linear
/// work at 100,000 and 800,000, 5.7 to 6.9 times against 20.8 (load about 31).
// Only Linux has a meter of processor time.
#[cfg(target_os = "linux")]
#[test]
fn processor_time_tells_the_orders_apart_too() {
    let mut meter = Meter::of_cpu_time();
    let cpu = &mut meter;
    check_by(cpu, Measures::WorkOnly, "linear work", 100, 1, |n| {
        work(n, 1, 10_000)
    });
    assert!(fails(|| check_by(
        cpu,
        Measures::WorkOnly,
        "cubic work",
        100,
        1,
        |n| { work(n, 3, 2) }
    )));
}

/// `run` on a thread of its own, as a test on a stack of its own does.
fn on_a_bare_thread(f: impl FnOnce() + Send) {
    std::thread::scope(|s| s.spawn(f).join().unwrap());
}

/// Cubic work on a thread a run starts, at 50 and 400: 512 times the work, against the limit
/// of 10.5 (21 by time). A meter that missed the thread's work would find only the cost of
/// starting it, the same at both sizes. The quadratic work this test ran before, at 1000 and
/// 8000 (64 times, limit 11.4, 22.9 by time), took as long and measured 49 to 61 times by
/// time, but only 26 to 31 times with the small run made twice as slow, near the limit. The
/// cubic work measured 179 to 239 times by time, and 138 to 154 times with the small run
/// twice as slow (by instructions 502 and 253 times), at load 62 to 66 (2026-11-12).
#[test]
fn the_work_of_a_thread_a_run_starts_counts() {
    let cubic = |n| on_a_bare_thread(|| work(n, 3, 2));
    assert!(fails(|| check_instructions_only(
        "cubic work on a thread",
        50,
        1,
        cubic
    )));
    // Only Linux has a meter of processor time.
    #[cfg(target_os = "linux")]
    {
        let cpu = &mut Meter::of_cpu_time();
        assert!(fails(|| check_by(
            cpu,
            Measures::WorkOnly,
            "cubic, by time",
            50,
            1,
            cubic
        )));
    }
}
