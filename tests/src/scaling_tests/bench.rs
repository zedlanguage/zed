//! The two self-tests of [`crate::scaling`] that time work at two sizes on purpose and expect a
//! ratio far past the limit, so they take seconds (TEST-bench-move-crates, author P169):
//! benchmarks, run with `tools/run_tests.sh --bench`. The checks of the meters and the limit in
//! small steps are in [`super`]: `a_reading_grows_by_the_work_between` and
//! `work_a_power_of_n_above_the_order_given_fails` (instructions),
//! `the_processor_time_of_a_thread_leaves_out_its_sleep` (processor time),
//! `a_meter_counts_the_work_of_a_run_and_not_the_time_it_sleeps` and
//! `the_bytes_of_a_bare_thread_a_run_starts_count` (a thread a run starts).

use super::*;
use super::{fails, work};

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
/// 8000 (64 times, limit 11.4 of 2026-11-12, 22.9 by time), took as long and measured 49 to 61
/// times by time, but only 26 to 31 times with the small run made twice as slow, near the limit.
/// The cubic work measured 179 to 239 times by time, and 138 to 154 times with the small run
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

/// About 2n allocations on the meter's heap (module `meter` of zed-alloc-count, which every run
/// of [`check_order`] allocates from), at `n` and 8n: `n` blocks of 1 to 1024 bytes, then every
/// other one freed, so that about n/2 blocks wait on the free lists of their classes, then each
/// of those allocated again, from the lists; a vector of `n` words grown by doubling; and a
/// quarter of the blocks allocated on a thread the run starts and freed by the run, which does
/// not reuse them. Each call is O(1) (the module's complexity note) however long the free lists
/// are, so the whole is O(n) and the ratio about 8 (TEST-meter-allocator-bias). A `free` that
/// walked its class's list, as an allocator whose cost grows with the heap's state would, makes
/// the run Θ(n²) and fails (negative control, run once, 2026-11-15).
#[test]
fn a_metered_heap_is_linear() {
    check("allocations on the metered heap", 1 << 16, |n| {
        let churn = |n: usize, from: usize| {
            let size = |i: usize| 1 + (from + i) * 37 % 1024;
            let mut blocks: Vec<Vec<u8>> = (0..n).map(|i| vec![i as u8; size(i)]).collect();
            for i in (0..n).step_by(2) {
                blocks[i] = Vec::new();
            }
            for i in (0..n).step_by(2) {
                blocks[i] = vec![i as u8; size(i)];
            }
            blocks
        };
        let theirs = std::thread::scope(|s| s.spawn(|| churn(n / 4, 1)).join().unwrap());
        let mine = churn(n - n / 4, 0);
        let grown: Vec<u64> = (0..n as u64).collect();
        black_box((theirs, mine, grown));
    });
}

/// The benchmark that [`super::the_phase_at_8n_starts_at_its_run`] runs alone, with
/// `ZED_BENCH_LIMIT_FILE` and [`super::PHASE_SEEN`] naming one file: each input is the time it
/// was built, and the run at 8n reads the phase the file holds then, which must have started
/// after that input was built and ask for a limit of its own (`<start> <ms>`, `ms` above 0).
#[test]
fn a_spin_whose_phase_at_8n_is_read() {
    let now = || {
        let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH);
        t.expect("a clock past 1970").as_millis()
    };
    let seen = std::env::var_os(super::PHASE_SEEN);
    check_inputs(
        "a spin whose phase at 8n is read",
        1000,
        |k| (k, now()),
        |&(k, built)| {
            spin(4000 * k as u64);
            // k bytes, so that the bytes of the two runs can be compared (check_inputs measures
            // them, and refuses a run at 8n that allocates none).
            std::hint::black_box(vec![1u8; k]);
            let Some(path) = seen.as_ref().filter(|_| k == 8000) else {
                return;
            };
            // Read into a buffer on the stack: the run's bytes are measured, and a `String` of
            // the line is allocated in the run at 8n alone (18 bytes in job f4, where the run
            // allocated nothing else). `File::open` of a path under 384 bytes copies it on the
            // stack too (std's `run_path_with_cstr`, MAX_STACK_ALLOCATION).
            use std::io::Read as _;
            let mut buf = [0u8; 64];
            let mut file = std::fs::File::open(path).expect("the file of the phases");
            let len = file.read(&mut buf).expect("reading the file of the phases");
            let line = std::str::from_utf8(&buf[..len]).expect("the file of the phases is text");
            let (start, ms) = line.trim().split_once(' ').expect("<start> <ms>");
            let (start, ms): (u128, u64) = (start.parse().unwrap(), ms.parse().unwrap());
            assert!(
                start >= built && ms > 0,
                "the phase at 8n `{}` started {} ms before its input was built, at {built}",
                line.trim(),
                built.saturating_sub(start)
            );
        },
    );
}

/// The benchmark that [`super::a_hold_in_phases_counts_at_8n_in_a_phase_of_its_own`] runs alone,
/// with `ZED_BENCH_LIMIT_FILE` and [`super::PHASE_SEEN`] naming one file: the count at 8n reads
/// the phase the file holds, which must have started after the count at n ended and ask for a
/// limit of its own (`<start> <ms>`, `ms` above 0); after the hold the file asks for the
/// runner's limit (`ms` 0).
#[test]
fn a_count_held_in_phases() {
    let now = || {
        let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH);
        t.expect("a clock past 1970").as_millis()
    };
    let seen = std::env::var_os(super::PHASE_SEEN);
    let phase = || {
        seen.as_ref().map(|path| {
            let line = std::fs::read_to_string(path).expect("the file of the phases");
            let (start, ms) = line.trim().split_once(' ').expect("<start> <ms>");
            let phase: (u128, u64) = (start.parse().unwrap(), ms.parse().unwrap());
            phase
        })
    };
    let mut counted_at_n = 0;
    hold_in_phases("a count held in phases", "passes", 1000, 1, |k| {
        if k == 1000 {
            counted_at_n = now();
        } else if let Some((start, ms)) = phase() {
            assert!(
                start >= counted_at_n && ms > 0,
                "the phase at 8n `{start} {ms}` started before the count at n ended, at \
                 {counted_at_n}, or asks for no limit of its own"
            );
        }
        k as u64
    });
    if let Some((_, ms)) = phase() {
        assert_eq!(ms, 0, "after the hold, the runner's limit");
    }
}

/// The benchmark that [`super::a_benchmark_run_with_other_tests_counts_instructions`] runs
/// without `--exact`: a spin of 4000 passes per unit of n passes, and its negative control, a
/// spin of n² passes, 64 times the work at 8n, fails. Run so on a machine with no hardware
/// counter and with DynamoRIO named, each check counts the instructions of its runs in new
/// processes (BENCH-time-only-checks-by-instructions), and the control still fails.
#[test]
fn a_spin_run_with_other_tests() {
    let linear = |n: usize| spin(4000 * n as u64);
    check_instructions_only("a spin run with other tests", 1000, 1, linear);
    let square = |n: usize| spin((n * n) as u64);
    assert!(fails(|| check_instructions_only(
        "a square spin run with other tests",
        1000,
        1,
        square
    )));
}
