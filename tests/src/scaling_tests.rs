//! The tests of [`crate::scaling`], the harness of the scaling tests, compiled into this crate's
//! unit tests only. The harness itself is compiled, by `#[path]`, into the unit tests of
//! zed-kernel, zed-rt, zedc-preimage and zedc-presburger too, and while these tests lay inside it
//! they ran again in each of those binaries, where `cargo test -p <crate>` gives no
//! `GLIBC_TUNABLES` and `malloc_keeps_no_state_from_earlier_threads` failed
//! (TEST-scaling-module-tests-once). They test the harness's private items, which it gives this
//! crate as `pub(crate)`.

use std::hint::black_box;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::Relaxed;
use std::time::Duration;

use crate::scaling::*;

/// Work of order `n^power`: `n^power` units of `unit` passes of a loop.
fn work(n: usize, power: u32, unit: u64) {
    spin(n.pow(power) as u64 * unit);
}

fn fails(run: impl FnOnce()) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)).is_err()
}

/// A command that runs this test binary with the meter this process has, for a test that
/// compares the unit a run prints with this process's `Meter::new`. A process that runs more
/// than one test does not start again under DynamoRIO (`Meter::new`), and one started with
/// `--exact` for one test does; so where this process does not count in software, the run is
/// started without `ZED_METER_DRRUN`, and both measure by the hardware or the task clock. Where
/// it does, DynamoRIO follows the run's `execve`, or the run starts itself again under it.
fn this_binary_with_this_meter() -> std::process::Command {
    let mut command =
        std::process::Command::new(std::env::current_exe().expect("this test binary"));
    if zed_alloc_count::os::software_instructions().is_none() {
        command.env_remove(zed_meter_settings::ZED_METER_DRRUN);
    }
    command
}

/// Which tests may hold measured work to a limit (BENCH-meters-outside-bench): one with `bench::`
/// anywhere in its path, as tools/run_tests.sh reads a benchmark, one the list names, and a
/// thread that is no test. m0_01 `meters::a_comparison_made_outside_a_bench_path_is_refused`
/// checks the refusal itself, from a test outside both.
#[test]
fn a_measure_is_held_only_by_a_test_on_a_bench_path() {
    for refused in [
        "kinds::the_steps_take_linear_time",
        "benchmarks::x",
        "bench_x::y",
        // The entry `scaling_tests::` names a module, not the modules whose names it begins.
        "scaling_tests_x::y",
    ] {
        assert!(outside_a_bench(Some(refused)), "{refused}");
    }
    for allowed in [
        "bench::kinds::the_steps_take_linear_time",
        "exact::tests::bench::two_distributed",
        "deep_bench::x",
        "scaling_tests::a_reading_grows_by_the_work_between",
        "main",
    ] {
        assert!(!outside_a_bench(Some(allowed)), "{allowed}");
    }
    assert!(!outside_a_bench(None));
}

#[test]
fn a_reading_grows_by_the_work_between() {
    let mut m = Meter::new();
    let start = m.read();
    spin(1_000_000);
    let middle = m.read();
    spin(10_000_000);
    let end = m.read();
    assert!(
        end - middle > 5 * (middle - start),
        "{start} {middle} {end}"
    );
}

#[test]
fn work_of_the_order_given_passes() {
    check_instructions_only("linear work", 1000, 1, |n| work(n, 1, 10));
    check_instructions_only("quadratic work", 100, 2, |n| work(n, 2, 2));
}

/// Work of a power of n above the order a check is given fails, and the same work at its own
/// order passes (the negative control). On the meter this machine gives, the work is two powers
/// above, since processor time, the meter of a machine with no counter of instructions (Colab
/// VMs), cannot tell one power from the next at the sizes of a unit test: `work(n, 2, 2)` at 100
/// and 800, 64 times the work, took 5.2 times the time on hm5 (2026-11-22), the start of the
/// run's thread, about 0.22 ms, being most of the run at 100, and over the limit a ratio of the
/// fastest of five runs can fall to 0.34 of the work's (see
/// [`TIME_RUNS`]). Cubic work at power 1 is 512 times the work for a limit of 10.5 there (21
/// until FAIL-scaling-check-passes-over-limit), and
/// `work(n, 3, 500)` runs 500,000 passes at 10, about 0.4 ms, so the ratio stays over 100 at
/// 0.34 of the work's. One power above, at power 2, is held on a counter only the run moves,
/// as a count of instructions and as one of processor time (TEST-scaling-lib-no-counter: until
/// 2026-11-22 this test held quadratic work at power 1 and cubic at power 2 on the machine's
/// meter, which failed on every Colab VM).
#[test]
fn work_a_power_of_n_above_the_order_given_fails() {
    let cubic = |n| work(n, 3, 500);
    assert!(fails(|| check_instructions_only(
        "cubic work",
        10,
        1,
        cubic
    )));
    check_instructions_only("cubic work", 10, 3, cubic);
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let cubic = |n: usize| {
        spin((n * n * n) as u64);
        PASSES.fetch_add((n * n * n) as u64, Relaxed);
    };
    for instructions in [true, false] {
        let mut meter = Meter {
            read: Box::new(|| PASSES.load(Relaxed)),
            unit: "passes",
            instructions,
            fresh: false,
            elsewhere: false,
        };
        let only = Measures::WorkOnly;
        assert!(fails(|| check_by(
            &mut meter,
            only,
            "cubic passes",
            10,
            2,
            cubic
        )));
        check_by(&mut meter, only, "cubic passes", 10, 3, cubic);
    }
}

/// A meter of the passes `passes` counts, which only one test adds to, so the ratio of two runs
/// is that of the passes they are given, exactly (TEST-cov-scaling-noise). The checks of a ratio
/// within 1% of the limit use it, and not the instruction counter, whose count of a fixed loop is
/// exact in the normal build (the same within 0.01% in 24 runs beside the other tests) but not in
/// a coverage build: there each pass of [`spin`] adds to one counter of the coverage map by
/// `lock incq`, a write every thread running `spin` shares, and with tests running beside each
/// other the hardware counted up to 5% more instructions than the 5 per pass the loop retires
/// (10.68 times for n log n work at 1000, over the limit of 10.5; 10.346 to 10.348 with one test
/// at a time). The instruction counter is tested away from the limit, where 5% decides nothing:
/// `work_of_the_order_given_passes` and `work_a_power_of_n_above_the_order_given_fails`.
fn meter_of_passes(passes: &'static AtomicU64) -> Meter {
    Meter {
        read: Box::new(|| passes.load(Relaxed)),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    }
}

/// Work of order `n log n`: `50 n log2 n` passes, counted in `passes`.
fn n_log_n_passes(passes: &'static AtomicU64, n: usize) {
    passes.fetch_add((n as f64 * (n as f64).log2() * 50.0) as u64, Relaxed);
}

/// Work of order `n^1.25` and n log n at sizes n and 8n, counted exactly, against the limit of
/// 10.5: `n^1.25`, which the limit of 24 for k = 1 let pass (13.45 times at 8n), fails at
/// n = 1000, and n log n passes there (10.408 times) and at n = 2000 (10.19 times).
#[test]
fn work_a_quarter_power_above_n_log_n_fails() {
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let meter = &mut meter_of_passes(&PASSES);
    let n_log_n = |n: usize| n_log_n_passes(&PASSES, n);
    check_by(meter, Measures::WorkOnly, "n log n work", 1000, 1, n_log_n);
    check_by(meter, Measures::WorkOnly, "n log n work", 2000, 1, n_log_n);
    let quarter = |n: usize| _ = PASSES.fetch_add(((n as f64).powf(1.25) * 500.0) as u64, Relaxed);
    let message = message_of(|| {
        check_by(
            meter,
            Measures::WorkOnly,
            "work of order n^1.25",
            1000,
            1,
            quarter,
        )
    });
    assert!(message.contains("13.45 times the work"), "{message}");
}

/// The limit is 10.5 at 8n for work of order n, times `8^(k − 1)` for order `n^k`. Work of
/// order n log n is under it from n = 777 on (10.4995 times at 777, 10.5000 at 776), work of
/// order `n^1.13` (10.48 times) is under it at every n and work of order `n^1.14` (10.70
/// times) over it, and work of order `n log^2 n` is under it from n = 1,587,343 on.
#[test]
fn the_limit_is_10_5_times_8_to_the_power_less_one() {
    assert_eq!(
        (limit(0), limit(1), limit(2), limit(3)),
        (1.3125, 10.5, 84.0, 672.0)
    );
    let n_log_n = |n: f64| 8.0 * (8.0 * n).ln() / n.ln();
    assert!(n_log_n(777.0) < limit(1) && n_log_n(776.0) > limit(1));
    assert!(8f64.powf(1.14) > limit(1) && 8f64.powf(1.13) < limit(1));
    let n_log2_n = |n: f64| n_log_n(n).powi(2) / 8.0;
    assert!(n_log2_n(1_587_343.0) < limit(1) && n_log2_n(1_587_342.0) > limit(1));
}

/// [`n_log_n_ratio`] is `8 ln(8n) / ln(n)`, and [`check_n_log_n_by`] holds work to it. Work of
/// order n log n with a linear part, `50 n (log2 n + 1)` passes, passes at 4096 (128/13 = 9.85
/// times, under 10) and at 2500; at 64 the ratio of n log n is 12, over the limit, so the bound
/// is 10.5: linear work passes there and work of order n log n alone fails (12 times). Work of
/// order `n^1.12` (10.27 times) fails at 4096, though it is under the limit of 10.5, and work
/// of order `n log² n` fails there, 12.5 times.
#[test]
fn work_proved_n_log_n_is_held_to_the_ratio_of_n_log_n() {
    assert_eq!(format!("{:.2}", n_log_n_ratio(4096)), "10.00");
    assert_eq!(format!("{:.2}", n_log_n_ratio(2500)), "10.13");
    assert_eq!(format!("{:.2}", n_log_n_ratio(64)), "12.00");
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let meter = &mut meter_of_passes(&PASSES);
    let n_log_n_and_n = |n: usize| {
        n_log_n_passes(&PASSES, n);
        _ = PASSES.fetch_add(n as u64 * 50, Relaxed)
    };
    check_n_log_n_by(
        meter,
        Measures::WorkOnly,
        "n log n work",
        4096,
        &n_log_n_and_n,
    );
    check_n_log_n_by(
        meter,
        Measures::WorkOnly,
        "n log n work",
        2500,
        &n_log_n_and_n,
    );
    let linear = |n: usize| _ = PASSES.fetch_add(n as u64 * 600, Relaxed);
    check_n_log_n_by(meter, Measures::WorkOnly, "linear work", 64, &linear);
    let n_log_n = |n: usize| n_log_n_passes(&PASSES, n);
    assert!(fails(|| {
        check_n_log_n_by(meter, Measures::WorkOnly, "n log n work", 64, &n_log_n)
    }));
    let above = |n: usize| _ = PASSES.fetch_add(((n as f64).powf(1.12) * 200.0) as u64, Relaxed);
    assert!(fails(|| {
        check_n_log_n_by(
            meter,
            Measures::WorkOnly,
            "work of order n^1.12",
            4096,
            &above,
        )
    }));
    let n_log2_n = |n: usize| {
        let log = (n as f64).log2();
        _ = PASSES.fetch_add((n as f64 * log * log * 50.0) as u64, Relaxed)
    };
    let message = message_of(|| {
        check_n_log_n_by(meter, Measures::WorkOnly, "n log² n work", 4096, &n_log2_n)
    });
    assert!(message.contains("12.50 times the work"), "{message}");
}

/// `n` times the levels of a trie whose leaf holds 4096 numbers and each level above it 64
/// times as many: 16 times at 4096 and 32,768, where the second level comes, and 8 times at
/// 512.
fn n_times_levels(n: usize) -> f64 {
    let (mut levels, mut held) = (1, 4096);
    while held < n {
        (levels, held) = (levels + 1, held * 64);
    }
    (n * levels) as f64
}

/// [`check_proved_cost_by`] holds work to the ratio of the cost given at the two sizes, over
/// [`LIMIT`] where that cost steps: work of `n` times the levels with a linear part passes at
/// 4096 (12 times, over 10.5, under 16); work of order n log n fails at 512, where the cost
/// does not step and the bound is 8; work of `n^1.2` times the levels, 24.25 times at 4096,
/// fails there.
#[test]
fn work_proved_of_a_stepped_cost_is_held_to_that_costs_ratio() {
    assert_eq!(n_times_levels(32_768) / n_times_levels(4096), 16.0);
    assert_eq!(n_times_levels(4096) / n_times_levels(512), 8.0);
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let meter = &mut meter_of_passes(&PASSES);
    let cost = ("n L(n)", n_times_levels as fn(usize) -> f64);
    let levels_and_n =
        |n: usize| _ = PASSES.fetch_add((n_times_levels(n) * 50.0) as u64 + n as u64 * 50, Relaxed);
    check_proved_cost_by(
        meter,
        Measures::WorkOnly,
        "n L(n) work",
        4096,
        cost,
        &levels_and_n,
    );
    let n_log_n = |n: usize| n_log_n_passes(&PASSES, n);
    let message = message_of(|| {
        check_proved_cost_by(
            meter,
            Measures::WorkOnly,
            "n log n work",
            512,
            cost,
            &n_log_n,
        )
    });
    assert!(message.contains("under 8.00 times"), "{message}");
    let above = |n: usize| {
        _ = PASSES.fetch_add(
            (n_times_levels(n) * (n as f64).powf(0.2) * 50.0) as u64,
            Relaxed,
        )
    };
    assert!(fails(|| {
        check_proved_cost_by(
            meter,
            Measures::WorkOnly,
            "n^1.2 L(n) work",
            4096,
            cost,
            &above,
        )
    }));
}

/// [`hold`] passes a ratio under the limit, fails one at it or over it, and reads a count of
/// 0 as 1.
#[test]
fn a_held_ratio_must_be_under_the_limit() {
    assert_eq!(hold("nodes, n and 8n", "nodes", 100, 1049, 1), 10.49);
    assert!(fails(|| _ = hold("nodes, n and 8n", "nodes", 100, 1050, 1)));
    assert!(fails(|| _ = hold("nodes, n and 8n", "nodes", 100, 8_400, 2)));
    assert_eq!(hold("nodes, n and 8n", "nodes", 0, 8, 1), 8.0);
    let message = message_of(|| _ = hold("steps at 10 and 80", "steps", 10, 200, 1));
    assert!(
        message.contains("steps at 10 and 80: 10 and 200 steps, 20.00 times at 8n"),
        "{message}"
    );
}

/// Run by [`a_ratio_from_9_to_10_5_prints_a_note_naming_the_test`]: a ratio of 10 by [`hold`]
/// and work of order n log n at 1000 (10.408 times, counted by [`meter_of_passes`]) print a
/// note, a ratio of 8 none.
#[test]
fn ratios_near_the_limit_pass() {
    static PASSES: AtomicU64 = AtomicU64::new(0);
    hold("ten times", "nodes", 100, 1000, 1);
    hold("eight times", "nodes", 100, 800, 1);
    let n_log_n = |n: usize| n_log_n_passes(&PASSES, n);
    let meter = &mut meter_of_passes(&PASSES);
    check_by(meter, Measures::WorkOnly, "n log n work", 1000, 1, n_log_n);
}

#[test]
fn a_ratio_from_9_to_10_5_prints_a_note_naming_the_test() {
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "--exact",
            "scaling_tests::ratios_near_the_limit_pass",
            "--show-output",
            "--test-threads=1",
        ])
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{out}");
    let note = "note: scaling_tests::ratios_near_the_limit_pass: ";
    assert!(
        out.contains(&format!("{note}ten times: 10.00 times the nodes")),
        "{out}"
    );
    assert!(
        out.contains(&format!("{note}n log n work: sizes 1000 and 8000: ")),
        "{out}"
    );
    assert!(!out.contains(&format!("{note}eight times")), "{out}");
    assert!(
        out.contains("eight times: passed: 100 and 800 nodes, 8.00 times"),
        "{out}"
    );
}

#[test]
fn a_comparison_holds_two_sizes_to_the_limit_of_their_order() {
    // Lists of 2^17 and 2^20 words at most: 8 times the work and the bytes; and 2^23, 64 times.
    let (small, large) = (|| linear_bytes(100_000), || linear_bytes(800_000));
    compare("8 times", 1, small, large);
    assert!(fails(|| compare("64 times", 1, small, || linear_bytes(
        6_400_000
    ))));
    compare("64 times, of order n^2", 2, small, || {
        linear_bytes(6_400_000)
    });
}

/// A comparison by the meter this machine gives runs each size once on a count of instructions
/// (author A160, 2026-11-20), and on processor time the fastest of [`TIME_RUNS`] in each
/// measurement, up to [`TRIES`] measurements: a comparison under its limit runs each size
/// [`TIME_RUNS`] times, and one over it in every measurement [`Meter::runs`] times (the negative
/// control) and fails. Both sizes run in this process (see
/// `a_set_up_hidden_in_a_memo_the_process_keeps_is_counted_at_8n` for the run in a new process).
/// The limits, one no ratio is over and one every ratio is over, make the count the same at any
/// load. Until TEST-scaling-lib-no-counter (2026-11-22) this test held [`Meter::runs`] to one
/// run of each size, which failed on every machine with no counter of instructions (Colab VMs).
#[test]
fn a_comparison_runs_each_size_as_often_as_the_meter_says() {
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    let mut meter = Meter::new();
    meter.fresh = false;
    let one = if meter.instructions { 1 } else { TIME_RUNS };
    let most = meter.runs();
    let mut counted = |limit: f64| {
        let (small, large) = (AtomicUsize::new(0), AtomicUsize::new(0));
        let failed = fails(|| {
            compare_by(
                &mut meter,
                Measures::WorkOnly,
                None,
                "counted runs",
                Bound::Given(
                    limit,
                    "a limit no ratio is over, or one every ratio is over",
                ),
                || _ = small.fetch_add(1, Relaxed),
                || _ = large.fetch_add(1, Relaxed),
            )
        });
        (failed, small.into_inner(), large.into_inner())
    };
    assert_eq!(counted(f64::INFINITY), (false, one, one));
    assert_eq!(counted(0.0), (true, most.0, most.1));
}

#[test]
fn the_processor_time_of_a_thread_leaves_out_its_sleep() {
    let start = cpu_time();
    std::thread::sleep(Duration::from_millis(20));
    let slept = cpu_time() - start;
    assert!(slept < Duration::from_millis(10), "{slept:?}");
}

#[test]
#[should_panic(expected = "cannot measure work")]
fn with_no_counter_a_test_stops_with_its_own_error() {
    no_counter();
}

/// Fails where a copy or fill runs as a `rep` instruction a hardware counter sees as one:
/// there, a quadratic copy would pass [`check`]. The sizes run from past the 4 KiB at which
/// glibc starts `rep` on most CPUs to past the 12 MiB at which it starts on some.
///
/// A meter of processor time sees a `rep` copy's work whatever its length, so there the
/// 64 KiB size, whose copy runs 15 to 23 µs, is left out: measured on a Colab VM with no
/// hardware counter (l43, 12 cores, 2026-11-23, b22-tests7), its least of the runs was 2.6 to 4
/// times that of 8 times the length under load, below the 4 asserted, as `work(n, 1, 10_000)`
/// in the processor-time table of `scaling.rs` (least 2.74 under load): runs of tens of µs
/// are within the clock's and the scheduler's noise. 0 of 45 runs failed there (20 idle, 20 and
/// 5 alone under 24 busy loops); misc8 saw the failure at load 28 (FAIL-copies-and-fills-meter-
/// under-load). The 1 MiB and 16 MiB sizes run 0.2 ms and more.
#[test]
fn copies_and_fills_count_by_their_length() {
    let mut meter = Meter::new();
    let from = vec![1u8; 128 << 20];
    let to = std::cell::RefCell::new(vec![2u8; 128 << 20]);
    let sizes: &[usize] = if meter.instructions {
        &[64 << 10, 1 << 20, 16 << 20]
    } else {
        &[1 << 20, 16 << 20]
    };
    for &len in sizes {
        let copy = |len| to.borrow_mut()[..len].copy_from_slice(black_box(&from[..len]));
        let fill = |len: usize| to.borrow_mut()[..len].fill(black_box(3));
        for (what, f) in [("copy", &copy as &dyn Fn(usize)), ("fill", &fill)] {
            let small = meter.least(|| {}, || f(len));
            let large = meter.least(|| {}, || f(FACTOR * len));
            let (small, large) = (small.units, large.units);
            let ratio = large as f64 / small as f64;
            assert!(
                ratio >= FACTOR as f64 / 2.0,
                "a {what} of {len} bytes took {small} and one {FACTOR} times as long took \
                 {large} {}: this meter does not see the work of a long {what}. Run the \
                 tests by tools/run_tests.sh, which keeps glibc from rep movsb and rep stosb",
                meter.unit()
            );
        }
    }
}

/// A run that allocates blocks of many sizes, frees half of them in a scattered order, grows a
/// vector, and frees the rest. Its own work is the same each time: no hash seed, no thread.
fn churn() {
    let mut blocks: Vec<Option<Vec<u8>>> = (0..2000usize)
        .map(|i| Some(vec![i as u8; 1 + i * 37 % 3000]))
        .collect();
    for i in 0..1000usize {
        blocks[i * 7919 % 2000] = None;
    }
    let mut grown = Vec::new();
    for i in 0..5000u64 {
        grown.push(i);
    }
    black_box((blocks, grown));
}

/// [`churn`] on two threads at once, which allocate blocks the run frees.
fn churn_on_threads() {
    let theirs = std::thread::scope(|s| {
        let a = s.spawn(churn);
        let b = s.spawn(|| (0..300).map(|i| vec![0u32; i]).collect::<Vec<_>>());
        a.join().unwrap();
        b.join().unwrap()
    });
    black_box(theirs);
}

/// The instructions of `run` in five rounds, each after the heaps of the C library were left in
/// another state and another thread had come and gone: on a thread of [`alone`], which allocates
/// from a metered heap, when `metered`, and else on a thread started plainly, which allocates
/// from glibc's malloc.
///
/// Two things change a count that are not the allocator's, and both are measured on a run that
/// allocates nothing (`spin(10)` and `spin(1_000_000)` in `alone`, 2026-11-15): the first run in
/// a process counts about 1,760 instructions more, the one-time work of the first thread `alone`
/// starts, which the harness's warm-up run takes too (see `Meter::repeats`), so a warm-up run is
/// left out here; and the counter now and then counts an instruction twice, 1 more in some runs,
/// as the hardware counters of x86 overcount on an interrupt or a page fault (V. M. Weaver,
/// D. Terpstra and S. Moore, "Non-determinism and overcount on modern hardware performance
/// counter implementations", ISPASS 2013, pp. 215-224, doi:10.1109/ispass.2013.6557172; read
/// 2026-11-21 in the publisher's PDF, from LibGen). Sec. "Sources of Overcount and
/// Non-Determinism on x86 64", p. 218: "Most x86 64 events are incremented an extra time for
/// every hardware interrupt", and a page fault "counts as an extra instruction". Table IV,
/// p. 219, marks the total retired instructions event on every machine tested (Atom to
/// IvyBridge, Pentium D, Phenom, Istanbul, Bobcat) with interrupts, page faults, x87/SSE
/// exceptions and the lazy FP save, and on Pentium D and the AMD machines with instructions
/// counted twice; it marks no machine as undercounting that event, though the text names an
/// instruction "not counted at all" as one possible error. Every marked cause adds counts,
/// so the least of three runs is the one nearest the true count. The paper tested no
/// machine newer than IvyBridge; that the counter here does not undercount rests on the
/// 2026-11-15 runs above, whose counts were the base count or 1 more.
fn counts_of(run: fn(), metered: bool) -> Vec<u64> {
    let mut meter = Meter::new();
    let mut once = || {
        if metered {
            meter.work(|| _ = alone(&run)).units
        } else {
            meter
                .work_on_the_c_heap(|| std::thread::scope(|s| s.spawn(run).join().unwrap()))
                .units
        }
    };
    once();
    let mut counts = Vec::new();
    let mut kept = Vec::new();
    for round in 0..5usize {
        kept.extend((0..round * 500).map(|i| vec![0u8; 1 + i * 13 % 900]));
        std::thread::spawn(|| black_box(vec![0u8; 4096]))
            .join()
            .unwrap();
        counts.push((0..3).map(|_| once()).min().unwrap());
    }
    black_box(kept);
    counts
}

/// Prints the counts of [`churn_on_threads`] by [`counts_of`] on the meter's heap and on glibc's
/// malloc, for `the_instructions_of_a_run_repeat`, which runs this test alone. It holds nothing
/// itself: beside the other tests of the binary both sets of counts spread by about 1,000
/// (2026-11-15, three runs of the binary), since a thread's start costs instructions that depend
/// on the other threads alive (std's map of live threads, see zed-alloc-count's documentation,
/// and glibc's cache of thread stacks); a scaling run is measured beside other tests too, and
/// takes the least of its runs for that reason.
#[test]
fn counts_of_a_run_on_each_heap() {
    println!("meter unit {}", Meter::new().unit());
    let ours = counts_of(churn_on_threads, true);
    let glibc = counts_of(churn_on_threads, false);
    println!("metered heap {ours:?}, glibc {glibc:?}");
}

/// The count of instructions of a run that starts threads changes less from run to run on the
/// meter's heap than on glibc's malloc, whatever the heaps held before and the threads before:
/// the meter's allocator (module `meter` of zed-alloc-count) spends on each call what the run's
/// own calls decide (TEST-meter-allocator-bias). The counts come from
/// `counts_of_a_run_on_each_heap` run alone in a process of its own, where no other test starts
/// threads. Measured (2026-11-15, 3 processes each time, twice): the metered counts differ by at
/// most 1, the counter's own overcount, and glibc's with its per-thread cache by 700 to 890. That
/// the allocator's state follows the run's own calls alone is tested exactly, without the
/// counter, by zed-alloc-count's test
/// `a_metered_run_places_its_blocks_the_same_way_whatever_came_before`.
#[test]
fn the_instructions_of_a_run_repeat() {
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "--exact",
            "scaling_tests::counts_of_a_run_on_each_heap",
            "--show-output",
            "--test-threads=1",
        ])
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{out}");
    // The spreads compared below are of instructions. Where the run alone found neither the
    // hardware counter nor DynamoRIO's zed_icount, its meter reads processor time, whose spread
    // from run to run is the load's and says nothing of the heaps: b22-mem40's merge check
    // (2026-11-22, run 3) failed so with counts of 3 to 5 million ns, on a checkout older than
    // tools/icount, for which Colab's job.sh sets no ZED_METER_DRRUN (TEST-instructions-repeat-
    // recheck). That case is named here, not reported as a spread.
    let unit = out
        .lines()
        .find_map(|l| l.strip_prefix("meter unit "))
        .unwrap_or_else(|| panic!("no line naming the meter in:\n{out}"));
    assert!(
        unit.starts_with("instructions"),
        "the run alone counted {unit}, not instructions: this machine has no hardware counter of \
         instructions, and ZED_METER_DRRUN and ZED_METER_ICOUNT (crate zed-meter-settings) do not \
         name DynamoRIO and its client zed_icount (tools/icount), so the spreads of the two heaps \
         cannot be compared"
    );
    let line = out
        .lines()
        .find_map(|l| l.strip_prefix("metered heap "))
        .unwrap_or_else(|| panic!("no line of counts in:\n{out}"));
    let (ours, glibc) = line.split_once(", glibc ").expect("two lists of counts");
    let counts = |list: &str| -> Vec<u64> {
        list.trim_matches(['[', ']'])
            .split(", ")
            .map(|c| c.parse().expect("a count"))
            .collect()
    };
    let (ours, glibc) = (counts(ours), counts(glibc));
    let spread = |c: &[u64]| c.iter().max().unwrap() - c.iter().min().unwrap();
    assert!(
        spread(&ours) < spread(&glibc),
        "the metered heap's counts {ours:?} spread as much as glibc's {glibc:?}"
    );
}

/// `tools/run_tests.sh` exports the settings the meter counts under, the same text as
/// `zed_meter_settings::GLIBC_TUNABLES`, so a binary it runs need not start itself again and the
/// programs the tests start run under them too.
#[test]
fn run_tests_exports_the_settings_of_the_meter() {
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../tools/run_tests.sh");
    let text = std::fs::read_to_string(script).expect("tools/run_tests.sh");
    let exports: Vec<&str> = text
        .lines()
        .filter_map(|l| l.strip_prefix("export GLIBC_TUNABLES="))
        .collect();
    assert_eq!(exports, [zed_meter_settings::GLIBC_TUNABLES]);
}

/// When the function of zed-meter-settings in `.init_array` ran, this process had one thread, so
/// it read the environment raw and could start the binary again (argument at `START` in
/// crates/zed-meter-settings/src/lib.rs). This binary loads the workspace's dylibs, whose
/// constructors run before that function; the crate's own test of the same name covers a binary
/// without them. Fails when a constructor of a library or of the program starts a thread.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn no_other_thread_exists_when_start_runs() {
    assert_eq!(zed_meter_settings::threads_at_start(), Some(1));
}

/// The variable the start of a test binary sets for a benchmark is the one zed-collections reads.
#[test]
fn the_meter_fixes_the_draw_zed_collections_reads() {
    assert_eq!(
        zed_meter_settings::ZED_TREAP_SEED,
        zed_collections::priority::SEED_VAR
    );
}

/// A benchmark started by a runner that does not fix the draw (cargo, Colab's job.sh) measures
/// the draw 0, and one given a draw keeps it; a process whose filter names no benchmark keeps a
/// fresh draw. Each run is this binary started on `bench::the_draw_of_this_process` with
/// `ZED_TREAP_SEED` removed or set, with the meter's settings (no start again) and without
/// them (the start again sets the draw in the second image). Failed before
/// FAIL-bench-random-fingerprint-primes, when the first printed `unset`.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn a_benchmark_measures_a_fixed_draw_by_any_runner() {
    let probe = "scaling_tests::bench::the_draw_of_this_process";
    let draw = |args: &[&str], seed: Option<&str>, settings: bool| {
        let mut run =
            std::process::Command::new(std::env::current_exe().expect("this test binary"));
        run.args(args).args(["--nocapture", "--test-threads=1"]);
        match seed {
            Some(s) => run.env(zed_meter_settings::ZED_TREAP_SEED, s),
            None => run.env_remove(zed_meter_settings::ZED_TREAP_SEED),
        };
        if !settings {
            run.env_remove("GLIBC_TUNABLES");
        }
        let out = run.output().expect("this test binary runs");
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        assert!(out.status.success(), "{text}");
        // With one test thread libtest writes `test <path> ... ` before the test runs, so the
        // probe's line follows it on the same line.
        let line = text
            .lines()
            .find_map(|l| l.split_once("draw: ").map(|(_, r)| r));
        line.and_then(|r| r.split_whitespace().next())
            .map(str::to_owned)
    };
    for settings in [true, false] {
        let exact = [probe, "--exact"];
        assert_eq!(draw(&exact, None, settings).as_deref(), Some("0"));
        assert_eq!(draw(&exact, Some("7"), settings).as_deref(), Some("7"));
        // A filter that selects the probe without naming `bench::`, as a correctness run's
        // filter may: the draw stays fresh.
        let part = ["the_draw_of_this_process"];
        assert_eq!(draw(&part, None, settings).as_deref(), Some("unset"));
    }
}

/// `tools/run_tests.sh --bench` fixes the draw of the treap priorities when `ZED_TREAP_SEED` is
/// unset, so that a benchmark measures the same draw on every run; a correctness run does not.
#[test]
fn run_tests_fixes_the_treap_draw_for_benchmarks_only() {
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../tools/run_tests.sh");
    let text = std::fs::read_to_string(script).expect("tools/run_tests.sh");
    let lines: Vec<&str> = text
        .lines()
        .filter(|l| l.contains("ZED_TREAP_SEED=") && !l.starts_with('#'))
        .collect();
    assert_eq!(
        lines,
        [r#"[ "$run_kind" = test ] || export ZED_TREAP_SEED=${ZED_TREAP_SEED:-0}"#]
    );
}

#[test]
fn a_meter_counts_the_work_of_a_run_and_not_the_time_it_sleeps() {
    let mut meter = Meter::new();
    let spun = meter.work(|| spin(10_000_000));
    let slept = meter.work(|| std::thread::sleep(Duration::from_millis(20)));
    assert!(spun.units > slept.units, "spun {spun:?}, slept {slept:?}");
}
/// `n²` bytes, zeroed by the kernel as they are first touched, which they never are: the
/// work in user mode does not depend on `n`, only the bytes do.
fn square_of_bytes(n: usize) {
    black_box(vec![0u8; n * n]);
}

/// `n` pushes onto a list, which grows by doubling.
fn linear_bytes(n: usize) {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(black_box(i));
    }
    black_box(v);
}

#[test]
fn bytes_of_the_order_given_pass() {
    check("a list of n pushed", 10_000, linear_bytes);
    check_order("n² bytes, of order n²", 300, 2, square_of_bytes);
}

/// A passing check prints its measurements, so a pass near the limit is seen: this test
/// binary runs `bytes_of_the_order_given_pass` alone, as libtest shows a pass's output.
#[test]
fn a_passing_check_prints_its_sizes_work_bytes_and_ratios() {
    let run = this_binary_with_this_meter()
        .args([
            "--exact",
            "scaling_tests::bytes_of_the_order_given_pass",
            "--show-output",
            "--test-threads=1",
        ])
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{out}");
    assert!(out.contains("test result: ok. 1 passed"), "{out}");
    let line = out
        .lines()
        .find(|l| l.starts_with("a list of n pushed: sizes 10000 and 80000: passed: took "))
        .unwrap_or_else(|| panic!("no line of measurements in:\n{out}"));
    let unit = Meter::new().unit();
    for part in [
        format!(" {unit}, "),
        " times the work; allocated ".into(),
        " bytes, ".into(),
        format!(" times the bytes; the limit is {:.2}", limit(1)),
    ] {
        assert!(line.contains(&part), "{part:?} not in {line:?}");
    }
    assert!(
        out.contains("n² bytes, of order n²: sizes 300 and 2400: passed: took "),
        "{out}"
    );
}

/// Two checks for [`each_check_prints_a_bench_line_whose_time_grows_with_the_work`]: a spin
/// loop of 4000 passes per unit of n, and its negative control, a loop of the same length at
/// both sizes. Each run also sleeps [`SLEEP_PER_N`] per unit of n, n = 1000 at both sizes for
/// the control: the meter does not count a sleep, and the time of a run cannot be less than
/// its sleep, so the time a line prints has a lower bound that no load moves.
#[test]
fn spins_for_the_bench_line() {
    let growing = |n: usize| {
        spin(4000 * n as u64);
        std::thread::sleep(SLEEP_PER_N * n as u32);
    };
    check_instructions_only("a growing spin", 1000, 1, growing);
    check_instructions_only("a constant spin", 1000, 0, |_| growing(1000));
}

/// The sleep of a run of [`spins_for_the_bench_line`] per unit of n.
const SLEEP_PER_N: Duration = Duration::from_micros(20);

/// The fields of the bench line of `what` in `out`: n, the two times and the two counts, by
/// `instr=` where the run that printed the line counted instructions and `work=` where it did
/// not. The key is read from the line, not from this process's meter, since the run alone may
/// count by DynamoRIO where this process, which runs more than one test, does not.
fn bench_fields(out: &str, what: &str) -> (String, [u64; 2], [u64; 2]) {
    let line = out
        .lines()
        .find(|l| l.starts_with(&format!("bench {what}: sizes ")))
        .unwrap_or_else(|| panic!("no bench line of {what:?} in:\n{out}"));
    let field = |key: &str| {
        line.split(' ')
            .find_map(|f| f.strip_prefix(key))
            .unwrap_or_else(|| panic!("no {key} in {line:?}"))
            .to_owned()
    };
    let pair = |key: &str| -> [u64; 2] {
        let f = field(key);
        let (a, b) = f.split_once('/').unwrap_or_else(|| panic!("{key}{f}"));
        [a.parse().unwrap(), b.parse().unwrap()]
    };
    for key in ["bytes=", "ratio="] {
        field(key);
    }
    let key = if line.split(' ').any(|f| f.starts_with("instr=")) {
        "instr="
    } else {
        "work="
    };
    (field("n="), pair("ns="), pair(key))
}

/// Each check prints one line `bench <what> n=<n> ns=<small>/<large> instr=<small>/<large>
/// bytes=<small>/<large> ratio=<ratio>` and writes the two times to the file of
/// [`RATIOS_FILE`] (TEST-bench-split). The count of a loop 8 times as long grows, held above
/// 4 times; that of the negative control, a loop of one length at both sizes, stays under 2.
/// Each time is at least the sleep of its run, 8 times as long at 8n for the growing loop: a
/// timer that measured less than the run, or that gave the larger size the time of the
/// smaller, fails.
///
/// The test held the time to the same ratios as the count until TEST-flaky-constant-spin:
/// two runs of the constant loop took 983682 and 2177950 ns (2.21 times) at load 19, and
/// 2283732 and 5777023 ns (2.53 times) at load 32, with the same count of instructions, since
/// a run preempted or moved to a busy core takes longer by the clock. Instructions and bytes
/// decide, time is only reported; no upper bound on a time holds under load, so only the
/// lower bounds the sleeps give are held.
///
/// The run is started with this process's environment, ZED_METER_DRRUN included, not by
/// [`this_binary_with_this_meter`]: run alone with `--exact`, it counts instructions under
/// DynamoRIO even where this process does not (TEST-bench-line-grows-under-dr). Started without
/// it on Colab std1 (2 cores, no hardware counter), the run read processor time, and with the
/// rest of the lib running the counts of the growing spin were 3.29 to 3.39 million ns at n
/// and 12.2 to 12.6 million at 8n, 3.6 to 3.75 times, failing 4 of 5 runs of the lib; alone
/// they were 1.8 to 1.9 and 12.2 to 12.3 million, 6.4 to 6.7 times. A spin 4 times as long did
/// not help (12.2 to 12.7 million ns at n against 6.3 million alone, 48 million at 8n, failing
/// 3 of 5): the slowdown is in proportion to the run, as from a second thread on the same
/// physical core while the other tests run, so no length of spin makes processor time a count
/// of work. Under DynamoRIO the counts were 16015189 and 128015348, 7.993 times, in 3 of 3 runs.
/// On a machine with neither counter the run still reads processor time, as every check there
/// does.
#[test]
fn each_check_prints_a_bench_line_whose_time_grows_with_the_work() {
    let ratios = std::env::temp_dir().join(format!("zed-bench-line-{}", std::process::id()));
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "--exact",
            "scaling_tests::spins_for_the_bench_line",
            "--show-output",
            "--test-threads=1",
        ])
        .env(RATIOS_FILE, &ratios)
        .output()
        .expect("running this test binary");
    let written = std::fs::read_to_string(&ratios);
    let _ = std::fs::remove_file(&ratios);
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{out}");
    let lines = out.lines().filter(|l| l.starts_with("bench ")).count();
    assert_eq!(lines, 2, "one bench line per check in:\n{out}");
    let sleep = |n: u32| (SLEEP_PER_N * n).as_nanos() as u64;
    let (n, grows, units) = bench_fields(&out, "a growing spin");
    assert_eq!(n, "1000");
    assert!(units[1] > 4 * units[0], "{units:?}");
    assert!(
        grows[0] >= sleep(1000) && grows[1] >= sleep(8000),
        "the times of runs that sleep {} and {} ns: {grows:?}",
        sleep(1000),
        sleep(8000)
    );
    let (_, flat, units) = bench_fields(&out, "a constant spin");
    assert!(units[1] < 2 * units[0], "{units:?}");
    assert!(
        flat.iter().all(|&t| t >= sleep(1000)),
        "the times of runs that sleep {} ns: {flat:?}",
        sleep(1000)
    );
    // The file has the times as its last two columns, the same as the line's.
    let written = written.expect("the file of the ratios");
    let row = written
        .lines()
        .find(|l| l.contains("\ta growing spin: sizes "))
        .unwrap_or_else(|| panic!("no row of the growing spin in:\n{written}"));
    let columns: Vec<&str> = row.split('\t').collect();
    assert_eq!(columns.len(), 14, "{row}");
    assert_eq!(
        columns[12..],
        [grows[0].to_string(), grows[1].to_string()],
        "{row}"
    );
}

/// A benchmark run without `--exact`, as under a name filter or in a run of several tests,
/// counts instructions wherever a run of it alone does: by the hardware counter, or, where
/// there is none and DynamoRIO and its client are named, by DynamoRIO in a new process for each
/// run (BENCH-time-only-checks-by-instructions). Before, it read processor time there, held to
/// 21 and not 10.5, and its line said `work=`: on origin/main 6b511a69a on a Colab VM this
/// test's run printed `work=` (red, b22-tests8 job f3). The negative control of the benchmark
/// still fails, so a check whose runs are counted elsewhere still decides in this process. On
/// a machine with neither counter the line still says `work=`, as every check there does.
#[cfg(target_os = "linux")]
#[test]
fn a_benchmark_run_with_other_tests_counts_instructions() {
    let named = |var: &str| std::env::var_os(var).is_some_and(|v| !v.is_empty());
    let hardware = Meter::open(
        perf_event::events::Hardware::INSTRUCTIONS,
        "instructions",
        true,
    )
    .is_some();
    let software =
        named(zed_meter_settings::ZED_METER_DRRUN) && named(zed_meter_settings::ZED_METER_ICOUNT);
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "scaling_tests::bench::a_spin_run_with_other_tests",
            "--show-output",
            "--test-threads=1",
        ])
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    let err = String::from_utf8_lossy(&run.stderr);
    assert!(run.status.success(), "{out}\n{err}");
    let (n, _, units) = bench_fields(&out, "a spin run with other tests");
    assert_eq!(n, "1000");
    assert!(units[1] > 4 * units[0], "{units:?}");
    let line = out
        .lines()
        .find(|l| l.starts_with("bench a spin run with other tests: "))
        .expect("the bench line, found above");
    assert_eq!(
        line.split(' ').any(|f| f.starts_with("instr=")),
        hardware || software,
        "hardware counter: {hardware}; DynamoRIO named: {software}; {line}"
    );
}

/// The variable naming, for [`bench::a_spin_whose_phase_at_8n_is_read`], the file of the
/// benchmark's phases: its own name, since a process started for a run at 8n is not given
/// `ZED_BENCH_LIMIT_FILE`.
const PHASE_SEEN: &str = "ZED_TEST_PHASE_SEEN";

/// The phase at 8n of a benchmark starts at the run at 8n, after the inputs it reads are built,
/// and asks for its own limit, 10.5 t1: in a process started for that run too, which starts,
/// runs again under DynamoRIO, replays the test and builds its input at 8n first, all before
/// the run (author A160: the runner's limit for "each run at n and what comes before it").
/// Before, that phase was started in the process that started that one, before it did any of
/// this: on origin/main 6b511a69a on a Colab VM, where the run at 8n is in a new process, this
/// test failed with the phase at 8n started before the input was built (red, b22-tests8 job
/// f4), and benchmarks whose run at n took under 1.9 s stopped at 20 s in that phase (job f3,
/// FAIL-bench-pieces-past-limit-on-main). Where the run at 8n stays in this process (a hardware
/// counter of instructions) the input at 8n is built before the phase at n, and the test
/// passes on either.
#[test]
fn the_phase_at_8n_starts_at_its_run() {
    let (out, _) = run_reading_phases("a_spin_whose_phase_at_8n_is_read");
    assert!(
        out.lines()
            .any(|l| l.starts_with("bench a spin whose phase at 8n is read: ")),
        "{out}"
    );
}

/// [`hold_in_phases`] counts at 8n in a phase of its own, started after the count at n, that
/// asks for a limit of its own, and then starts a phase with the runner's limit
/// (FAIL-bench-first-phase-past-20s-l0126-l0129). Negative control: with `hold_in_phases`
/// starting no phase, the benchmark finds no file of the phases and fails.
#[test]
fn a_hold_in_phases_counts_at_8n_in_a_phase_of_its_own() {
    // libtest shows the captured output of a passing test, `eprintln!`'s too, on stdout.
    let (out, err) = run_reading_phases("a_count_held_in_phases");
    assert!(
        format!("{out}\n{err}")
            .lines()
            .any(|l| l.starts_with("a count held in phases: passed: 1000 and 8000 passes")),
        "{out}\n{err}"
    );
}

/// [`ran_alone_in_a_new_process`] runs a test whose meter counts no instructions again, alone, in
/// a new process of this binary, and the caller measures only there
/// (FAIL-casts-difference-of-processor-times). Run with the binary's other tests, or under a
/// filter, the body below runs in the new process; run alone with `--exact`, it runs here.
/// Negative control: without the call, a run of the whole binary measures in this process, beside
/// the other tests, and the assertion fails.
#[test]
fn a_meter_of_processor_time_measures_only_in_a_process_running_the_test_alone() {
    let meter = Meter {
        read: Box::new(|| 0),
        unit: "ns of processor time",
        instructions: false,
        fresh: false,
        elsewhere: false,
    };
    if ran_alone_in_a_new_process(&meter) {
        // A helper called again in the same test returns too (BENCH-self-counted-meters-...).
        assert!(ran_alone_in_a_new_process(&meter));
        return;
    }
    // In the process that runs the test alone, every call measures here.
    assert!(!ran_alone_in_a_new_process(&meter));
    let thread = std::thread::current();
    let test = thread.name().expect("a test's thread has its name");
    assert!(
        runs_alone(test),
        "{test} measured in a process that may run other tests"
    );
}

/// Runs the benchmark `scaling_tests::bench::<test>` of this binary alone, with
/// `ZED_BENCH_LIMIT_FILE` and [`PHASE_SEEN`] naming one file, and gives its standard output and
/// standard error once it has passed.
fn run_reading_phases(test: &str) -> (String, String) {
    let file = std::env::temp_dir().join(format!("zed-phases-{}-{test}", std::process::id()));
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            &format!("scaling_tests::bench::{test}"),
            "--exact",
            "--show-output",
            "--test-threads=1",
        ])
        .env(BENCH_LIMIT_FILE, &file)
        .env(PHASE_SEEN, &file)
        .output()
        .expect("running this test binary");
    // The file is the test's own, by this process's id; the benchmark writes it at each phase.
    let removed = std::fs::remove_file(&file);
    let out = String::from_utf8_lossy(&run.stdout).into_owned();
    let err = String::from_utf8_lossy(&run.stderr).into_owned();
    assert!(run.status.success(), "{out}\n{err}");
    removed.expect("removing the file of the phases");
    (out, err)
}

#[test]
fn bytes_a_power_of_n_above_the_order_given_fail_though_the_work_does_not() {
    let failed = std::panic::catch_unwind(|| check("n² bytes", 1000, square_of_bytes));
    let message = *failed.unwrap_err().downcast::<String>().unwrap();
    assert!(message.contains("64.0 times the bytes"), "{message}");
    check_instructions_only("n² bytes", 1000, 1, square_of_bytes);
}

#[test]
fn the_bytes_of_a_thread_a_run_starts_by_on_a_thread_count() {
    let on_a_thread = |n| on_a_thread(1 << 20, || square_of_bytes(n));
    assert!(fails(|| check("n² bytes on a thread", 1000, on_a_thread)));
    // Only Linux has a meter of processor time.
    #[cfg(target_os = "linux")]
    {
        let cpu = &mut Meter::of_cpu_time();
        assert!(fails(|| check_by(
            cpu,
            Measures::Both,
            "n² bytes on a thread, by time",
            1000,
            1,
            on_a_thread
        )));
    }
}

// Off Linux the counts are of the whole process, so the threads beside a run add to them.
#[cfg(target_os = "linux")]
#[test]
fn the_bytes_of_a_run_do_not_depend_on_tests_running_beside_it() {
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|s| {
        // Four threads beside the measured one, as tests running beside it are: none of them
        // started by it.
        for _ in 0..4 {
            s.spawn(|| {
                while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                    black_box(vec![0u8; 100]);
                }
            });
        }
        let measured = s.spawn(|| {
            let mut meter = Meter::new();
            (0..20)
                .map(|_| meter.work(|| linear_bytes(1000)).bytes)
                .collect::<Vec<u64>>()
        });
        let bytes = measured.join().unwrap();
        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        // 1000 words in lists of 4, 8, ..., 1024 of them.
        assert_eq!(bytes, vec![8 * (2048 - 4); 20]);
    });
}

/// The bytes `alone` returns, which a comparison compares, are those of the run whatever
/// threads start and end beside it: the start of `alone`'s own thread, whose bookkeeping in
/// std depends on the threads alive, is not in them.
#[cfg(target_os = "linux")]
#[test]
fn the_bytes_of_a_run_alone_do_not_depend_on_threads_starting_beside_it() {
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|s| {
        // Eight threads beside the measured one, each starting threads of its own and
        // allocating on them, so the set of threads alive changes all the time.
        for _ in 0..8 {
            s.spawn(|| {
                while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                    std::thread::spawn(|| black_box(vec![0u8; 100]))
                        .join()
                        .unwrap();
                }
            });
        }
        // Measured on a thread none of them started, as a test beside them is.
        let measured =
            s.spawn(|| -> Vec<u64> { (0..50).map(|_| alone(&|| linear_bytes(1000)).0).collect() });
        let bytes = measured.join().unwrap();
        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        // 1000 words in lists of 4, 8, ..., 1024 of them.
        assert_eq!(bytes, vec![8 * (2048 - 4); 50]);
    });
}

/// The message of the panic of `run`, which must panic.
fn message_of(run: impl FnOnce()) -> String {
    let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(run));
    *failed.unwrap_err().downcast::<String>().unwrap()
}

#[test]
fn a_run_alone_counts_the_bytes_its_thread_allocates() {
    let before = zed_alloc_count::allocated();
    // 1000 words in lists of 4, 8, ..., 1024 of them.
    assert_eq!(alone(&|| linear_bytes(1000)).0, 8 * (2048 - 4));
    assert!(zed_alloc_count::allocated() - before >= 8 * (2048 - 4));
}

#[test]
fn a_larger_run_that_allocates_no_bytes_on_its_thread_is_refused() {
    let message = message_of(|| check("linear work", 1000, |n| work(n, 1, 10)));
    assert!(
        message.contains("allocated no bytes, on its thread"),
        "{message}"
    );
}

/// A run that does its work on a thread it starts with a bare `std::thread::spawn`, or on a
/// thread that one starts, counts those threads' bytes; one that works on its own thread
/// counts the same as before.
#[test]
fn the_bytes_of_a_bare_thread_a_run_starts_count() {
    // 1000 words in lists of 4, 8, ..., 1024 of them.
    let list = 8 * (2048 - 4);
    assert_eq!(alone(&|| linear_bytes(1000)).0, list);
    let spawned = || std::thread::spawn(|| linear_bytes(1000)).join().unwrap();
    let joined = alone(&spawned).0;
    assert!(joined >= list, "{joined}");
    // The list is allocated on the second thread down only. The starts of the threads differ
    // by the other threads alive (see zed-alloc-count), so the two counts are not compared.
    let nested = alone(&|| std::thread::spawn(spawned).join().unwrap()).0;
    assert!(nested >= list, "{nested}");
    let bare = |n| {
        std::thread::spawn(move || square_of_bytes(n))
            .join()
            .unwrap()
    };
    let message = message_of(|| check("n² bytes on a bare thread", 1000, bare));
    assert!(message.contains("times the bytes"), "{message}");
}

thread_local! {
    /// Whether a run on this thread has filled its memo, as zed-kernel's tables are filled.
    static FILLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Fails if the runs share a thread, for then each run after the first finds the memo the
/// first filled (F44). Every run made is counted, on the meter this machine gives, both sizes
/// in this process. The negative control: a memo the process keeps, which every run after the
/// first finds filled. Until TEST-scaling-lib-no-counter (2026-11-22) the test expected
/// [`Meter::runs`] runs, the most a meter of processor time makes, where a comparison that
/// passes its first measurement makes [`TIME_RUNS`] of each size: 10 found the memo empty
/// against 30 expected on every Colab VM.
#[test]
fn each_run_starts_with_empty_thread_memos() {
    use std::sync::atomic::AtomicBool;
    let mut meter = Meter::new();
    meter.fresh = false;
    let (runs, fresh) = memo_runs(&mut meter, || FILLED.replace(true));
    assert!(runs >= 2, "{runs} runs");
    assert_eq!(fresh, runs);
    static KEPT: AtomicBool = AtomicBool::new(false);
    let (runs, fresh) = memo_runs(&mut meter, || KEPT.swap(true, Relaxed));
    assert!(runs >= 2, "{runs} runs");
    assert_eq!(fresh, 1);
}

/// How many runs a comparison by `meter` made, and in how many of them `filled`, which marks a
/// memo filled and says whether it was filled before, found it empty. The limit no ratio is over
/// makes the count the same at any load.
fn memo_runs(meter: &mut Meter, filled: impl Fn() -> bool + Sync) -> (usize, usize) {
    use std::sync::atomic::AtomicUsize;
    let (runs, fresh) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let run = || {
        runs.fetch_add(1, Relaxed);
        if !filled() {
            fresh.fetch_add(1, Relaxed);
        }
    };
    compare_by(
        meter,
        Measures::WorkOnly,
        None,
        "memo runs",
        Bound::Given(f64::INFINITY, "runs counted, not compared"),
        run,
        run,
    );
    (runs.into_inner(), fresh.into_inner())
}

/// [`fresh_inputs_by`] holds one input or output at a time, and builds and releases each outside
/// the measured runs: not the 30 inputs of both sizes that the tests building every input first
/// held on processor time (MEM-l0126-40gb: 37,066,996 kB for one benchmark of l01_26 on a VM
/// without a counter of instructions), nor a batch of [`TIME_RUNS`] (11,022,424 kB). The bytes
/// of an input built inside a run would count in the run's bytes, 8 times the input at 8n, and
/// still pass a linear check, so the builds are counted too: one per run, numbered from 0 at
/// each size; and an input released inside a run would put its release in the measure.
#[test]
fn fresh_inputs_are_held_one_at_a_time_and_built_outside_the_runs() {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    static LIVE: AtomicUsize = AtomicUsize::new(0);
    static MOST: AtomicUsize = AtomicUsize::new(0);
    static IN_RUN: AtomicUsize = AtomicUsize::new(0);
    static BUILT_IN_RUN: AtomicUsize = AtomicUsize::new(0);
    static DROPPED_IN_RUN: AtomicUsize = AtomicUsize::new(0);
    static RUNS: AtomicUsize = AtomicUsize::new(0);
    struct Input(Vec<u8>);
    impl Drop for Input {
        fn drop(&mut self) {
            if IN_RUN.load(Relaxed) > 0 {
                DROPPED_IN_RUN.fetch_add(1, Relaxed);
            }
            LIVE.fetch_sub(1, Relaxed);
        }
    }
    let built = Mutex::new(Vec::new());
    let make = |k: usize, i: usize| {
        built.lock().unwrap().push((k, i));
        if IN_RUN.load(Relaxed) > 0 {
            BUILT_IN_RUN.fetch_add(1, Relaxed);
        }
        let live = LIVE.fetch_add(1, Relaxed) + 1;
        MOST.fetch_max(live, Relaxed);
        Input(vec![1; k])
    };
    let run = |_: usize, input: Input| {
        IN_RUN.fetch_add(1, Relaxed);
        RUNS.fetch_add(1, Relaxed);
        black_box(input.0.iter().map(|b| b ^ 1).collect::<Vec<u8>>());
        IN_RUN.fetch_sub(1, Relaxed);
        input
    };
    let n = 200_000;
    fresh_inputs_by(
        &mut Meter::of_cpu_time(),
        Measures::Both,
        Some(n),
        "a pass over a fresh input",
        Bound::Order(1),
        (n, FACTOR * n),
        &make,
        &run,
    );
    assert_eq!(LIVE.load(Relaxed), 0, "every input released");
    assert_eq!(MOST.load(Relaxed), 1, "inputs held at once");
    let built = built.into_inner().unwrap();
    assert_eq!(built.len(), RUNS.load(Relaxed), "one input per run");
    for k in [n, FACTOR * n] {
        let numbers: Vec<usize> = built.iter().filter(|b| b.0 == k).map(|b| b.1).collect();
        let from_0: Vec<usize> = (0..numbers.len()).collect();
        assert_eq!(numbers, from_0, "the inputs of size {k} numbered from 0");
    }
    assert_eq!(
        BUILT_IN_RUN.load(Relaxed),
        0,
        "an input built while a run ran"
    );
    assert_eq!(
        DROPPED_IN_RUN.load(Relaxed),
        0,
        "an input released while a run ran"
    );
}

/// A quadratic pass behind a memo the process keeps for all threads, keyed by size, as a
/// table not keyed by thread is: the first run of each size does `n²` work and allocates `n²`
/// bytes, every later run finds the size in the memo and does `n`. The least of several runs
/// would see only the later runs, 8 times at both measures; the first runs are 64 times. On a
/// count of instructions each size runs once, so the runs measured are the first (author A160,
/// 2026-11-20); processor time takes the fastest of [`TIME_RUNS`] and holds the bytes of the
/// first runs.
#[test]
fn a_memo_that_outlives_a_thread_does_not_hide_the_work_of_the_first_runs() {
    static DONE: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());
    let memoized = |n: usize| {
        let done = DONE.lock().unwrap().contains(&n);
        if done {
            work(n, 1, 2);
            linear_bytes(n);
        } else {
            work(n, 2, 2);
            black_box(vec![1u8; n * n]);
            DONE.lock().unwrap().push(n);
        }
    };
    let message = message_of(|| check("a memoized quadratic", 300, memoized));
    let instructions = Meter::new().instructions;
    // The memo's own `Vec` adds a few bytes to the n² of each first run.
    let held = if instructions {
        ": allocated "
    } else {
        ": the first runs allocated "
    };
    assert!(
        message.contains(held) && message.contains(" bytes, 64.0 times the bytes"),
        "{message}"
    );
    // Once both sizes are in the memo, every run is linear and passes. Filled here, before the
    // check, so that the new process of a run at 8n fills it too: there the check before ran
    // its run at n only (see `compare_by`).
    memoized(300);
    memoized(2400);
    check("a memoized quadratic, memo full", 300, memoized);
    // The work of the first runs, without their bytes, on a count of instructions; processor
    // time holds only their bytes (see `compare_by`).
    if instructions {
        let message = message_of(|| check_instructions_only("work only", 200, 1, memoized));
        // About 61 times: the work has a linear part beside the quadratic.
        assert!(
            message.starts_with("work only: sizes 200 and 1600: took ")
                && message.contains(" times the work in "),
            "{message}"
        );
    }
}

/// A made-up set-up of order `n²` hidden in a memo the process keeps for all threads: a table
/// built once, by the first run, for that run's size, and read by every later run, as the
/// grammar or an interner is (TEST-scaling-cold-shared-memo). In one process the run at n built
/// it and the run at 8n found it built: `2 × 300²` and `20 × 300` passes against `20 × 2400`,
/// 0.26 times the work, which passed. With the run at 8n in a new process it builds the table
/// at its own size, `2 × 2400²` passes more, about 62 times the work.
#[test]
fn a_set_up_hidden_in_a_memo_the_process_keeps_is_counted_at_8n() {
    static TABLE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    let run = |n: usize| {
        black_box(*TABLE.get_or_init(|| {
            work(n, 2, 2);
            n
        }));
        work(n, 1, 20);
        linear_bytes(n);
    };
    // A meter of processor time runs both sizes in this process and keeps the hole (see
    // `compare_by`).
    if !Meter::new().fresh {
        return;
    }
    let message = message_of(|| check("a hidden quadratic set-up", 300, run));
    assert!(
        message.starts_with("a hidden quadratic set-up: sizes 300 and 2400: took ")
            && message.contains(" times the work in "),
        "{message}"
    );
}

/// A set-up of fixed size that the process builds once and keeps passes: both runs pay it, the
/// run at n in this process and the run at 8n in the new one. A second check of the same test
/// finds it built in both, since the new process runs the first check's run at n before it (see
/// `compare_by`): without that its run at 8n would pay the set-up alone, `2000²` passes against
/// `20 × 300`, and fail.
#[test]
fn a_fixed_set_up_kept_by_the_process_passes_in_each_check_of_a_test() {
    static TABLE: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    let run = |n: usize| {
        TABLE.get_or_init(|| work(2000, 2, 1));
        work(n, 1, 20);
        linear_bytes(n);
    };
    check("a fixed set-up, first check", 300, run);
    check("a fixed set-up, second check", 300, run);
}

/// The table of fixed size that [`a_set_up_another_test_built_a_fills_the_table`] builds and
/// [`a_set_up_another_test_built_b_is_paid_at_both_sizes`] reads.
static BUILT_BY_ANOTHER_TEST: std::sync::OnceLock<()> = std::sync::OnceLock::new();

/// Builds [`BUILT_BY_ANOTHER_TEST`]: `2000²` passes, against `20 × 300` for the run at n of the
/// check that reads it.
fn build_the_table_of_another_test() {
    BUILT_BY_ANOTHER_TEST.get_or_init(|| work(2000, 2, 1));
}

/// Fills the table, as an earlier test in the same process fills the grammar.
#[test]
fn a_set_up_another_test_built_a_fills_the_table() {
    build_the_table_of_another_test();
}

/// A linear run that builds the table on first use. Run alone, both runs pay the table. Run
/// after [`a_set_up_another_test_built_a_fills_the_table`] in one process, the run at n found it
/// built and the run at 8n, in a new process, paid it: `2000² + 20 × 2400` passes against
/// `20 × 300`, and the check failed (FAIL-lr4-bench-annotation-update).
#[test]
fn a_set_up_another_test_built_b_is_paid_at_both_sizes() {
    let run = |n: usize| {
        build_the_table_of_another_test();
        work(n, 1, 20);
        linear_bytes(n);
    };
    check("a set-up another test built", 300, run);
}

/// Both tests above in one process, on one thread, in order of their names, as a run of the
/// whole binary or of a filter matching several tests runs them: the check passes, since its
/// run at n moves to a new process too (see `compare_by`). Only a count of instructions runs
/// the run at 8n in a new process.
#[test]
fn a_check_after_another_test_built_its_set_up_passes() {
    if !Meter::new().fresh {
        return;
    }
    let run = fresh_command(&std::env::current_exe().expect("this test binary"))
        .args([
            "scaling_tests::a_set_up_another_test_built_",
            "--test-threads=1",
        ])
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success() && out.contains("test result: ok. 2 passed"),
        "{out}"
    );
}

/// The variable naming the file each build of [`a_check_of_built_inputs_logs_its_builds`]
/// appends `<pid> <size>` to; set only by [`check_inputs_builds_only_the_sizes_each_process_runs`].
const BUILDS_LOG: &str = "ZED_SCALING_TEST_BUILDS_LOG";

/// Two checks of [`check_inputs`], sizes 100 and 200, each input built logged to the file
/// [`BUILDS_LOG`] names, when it is set (the processes of the checks inherit it).
#[test]
fn a_check_of_built_inputs_logs_its_builds() {
    let make = |n: usize| {
        if let Ok(path) = std::env::var(BUILDS_LOG) {
            use std::io::Write;
            let mut log = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(path)
                .expect("opening the log of builds");
            writeln!(log, "{} {n}", std::process::id()).expect("logging a build");
        }
        n
    };
    for n in [100, 200] {
        check_inputs("an input built at the sizes run", n, make, |&k: &usize| {
            work(k, 1, 20);
            linear_bytes(k);
        });
    }
}

/// [`check_inputs`] builds in each process only the inputs it runs (BENCH-follow-group-near-60s):
/// [`a_check_of_built_inputs_logs_its_builds`] run alone builds 100 and 200 in its own process,
/// 800 in the process of the run at 8n of its first check, and 100 (the replay of the first
/// check's run at n) and 1600 in that of its second: 5 inputs, where [`inputs`] built both sizes
/// of every check reached in every process, 10. Only a count of instructions runs the run at 8n
/// in a new process.
#[test]
fn check_inputs_builds_only_the_sizes_each_process_runs() {
    if !Meter::new().fresh {
        return;
    }
    let log = crate::scratch::scratch("check-inputs-builds.log");
    std::fs::create_dir_all(log.parent().unwrap()).unwrap();
    std::fs::write(&log, "").unwrap();
    let me = "scaling_tests::a_check_of_built_inputs_logs_its_builds";
    let run = fresh_command(&std::env::current_exe().expect("this test binary"))
        .args([me, "--exact", "--test-threads=1"])
        .env(BUILDS_LOG, &log)
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success() && out.contains("test result: ok. 1 passed"),
        "{out}"
    );
    let builds = builds_by_process(&std::fs::read_to_string(&log).unwrap());
    assert_eq!(builds, [vec![100, 200], vec![100, 1600], vec![800]]);
}

/// The sizes of each process's builds in a log of `<pid> <size>` lines, each process's in the
/// order logged, the processes sorted by their sizes.
fn builds_by_process(log: &str) -> Vec<Vec<usize>> {
    let mut by_pid = std::collections::BTreeMap::<&str, Vec<usize>>::new();
    for line in log.lines() {
        let (pid, size) = line.split_once(' ').expect("a line `<pid> <size>`");
        by_pid
            .entry(pid)
            .or_default()
            .push(size.parse().expect("a size"));
    }
    let mut sizes: Vec<_> = by_pid.into_values().collect();
    sizes.sort();
    sizes
}

/// The passes of the loops of [`counted_spin`] on every thread of the process; only
/// `a_meter_measures_by_any_counter_it_is_given` runs them.
static SPUN: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// A counter of the passes of [`counted_spin`] in the whole process, as the counters of macOS
/// and Windows count the whole process, in passes of a loop rather than instructions.
fn spun_counter() -> Read {
    Box::new(|| SPUN.load(std::sync::atomic::Ordering::Relaxed))
}

/// `n` passes of a loop, counted by [`spun_counter`].
fn counted_spin(n: u64) {
    spin(n);
    SPUN.fetch_add(n, std::sync::atomic::Ordering::Relaxed);
}

/// The counter that moves is taken, with its unit, past one that reads 0, as macOS takes
/// `ri_cycles` where `ri_instructions` reads 0; none moving gives no meter.
#[test]
fn a_meter_takes_the_first_counter_that_moves() {
    // A counter that moves by one at each read stands in for one that counts the work.
    let moving = || {
        let mut passes = 0u64;
        Box::new(move || {
            passes += 1;
            passes
        }) as Read
    };
    let zero = || Box::new(|| 0u64) as Read;
    let meter =
        Meter::first_that_moves([(zero(), "instructions", true), (moving(), "cycles", false)])
            .expect("the second counter moves");
    assert_eq!(meter.unit(), "cycles");
    assert_eq!(meter.runs(), (TIME_RUNS * TRIES, TIME_RUNS * TRIES));
    let meter =
        Meter::first_that_moves([(moving(), "instructions", true)]).expect("the counter moves");
    assert_eq!(meter.runs(), (1, 1));
    assert!(
        Meter::first_that_moves([(zero(), "instructions", true), (zero(), "cycles", false)])
            .is_none()
    );
}

/// A meter of a counter that only `counted_spin` moves measures the passes of a run, whatever
/// counter it reads, and compares the orders of two runs as a meter of instructions does.
#[test]
fn a_meter_measures_by_any_counter_it_is_given() {
    let mut meter = Meter {
        read: spun_counter(),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    };
    assert_eq!(meter.work(|| counted_spin(1234)).units, 1234);
    let linear = |n: usize| counted_spin(10 * n as u64);
    check_by(
        &mut meter,
        Measures::WorkOnly,
        "linear passes",
        1000,
        1,
        linear,
    );
    let quadratic = |n: usize| counted_spin((n * n) as u64);
    let message = message_of(|| {
        check_by(
            &mut meter,
            Measures::WorkOnly,
            "quadratic passes",
            1000,
            1,
            quadratic,
        )
    });
    assert!(
        message.contains(
            "quadratic passes: sizes 1000 and 8000: took 1000000 and 64000000, 64.00 times the \
             work in passes"
        ),
        "{message}"
    );
}

/// Compares a small run that adds `small(i)` passes to `passes` at its `i`th call with a large
/// one that adds `large(i)`, by `meter`, which must read `passes`; gives the message if the
/// comparison fails, and how often each size ran.
fn compare_counted(
    meter: &mut Meter,
    passes: &'static std::sync::atomic::AtomicU64,
    small: impl Fn(usize) -> u64 + Sync,
    large: impl Fn(usize) -> u64 + Sync,
) -> (Option<String>, usize, usize) {
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    let (smalls, larges) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compare_by(
            meter,
            Measures::WorkOnly,
            None,
            "counted passes",
            Bound::Order(1),
            || _ = passes.fetch_add(small(smalls.fetch_add(1, Relaxed)), Relaxed),
            || _ = passes.fetch_add(large(larges.fetch_add(1, Relaxed)), Relaxed),
        )
    }));
    let message = failed
        .err()
        .map(|e| *e.downcast::<String>().expect("a message"));
    (message, smalls.into_inner(), larges.into_inner())
}

/// A meter of a count that changes with load, processor time or cycles, here given a counter
/// that does not. A comparison under the limit stops after its first measurement, the fastest
/// of [`TIME_RUNS`] runs of each size; one over it in its first measurement only is measured
/// again and passes; one over it in every measurement takes all [`TRIES`], the runs
/// [`Meter::runs`] gives, and fails. On a machine with an instruction counter no other test
/// takes these paths.
#[test]
fn a_meter_of_a_count_that_changes_with_load_measures_up_to_three_times() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
        unit: "ns",
        instructions: false,
        fresh: false,
        elsewhere: false,
    };
    assert_eq!(meter.runs(), (TIME_RUNS * TRIES, TIME_RUNS * TRIES));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 8000);
    assert_eq!((message, smalls, larges), (None, TIME_RUNS, TIME_RUNS));
    // 64 times in the runs of the first measurement, 8 times after.
    let (message, smalls, larges) = compare_counted(
        &mut meter,
        &PASSES,
        |_| 1000,
        |i| if i < TIME_RUNS { 64_000 } else { 8000 },
    );
    assert_eq!(
        (message, smalls, larges),
        (None, 2 * TIME_RUNS, 2 * TIME_RUNS)
    );
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 64_000);
    assert_eq!((smalls, larges), meter.runs());
    let message = message.expect("64 times fails");
    assert!(
        message.contains(
            "took 1000 and 64000, 64.00 times the work; then 1000 and 64000, 64.00 times the \
             work; then 1000 and 64000, 64.00 times the work in ns"
        ),
        "{message}"
    );
}

/// A ratio at the limit or over it fails on every meter, and one just under it passes
/// (FAIL-scaling-check-passes-over-limit). Until then a meter of processor time or cycles
/// passed up to 21, `LIMIT` × `TIME_ALLOWANCE`, and printed "the limit is 10.50": s_01f's
/// `untyped_calls_scale_with_the_number_of_files` printed "passed" at 10.54 on a Colab VM
/// (b22-small10, 2026-11-23). The counter here is one only the runs move, so the ratios are
/// exact: 10540 against 1000 is 10.54, and 10490 against 1000 is 10.49, the negative control.
/// On a meter of processor time 10.54 is measured all [`TRIES`] times before it fails.
#[test]
fn a_ratio_over_the_limit_fails_on_every_meter() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    for instructions in [false, true] {
        let mut meter = Meter {
            read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
            unit: "ns",
            instructions,
            fresh: false,
            elsewhere: false,
        };
        let (message, _, _) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 10_490);
        assert_eq!(message, None, "10.49 on instructions: {instructions}");
        for over in [10_500, 10_540] {
            let (message, smalls, larges) =
                compare_counted(&mut meter, &PASSES, |_| 1000, |_| over);
            let message = message.unwrap_or_else(|| {
                panic!("{over} against 1000 passed on instructions: {instructions}")
            });
            let ratio = format!("{:.2}", over as f64 / 1000.0);
            assert!(
                message.contains(&format!("1000 and {over}, {ratio} times the work")),
                "{message}"
            );
            assert_eq!((smalls, larges), meter.runs());
        }
    }
}

/// On a count of instructions a check runs each size once, n first, and measures once
/// (author A160, 2026-11-20): the run at 8n is never run again, the one at n never warmed up.
/// A ratio under the limit passes; one over it fails on its one measurement.
#[test]
fn a_count_of_instructions_runs_each_size_once() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    };
    assert_eq!(meter.runs(), (1, 1));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 8000);
    assert_eq!((message, smalls, larges), (None, 1, 1));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 64_000);
    assert_eq!((smalls, larges), (1, 1));
    let message = message.expect("64 times fails");
    assert!(
        message.contains("counted passes: took 1000 and 64000, 64.00 times the work in passes"),
        "{message}"
    );
}

/// A meter of processor time or cycles takes the fastest of [`TIME_RUNS`] runs of each size,
/// and the first run of each size can fill a memo the later runs find full: their bytes are
/// held to the limit, from the runs measured, with no run added. Here the first run at 8n
/// allocates 64 times the bytes of the run at n and the later ones 8 times, so the fastest
/// runs pass and the first runs fail; a first run at 8n of 8 times passes (negative control).
#[test]
fn a_meter_of_a_count_that_changes_with_load_holds_the_bytes_of_the_first_runs() {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "ns",
        instructions: false,
        fresh: false,
        elsewhere: false,
    };
    let mut first_large = |first: usize| {
        let larges = AtomicUsize::new(0);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compare_by(
                &mut meter,
                Measures::Both,
                None,
                "counted bytes",
                Bound::Order(1),
                || {
                    PASSES.fetch_add(1000, Relaxed);
                    black_box(vec![0u8; 1000]);
                },
                || {
                    PASSES.fetch_add(8000, Relaxed);
                    let i = larges.fetch_add(1, Relaxed);
                    black_box(vec![0u8; if i == 0 { first } else { 8000 }]);
                },
            )
        }))
        .map_err(|e| *e.downcast::<String>().expect("a message"))
    };
    assert_eq!(first_large(8000), Ok(()));
    let message = first_large(64_000).expect_err("the first runs are 64 times");
    assert!(
        message.starts_with(
            "counted bytes: the first runs allocated 1000 and 64000 bytes, 64.0 times the bytes"
        ),
        "{message}"
    );
}

/// A method that fills a memo on its first run at each size and allocates nothing on later
/// runs does work of order n, and its first runs (8000 bytes at n, 64000 at 8n) are 8 times
/// apart. From 26e51b07b (TEST-scaling-runs, `Meter::repeats` gives (1, 1) for instructions)
/// to FAIL-scaling-cold-8n-bytes the run at 8n was measured only once, cold, while the run at
/// n was measured after the warm-up: 0 bytes against 64000, so the check failed, as did 20
/// checks of l01_23_subtyping (setop, witnesses, refusals and two of scaling), for example
/// "diagonal parity contradiction: sizes 9 and 72: allocated 0 and 134376 bytes, 134376.0
/// times the bytes". From then to A160 the run at 8n over the limit was run again, warm; since
/// A160 (2026-11-20) each size runs once, so both runs measured are the first of their size
/// (8000 bytes against 64000).
#[test]
fn a_memo_filled_by_the_first_run_of_each_size_scales_as_its_first_runs_do() {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    };
    let (small_filled, large_filled) = (AtomicBool::new(false), AtomicBool::new(false));
    compare_by(
        &mut meter,
        Measures::Both,
        None,
        "a memo filled once at each size",
        Bound::Order(1),
        || {
            PASSES.fetch_add(1000, Relaxed);
            if !small_filled.swap(true, Relaxed) {
                black_box(vec![0u8; 8000]);
            }
        },
        || {
            PASSES.fetch_add(8000, Relaxed);
            if !large_filled.swap(true, Relaxed) {
                black_box(vec![0u8; 64_000]);
            }
        },
    );
}

/// A method whose first run of each size does work the later runs skip, as one filling a
/// memo in its input does, is measured on a count of instructions in one state at both sizes:
/// the first run of each (author A160, 2026-11-20). Here the cold runs are 1250 and 12,000
/// passes, 9.6 times, and the warm ones 1000 and 8000. Held against the warm run at n, as the
/// cold run at 8n was from TEST-scaling-runs to A160, it would be 12 times and fail; held
/// against the cold run at n it passes. A cold run at 8n of 13,200 passes, 10.56 times the cold
/// run at n, fails (negative control). From 2026-11-15 to A160 a cold run at 8n at the note of
/// [`PREFERRED`] or over the limit was run again (PERF-permission-reverse-first-run).
#[test]
fn the_first_run_of_each_size_is_measured_against_the_other() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    };
    let cold_small = |i: usize| if i == 0 { 1250 } else { 1000 };
    let cold_large = |i: usize| if i == 0 { 12_000 } else { 8000 };
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, cold_small, cold_large);
    assert_eq!((message, smalls, larges), (None, 1, 1));
    let over = |i: usize| if i == 0 { 13_200 } else { 8000 };
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, cold_small, over);
    assert_eq!((smalls, larges), (1, 1));
    let message = message.expect("10.56 times fails");
    assert!(
        message.contains("took 1250 and 13200, 10.56 times the work in passes"),
        "{message}"
    );
}

/// A comparison of two runs that are not one pass at n and 8n holds its ratio to the limit
/// given: a ratio equal to it passes, one over it fails with the reason given.
#[test]
fn a_comparison_to_a_given_limit_passes_at_the_limit_and_fails_over_it() {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "passes",
        instructions: true,
        fresh: false,
        elsewhere: false,
    };
    let given = |meter: &mut Meter, second: u64| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compare_by(
                meter,
                Measures::WorkOnly,
                None,
                "two methods",
                Bound::Given(3.0, "the second method is at most 3 times the first"),
                || _ = PASSES.fetch_add(1000, Relaxed),
                || _ = PASSES.fetch_add(second, Relaxed),
            )
        }))
        .map_err(|e| *e.downcast::<String>().expect("a message"))
    };
    assert_eq!(given(&mut meter, 3000), Ok(()));
    let message = given(&mut meter, 3001).expect_err("over the limit");
    assert_eq!(
        message,
        "two methods: took 1000 and 3001, 3.00 times the work in passes; the second method is \
         at most 3 times the first"
    );
}

#[test]
fn one_test_at_a_time_is_read_from_the_options_of_libtest_or_its_variable() {
    let args = |a: &[&str]| -> Vec<String> {
        std::iter::once("steps")
            .chain(a.iter().copied())
            .map(String::from)
            .collect()
    };
    assert!(one_test_at_a_time(args(&["--test-threads=1"]), None));
    assert!(one_test_at_a_time(
        args(&["scaling", "--test-threads", "1"]),
        None
    ));
    assert!(one_test_at_a_time(args(&[]), Some("1")));
    assert!(!one_test_at_a_time(args(&[]), None));
    assert!(!one_test_at_a_time(args(&[]), Some("4")));
    assert!(!one_test_at_a_time(args(&["--test-threads=8"]), None));
    // The option overrides the variable, either way.
    assert!(!one_test_at_a_time(args(&["--test-threads=2"]), Some("1")));
    assert!(one_test_at_a_time(
        args(&["--test-threads", "1"]),
        Some("8")
    ));
}

mod bench;

/// A run at 1x of over 20 s / 10.5 asks for more than the runner's 20 s for its run at 8n
/// (author P214): 2 s asks for 21 s, which tools/bench_limit.sh takes over its base of 20 s.
/// Each phase is written with its own start and limit (author A160, 2026-11-20), and a later,
/// smaller phase replaces a larger one, since each phase has its own limit; the phase after a
/// run at 8n asks for 0, the runner's limit.
#[test]
fn bench_limit_a_1x_over_20_s_over_10_5_raises_the_limit() {
    assert_eq!(bench_limit_ms(2_000_000_000), 21_000);
    assert!(bench_limit_ms(1_904_000_000) < 20_000 && bench_limit_ms(1_905_000_000) > 20_000);
    let path = crate::scratch::scratch("bench-limit-raised");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    let at = |ms: u64| std::time::UNIX_EPOCH + Duration::from_millis(ms);
    write_bench_phase(&path, at(1_795_000_000_123), bench_limit_ms(2_000_000_000));
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "1795000000123 21000\n"
    );
    write_bench_phase(&path, at(1_795_000_021_000), 0);
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "1795000021000 0\n");
    write_bench_phase(&path, at(1_795_000_022_000), bench_limit_ms(1_000_000_000));
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "1795000022000 10500\n"
    );
}

/// A benchmark whose first run at 1x takes under 20 s / 10.5 asks for less than 20 s, so the
/// runner's 20 s holds: 1 s asks for 10.5 s.
#[test]
fn bench_limit_a_1x_under_20_s_over_10_5_keeps_20_s() {
    assert_eq!(bench_limit_ms(1_000_000_000), 10_500);
    assert_eq!(bench_limit_ms(1), 1);
    assert!(bench_limit_ms(1_904_000_000) < 20_000);
}

/// The variable that gives a process of this test binary its part in
/// [`a_fresh_child_ends_when_its_parent_is_killed`]: `parent` or `child`.
const ORPHAN_ROLE: &str = "ZED_SCALING_ORPHAN_ROLE";

/// A process [`fresh_command`] starts for a run at 8n ends when the process that started it is
/// killed. On 2026-11-20 tools/bench_limit.sh stopped a benchmark at its limit by killing the
/// test binary only, and its process for the run at 8n (l01_39a_bit_words, rung 2, sizes 600 and
/// 4800) ran on under systemd for 19 minutes, holding 67 to 71 GB, until it was killed by hand.
/// Here the test starts this binary as a parent, which starts a child by [`fresh_command`] that
/// sleeps for 60 s; the test kills the parent with SIGKILL, which no handler can catch, and the
/// child must end within 5 s. Without the parent-death signal the child sleeps on: the test
/// failed so before the fix, and kills the child itself then, leaving no process behind.
#[cfg(target_os = "linux")]
#[test]
fn a_fresh_child_ends_when_its_parent_is_killed() {
    use std::io::{BufRead, Write};
    use std::process::{Command, Stdio};
    let me = "scaling_tests::a_fresh_child_ends_when_its_parent_is_killed";
    let exe = std::env::current_exe().expect("this test binary");
    match std::env::var(ORPHAN_ROLE).as_deref() {
        Ok("child") => {
            std::thread::sleep(Duration::from_secs(60));
            return;
        }
        Ok("parent") => {
            let mut child = fresh_command(&exe)
                .args([me, "--exact", "--test-threads=1", "--quiet"])
                .env(ORPHAN_ROLE, "child")
                .stdout(Stdio::null())
                .spawn()
                .expect("starting the child");
            println!("\nzed-orphan-child {}", child.id());
            std::io::stdout().flush().unwrap();
            // Waits on the child, as `Command::output` in run_in_a_new_process does, until the
            // test kills this process.
            child.wait().unwrap();
            return;
        }
        _ => {}
    }
    let mut parent = Command::new(&exe)
        .args([me, "--exact", "--test-threads=1", "--nocapture"])
        .env(ORPHAN_ROLE, "parent")
        .stdout(Stdio::piped())
        .spawn()
        .expect("starting the parent");
    let stdout = std::io::BufReader::new(parent.stdout.take().unwrap());
    let child: i32 = stdout
        .lines()
        .map_while(Result::ok)
        // With one test thread libtest writes `test <name> ... ` before the test's own output,
        // with no line break, so the line is found wherever it starts.
        .find_map(|line| line.split_once("zed-orphan-child ")?.1.trim().parse().ok())
        .expect("the parent names its child");
    // The fields of /proc/<pid>/stat after the name, which is in parentheses and may hold
    // spaces, so they are read after the last `)`: field 3 (the state) is the first, field 9
    // (the flags) the seventh, field 22 (the start time, in clock ticks after boot) the 20th.
    let fields = || {
        let stat = std::fs::read_to_string(format!("/proc/{child}/stat")).ok()?;
        let rest = stat.rsplit(')').next()?;
        Some(
            rest.split_whitespace()
                .map(str::to_owned)
                .collect::<Vec<_>>(),
        )
    };
    // Read while the parent lives, so the child is alive (it sleeps for 60 s) and the start time
    // is its own: a pid and its start time name one process, where the pid alone could name a
    // later process given the same pid.
    let born = fields().expect("the child is alive before its parent is killed")[19].clone();
    parent.kill().unwrap();
    parent.wait().unwrap();
    // Alive: the same process (pid and start time) is there, not a zombie (state `Z`, ended and
    // waiting only to be reaped), not exiting (flag PF_EXITING, 0x4, set by the kernel's
    // `do_exit` before it frees the process's memory, after which it cannot run again), and with
    // no SIGKILL pending (bit 8 of `SigPnd` or `ShdPnd` in /proc/<pid>/status), which no process
    // can block or catch. `parent.wait()` returns after the parent was reaped, and the kernel
    // sends the parent-death signal before that (in `exit_notify`, through
    // `forget_original_parent`), so once the signal was sent the child is not alive by this
    // test even before it is scheduled to act on it. Under load the end of a process that was
    // sent SIGKILL (being scheduled, then `exit_mm`) can take seconds; the test asks whether the
    // signal was sent, so that time no longer counts (FAIL-fresh-child-killed-parent-under-load).
    let killed = || {
        let status = std::fs::read_to_string(format!("/proc/{child}/status")).unwrap_or_default();
        status.lines().any(|l| {
            let mask = (l
                .strip_prefix("SigPnd:")
                .or_else(|| l.strip_prefix("ShdPnd:")))
            .and_then(|m| u64::from_str_radix(m.trim(), 16).ok());
            mask.is_some_and(|m| m & (1 << 8) != 0)
        })
    };
    let alive = || {
        fields().is_some_and(|f| {
            let exiting = f[6].parse::<u64>().is_ok_and(|flags| flags & 0x4 != 0);
            f[19] == born && !f[0].starts_with('Z') && !exiting
        }) && !killed()
    };
    let start = std::time::Instant::now();
    while alive() && start.elapsed() < Duration::from_secs(5) {
        std::thread::sleep(Duration::from_millis(20));
    }
    if alive() {
        // What the child was doing, read before it is killed (FAIL-fresh-child-killed-parent-
        // under-load): its state and the kernel function it waits in, its parent, and the
        // signals pending on it (bit 8 of `SigPnd`/`ShdPnd`, SIGKILL = 9, set when the
        // parent-death signal was sent but the child has not yet left the kernel).
        let read = |f: &str| std::fs::read_to_string(format!("/proc/{child}/{f}"));
        let stat = read("stat").unwrap_or_default();
        let wchan = read("wchan").unwrap_or_default();
        let status = read("status").unwrap_or_default();
        let fields: Vec<&str> = (status.lines())
            .filter(|l| {
                ["State:", "PPid:", "SigPnd:", "ShdPnd:"]
                    .iter()
                    .any(|k| l.starts_with(k))
            })
            .collect();
        let pid = rustix::process::Pid::from_raw(child).expect("a pid above 0");
        let _ = rustix::process::kill_process(pid, rustix::process::Signal::KILL);
        panic!(
            "the child {child} of a killed parent was still running 5 s later: stat `{}`, \
             wchan `{wchan}`, {}",
            stat.trim(),
            fields.join(", ")
        );
    }
}
