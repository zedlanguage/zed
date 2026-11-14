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

#[test]
fn work_a_power_of_n_above_the_order_given_fails() {
    assert!(fails(|| check_instructions_only(
        "quadratic work",
        100,
        1,
        |n| work(n, 2, 2)
    )));
    assert!(fails(|| check_instructions_only(
        "cubic work",
        10,
        2,
        |n| work(n, 3, 20)
    )));
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
    assert!(message.contains("13.5 times the work"), "{message}");
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

#[test]
fn a_comparison_runs_each_size_as_often_as_the_meter_says() {
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    let (small, large) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let mut meter = Meter::new();
    // A check that passes on its first run at the larger size does not take the extra run
    // `Meter::runs` counts for one that is over.
    let (small_runs, large_runs) = meter.runs();
    let runs = (
        small_runs,
        large_runs - usize::from(meter.again_when_over()),
    );
    compare_by(
        &mut meter,
        Measures::WorkOnly,
        None,
        "counted runs",
        Bound::Order(1),
        || _ = small.fetch_add(1, Relaxed),
        || _ = large.fetch_add(1, Relaxed),
    );
    assert_eq!((small.into_inner(), large.into_inner()), runs);
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
#[test]
fn copies_and_fills_count_by_their_length() {
    let mut meter = Meter::new();
    let from = vec![1u8; 128 << 20];
    let to = std::cell::RefCell::new(vec![2u8; 128 << 20]);
    for len in [64 << 10, 1 << 20, 16 << 20] {
        let copy = |len| to.borrow_mut()[..len].copy_from_slice(black_box(&from[..len]));
        let fill = |len: usize| to.borrow_mut()[..len].fill(black_box(3));
        for (what, f) in [("copy", &copy as &dyn Fn(usize)), ("fill", &fill)] {
            let small = meter.least(|| f(len));
            let large = meter.least(|| f(FACTOR * len));
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

/// Fails where glibc's malloc keeps a cache per thread, which glibc turns off only by
/// `GLIBC_TUNABLES` as the process starts: there, the instructions a run spends in malloc
/// depend on the threads before it, and a difference of two counts can be 1.5 times its size.
#[test]
fn malloc_keeps_no_state_from_earlier_threads() {
    let tunables = std::env::var("GLIBC_TUNABLES").unwrap_or_default();
    let setting = "glibc.malloc.tcache_count=0";
    assert!(
        tunables.split(':').any(|s| s == setting),
        "GLIBC_TUNABLES ({tunables:?}) does not set {setting}. Run the tests by \
         tools/run_tests.sh, which sets it"
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
    let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
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
        "; the first runs took ".into(),
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
/// both sizes. A run of 4000 × 1000 passes takes a few milliseconds, so the time of the
/// larger is far above the clock's resolution and the start of a thread.
#[test]
fn spins_for_the_bench_line() {
    check_instructions_only("a growing spin", 1000, 1, |n| spin(4000 * n as u64));
    check_instructions_only("a constant spin", 1000, 0, |_| spin(4000 * 1000));
}

/// The fields of the bench line of `what` in `out`: n, the two times and the two counts.
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
    let key = if Meter::new().instructions {
        "instr="
    } else {
        "work="
    };
    (field("n="), pair("ns="), pair(key))
}

/// Each check prints one line `bench <what> n=<n> ns=<small>/<large> instr=<small>/<large>
/// bytes=<small>/<large> ratio=<ratio>` and writes the two times to the file of
/// [`RATIOS_FILE`] (TEST-bench-split). The time of a loop 8 times as long grows: 8 times by
/// its work, held above 4 so that a loaded machine passes. The negative control, a loop of
/// one length at both sizes, stays under 2: a timer that measured anything but the run, or
/// one size twice, would fail one of the two.
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
    let (n, grows, units) = bench_fields(&out, "a growing spin");
    assert_eq!(n, "1000");
    assert!(units[1] > 4 * units[0], "{units:?}");
    let ratio = grows[1] as f64 / grows[0] as f64;
    assert!(
        ratio > 4.0,
        "the time of 8 times the work: {grows:?}, {ratio:.2} times"
    );
    let (_, flat, _) = bench_fields(&out, "a constant spin");
    let ratio = flat[1] as f64 / flat[0] as f64;
    assert!(
        ratio < 2.0,
        "the time of the same work: {flat:?}, {ratio:.2} times"
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
/// first filled (F44).
#[test]
fn each_run_starts_with_empty_thread_memos() {
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    let fresh = AtomicUsize::new(0);
    let run = || {
        if !FILLED.replace(true) {
            fresh.fetch_add(1, Relaxed);
        }
    };
    let mut meter = Meter::new();
    let (small, large) = meter.runs();
    // The check passes on its first run at the larger size, so it takes no extra run.
    let large = large - usize::from(meter.again_when_over());
    let only = Measures::WorkOnly;
    compare_by(
        &mut meter,
        only,
        None,
        "memo runs",
        Bound::Order(1),
        run,
        run,
    );
    assert_eq!(fresh.into_inner(), small + large);
}

/// A quadratic pass behind a memo the process keeps for all threads, keyed by size, as a
/// table not keyed by thread is: the first run of each size does `n²` work and allocates `n²`
/// bytes, every later run finds the size in the memo and does `n`. The least of the runs sees
/// only the later runs, 8 times at both measures; the first runs are 64 times.
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
    assert!(message.contains("the first runs "), "{message}");
    assert!(message.contains("64.0 times the "), "{message}");
    // Once both sizes are in the memo, every run is linear and passes.
    check("a memoized quadratic, memo full", 300, memoized);
    // The work of the first runs, without their bytes, on a count of instructions; processor
    // time holds only their bytes (see `compare_by`).
    if Meter::new().instructions {
        let message = message_of(|| check_instructions_only("work only", 200, 1, memoized));
        assert!(message.contains("the first runs took "), "{message}");
    }
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
    assert_eq!(meter.runs(), (1 + 5 * TRIES, 5 * TRIES));
    let meter =
        Meter::first_that_moves([(moving(), "instructions", true)]).expect("the counter moves");
    assert_eq!(meter.runs(), (2, 2));
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
        message.contains("the first runs took 1000000 and 64000000 passes, 64.0 times the work"),
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
/// that does not. A comparison under the limit times [`TIME_ALLOWANCE`] stops after its first
/// measurement, the fastest of five runs of each size after the warm-up; one over it in its
/// first measurement only is measured again and passes; one over it in every measurement
/// takes all [`TRIES`], the runs [`Meter::runs`] gives, and fails naming the allowance. On a
/// machine with an instruction counter no other test takes these paths.
#[test]
fn a_meter_of_a_count_that_changes_with_load_measures_up_to_three_times() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
        unit: "ns",
        instructions: false,
    };
    assert_eq!(meter.runs(), (1 + 5 * TRIES, 5 * TRIES));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 8000);
    assert_eq!((message, smalls, larges), (None, 1 + 5, 5));
    // 64 times in the five runs of the first measurement, 8 times after.
    let (message, smalls, larges) = compare_counted(
        &mut meter,
        &PASSES,
        |_| 1000,
        |i| if i < 5 { 64_000 } else { 8000 },
    );
    assert_eq!((message, smalls, larges), (None, 1 + 2 * 5, 2 * 5));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, |_| 1000, |_| 64_000);
    assert_eq!((smalls, larges), meter.runs());
    let message = message.expect("64 times fails");
    assert!(
        message.contains(
            "took 1000 and 64000, 64.0 times the work; then 1000 and 64000, 64.0 times the \
             work; then 1000 and 64000, 64.0 times the work in ns"
        ),
        "{message}"
    );
    assert!(
        message.contains(", times 2 for a count that changes with load"),
        "{message}"
    );
}

/// On a count of instructions a check runs the smaller size twice, the warm-up and the run
/// measured, and the larger once, the run both held against the warm-up and measured, and
/// once more if that run is over the limit. The measured ratio is the second run at n against
/// the least of the runs at 8n: a first run at n that costs as much as the run at 8n, as one
/// building what the process keeps does, passes the check of the first runs and does not
/// hide work 64 times the second run at n.
#[test]
fn a_count_of_instructions_measures_the_second_run_at_n_against_the_run_at_8n() {
    static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(std::sync::atomic::Ordering::Relaxed)),
        unit: "passes",
        instructions: true,
    };
    assert_eq!(meter.runs(), (2, 2));
    let first_dear = |i: usize| if i == 0 { 64_000 } else { 1000 };
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, first_dear, |_| 8000);
    assert_eq!((message, smalls, larges), (None, 2, 1));
    // A run at 8n over the limit only the first time, as a memo filled by it makes it, is
    // run again and the least of the two passes.
    let first_dear_large = |i: usize| if i == 0 { 64_000 } else { 8000 };
    let (message, smalls, larges) =
        compare_counted(&mut meter, &PASSES, first_dear, first_dear_large);
    assert_eq!((message, smalls, larges), (None, 2, 2));
    let (message, smalls, larges) = compare_counted(&mut meter, &PASSES, first_dear, |_| 64_000);
    assert_eq!((smalls, larges), (2, 2));
    let message = message.expect("64 times fails");
    assert!(
        message.contains("counted passes: took 1000 and 64000, 64.0 times the work in passes"),
        "{message}"
    );
}

/// The bytes as [`a_count_of_instructions_measures_the_second_run_at_n_against_the_run_at_8n`]
/// the work: a first run at n that allocates as much as the run at 8n passes the check of the
/// first runs, and the runs at 8n, each 64 times the bytes of the second run at n, fail the
/// check of the runs measured. The first run at 8n is over the limit, so 8n runs twice and
/// the least of the two is held (see `a_memo_filled_by_the_first_run_of_each_size_scales_as_its_first_runs_do`).
#[test]
fn the_bytes_of_the_second_run_at_n_are_held_against_the_run_at_8n() {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "passes",
        instructions: true,
    };
    let (smalls, larges) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let message = message_of(|| {
        compare_by(
            &mut meter,
            Measures::Both,
            None,
            "counted bytes",
            Bound::Order(1),
            || {
                PASSES.fetch_add(1000, Relaxed);
                let first = smalls.fetch_add(1, Relaxed) == 0;
                black_box(vec![0u8; if first { 64_000 } else { 1000 }]);
            },
            || {
                PASSES.fetch_add(8000, Relaxed);
                larges.fetch_add(1, Relaxed);
                black_box(vec![0u8; 64_000]);
            },
        )
    });
    assert!(
        message.contains("counted bytes: allocated 1000 and 64000 bytes, 64.0 times the bytes"),
        "{message}"
    );
    assert_eq!((smalls.into_inner(), larges.into_inner()), (2, 2));
}

/// A method that fills a memo on its first run at each size and allocates nothing on later
/// runs does work of order n, and its first runs (8000 bytes at n, 64000 at 8n) are 8 times
/// apart. From 26e51b07b (TEST-scaling-runs, `Meter::repeats` gives (1, 1) for instructions)
/// to FAIL-scaling-cold-8n-bytes the run at 8n was measured only once, cold, while the run at
/// n was measured after the warm-up: 0 bytes against 64000, so the check failed, as did 20
/// checks of l01_23_subtyping (setop, witnesses, refusals and two of scaling), for example
/// "diagonal parity contradiction: sizes 9 and 72: allocated 0 and 134376 bytes, 134376.0
/// times the bytes". Now the run at 8n over the limit is run again, warm, and the least of
/// the two (0 bytes against 0) passes.
#[test]
fn a_memo_filled_by_the_first_run_of_each_size_scales_as_its_first_runs_do() {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "passes",
        instructions: true,
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

/// A comparison of two runs that are not one pass at n and 8n holds its ratio to the limit
/// given, in the check of the first runs and in that of the runs measured: a ratio equal to
/// it passes, one over it fails with the reason given, whichever check it is over in.
#[test]
fn a_comparison_to_a_given_limit_passes_at_the_limit_and_fails_over_it() {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};
    static PASSES: AtomicU64 = AtomicU64::new(0);
    let mut meter = Meter {
        read: Box::new(|| PASSES.load(Relaxed)),
        unit: "passes",
        instructions: true,
    };
    // The first method's first run does `warm` passes, its later runs 1000.
    let given = |meter: &mut Meter, warm: u64, second: u64| {
        let firsts = AtomicUsize::new(0);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compare_by(
                meter,
                Measures::WorkOnly,
                None,
                "two methods",
                Bound::Given(3.0, "the second method is at most 3 times the first"),
                || {
                    let first = firsts.fetch_add(1, Relaxed) == 0;
                    PASSES.fetch_add(if first { warm } else { 1000 }, Relaxed);
                },
                || _ = PASSES.fetch_add(second, Relaxed),
            )
        }))
        .map_err(|e| *e.downcast::<String>().expect("a message"))
    };
    assert_eq!(given(&mut meter, 1000, 3000), Ok(()));
    let message = given(&mut meter, 1000, 3001).expect_err("first runs over the limit");
    assert!(
        message.contains(
            "two methods: the first runs took 1000 and 3001 passes, 3.0 times the work; "
        ) && message.ends_with("; the second method is at most 3 times the first"),
        "{message}"
    );
    let message = given(&mut meter, 3000, 3001).expect_err("runs measured over the limit");
    assert_eq!(
        message,
        "two methods: took 1000 and 3001, 3.0 times the work in passes; the second method is \
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
