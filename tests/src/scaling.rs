//! The scaling test of the rule of low complexity (DESIGN.md Part G, "Six standing rules"): a
//! pass runs at sizes n and 8n, and the larger run must do less than 10.5 times the work of the
//! smaller, times `8^(k−1)` where `n^k` is the order the measured work is defined to have
//! ([`LIMIT`], [`limit`]; author, 2026-11-13: "Let's keep things under 10.5 for 8x scaling" and
//! "Under 10.5, but ideally under 9"). A check that passes with a ratio from 9 to 10.5 times
//! `8^(k−1)` ([`PREFERRED`]) prints a note naming the test ([`hold`]). Work of order n log n is
//! `8 ln(8n) / ln(n)` times: 10.4 at n = 1000, 10.4995 at n = 777, under 10.5 from n = 777 on and
//! 12.2 at n = 52. Work of order `n^1.13` is 10.48 times at every n, under the limit, and
//! `n^1.14` is 10.70 times, over it. Work of order `n log^2 n`, the best known cost of radix
//! conversion and of the gcd of numbers of n bits (author decision A47, 2026-11-09), is under
//! 10.5 only from n = 1,587,343 on. For a few hours of 2026-11-13 the limit was 13
//! (TESTS-scaling-limit-13), and until then `8^k × ln(8n) / ln(n) × 1.1` (SCALE-ratio, 15.4 at
//! n = 16), with `8 × (ln(8n) / ln(n))^2 × 1.1` for radix conversion and the gcd, and until
//! 2026-11-07 a fixed `24 × 8^(k−1)`. Setting
//! the variable `ZED_SCALING_RATIOS` ([`RATIOS_FILE`]) to a file name makes every check append
//! its measurements to that file.
//!
//! Work is counted in instructions retired, in user mode, by this thread and the threads it
//! starts. The count does not change with the load on the machine. Elapsed time and processor
//! time both do, and by more for the larger run: at load 55 with half the load copying memory,
//! a linear walk of 1000 and 8000 terms took 96 times as long by the clock and 44 times by
//! processor time, because the larger run lost the caches and was preempted, and it retired
//! 8.0 times the instructions on every try. So the instruction count is the test, and a test
//! never judges time; but a benchmark's plan row is marked Done only on a ratio of wall time
//! taken at a 5-minute load of 64 or less at both the start and the end of the run
//! (BENCH-wall-vs-instruction-check, 2026-11-18), the instruction ratio being cited only as a
//! diagnostic.
//!
//! The count has three limits. Work in the kernel is not counted. A `rep movsb` or `rep stosb`
//! counts as one instruction or few, whatever its length, and glibc's memcpy and memset use
//! them on a CPU with erms or fsrm, so the meter keeps glibc from them, and
//! `copies_and_fills_count_by_their_length` fails on a machine where they are hidden. The
//! instructions glibc's malloc spends depend on what earlier threads left in the arena a new
//! thread takes over and on the order the hash seed frees blocks in: one check of the same
//! program took 0.26 billion instructions (0.9%) more in some runs than in others, all of it in
//! malloc, and a difference of two such counts, of about 0.5 billion, came out 1.5 times its
//! size. Turning off malloc's cache per thread made the counts repeat but added work to each
//! allocation, which lowered the ratio of a superlinear cost (TEST-meter-allocator-bias). So each
//! run allocates from a heap of its own (`zed_alloc_count::metered`, module `meter` of that
//! crate), whose instructions per call depend only on the run's own calls, and
//! `the_instructions_of_a_run_repeat` fails where they do not.
//!
//! The settings against `rep movsb` and `rep stosb` are glibc tunables, which glibc reads only
//! as a process starts. The crate `zed-meter-settings` holds them (`GLIBC_TUNABLES`) and starts
//! a test binary that was started without them again with them, before `main`, and
//! [`Meter::new`] stops where they are still not in effect. So a test gives the same verdict run
//! directly by `cargo test` as under `tools/run_tests.sh`, which exports the same settings
//! (TEST-scaling-direct-run-verdict: a Θ(k²) cost took 11.29 times the instructions at 8n run
//! directly, and 10.41 with the settings of that time, which then also turned off malloc's
//! cache).
//!
//! Where the hardware has no counter, as in most virtual machines (the Colab VMs' kernels say "no
//! PMU driver, software events only"), the instructions can still be counted in software
//! (BENCH-vm-no-instruction-counter). When `zed_meter_settings::ZED_METER_DRRUN` and
//! `ZED_METER_ICOUNT` name DynamoRIO and its client `zed_icount` (tools/icount; Colab's job.sh sets
//! both), [`Meter::new`] in a test binary started with `--exact` (a benchmark under
//! `tools/run_tests.sh`, a run in a new process) starts it again under them
//! (`zed_meter_settings::start_under_dynamorio`), so that only the tests that measure pay the
//! slowdown, and the meter of the new image reads the client's count:
//! an add of a basic block's length to a counter of the thread as the block is entered, the
//! threads folded into the
//! thread that started them as they end, as the kernel's count with `inherit` is. DynamoRIO:
//! Bruening, Garnett and Amarasinghe, "An infrastructure for adaptive dynamic optimization", CGO
//! 2003, doi:10.1109/CGO.2003.1191551 (Crossref's record read, not the paper's text; a binary is
//! run from a cache of its basic blocks, copied and changed by the client as each is first
//! reached; tools/icount/zed_icount.c says what it counts and how it differs from the hardware).
//! Tradeoff, measured 2026-11-22 on a Colab hm
//! VM with the client's own test program (tools/icount/selftest.c, `work 40000`, a Θ(n²) sort,
//! 0.88 s natively), against the other ways to count in software:
//!
//! | counter | time | same count twice | 8n ratio against the hardware's |
//! |---|---|---|---|
//! | zed_icount (DynamoRIO 11.3.0) | 0.99 s, 1.12x | yes | 63.461 against 63.402 (0.09%) |
//! | DynamoRIO's sample inscount | 1.52 s, 1.73x | no (45 apart at n = 5000) | not read in the process |
//! | valgrind's callgrind | 18.43 s, 21x | yes | not read in the process |
//! | QEMU's plugin libinsn | not measured | | Ubuntu's qemu 8.2.2 ships no plugin |
//!
//! The hardware ratio is this machine's `perf stat -e instructions:u` of the same binary, built
//! on the VM. The software count is about 133,000 instructions below the hardware's at both sizes:
//! the start of the process before the client loads and its exit after the read, the same at
//! every size, so ratios at sizes the benchmarks use agree.
//!
//! Cost on zedc's code, which is far larger than the sort and runs much of it few times, so the
//! copying into the cache weighs more (hm3, 2026-11-22, handoff of b22-meter1): the 328 unit tests
//! of l01_29 (`--skip bench --test-threads=8`) took 4.9 s and 4.7 s natively, 23.0 s and 23.3 s
//! under DynamoRIO with no client, and 34.7 s and 35.2 s with zed_icount: 4.8x for DynamoRIO and
//! 1.5x more for the count, 7.3x in all. A benchmark run under it pays the cache once per process:
//! presburger's `products_whose_factors_one_sum_joins_scale` took 1.17 s to 1.41 s at n (24 ms
//! natively) and 2.27 s to 2.48 s at 8n (0.28 s) in four runs, the whole test 9.7 s to 10.5 s.
//! Placing each block's add where the
//! arithmetic flags are dead, so that drreg need not save them, was tried and gave the same counts
//! and the same times within the spread (34.7 s and 35.9 s), so the simpler add at the block's
//! first instruction stays. Why accepted: only the ratio of counts is read, which the time does
//! not change, and the phase limit of a benchmark (tools/bench_limit.sh) is on time; a benchmark
//! whose sizes then pass that limit on a VM is the benchmark's cost to fix, as l01_26's
//! `fits_sig_takes_linear_time_in_the_depth` already does natively there (50.6 s and 61.2 s a
//! run on hm3, most of it building the 160,000-deep types outside the measured runs).
//! Valgrind (Nethercote and Seward, PLDI 2007, doi:10.1145/1250734.1250746) is exact too but 20
//! times slower, and Intel's Pin and SDE (Luk et al., PLDI 2005, doi:10.1145/1065010.1065034) are
//! not free software and were not measured, so neither was taken. Checked by
//! `the_instructions_of_a_run_repeat`, which fails on processor time and passes on this count.
//!
//! Without either counter [`Meter`] falls back on the
//! kernel's task clock: the processor time of this thread and the threads it starts, without the
//! tests running beside it in the process. It changes with load, so it needs more runs: each size
//! the fastest of five, three measurements in a row over the limit. Processor time of the whole
//! process does not do: tests beside a run of 20 µs let a quadratic run pass. Where
//! `perf_event_open` is refused altogether no count exists, and the check stops with an error.
//!
//! All of the above is Linux. On macOS the count is `ri_instructions` of
//! `proc_pid_rusage(getpid(), RUSAGE_INFO_V4, ...)`, the instructions the whole process retired,
//! or, where that reads 0 (a machine whose counters the kernel does not read), its `ri_cycles`;
//! the unit in a failure's message says which was measured. On Windows the count is
//! `QueryProcessCycleTime`, the cycles of the whole process in user and kernel mode. Cycles
//! change with load, as processor time does, so they get its five runs and three measurements.
//! These counters, and the bytes `zed-alloc-count` counts on those systems, are of the whole
//! process and not of a thread and the threads it starts, so [`Meter::new`] stops with its own
//! error unless the harness runs one test at a time (`cargo test -- --test-threads=1`, or
//! `RUST_TEST_THREADS=1`). Off Linux there is no meter of processor time to fall back on, and on
//! any other system the check stops with an error. The calls are in `zed_alloc_count::os`, with
//! the documents they follow. The macOS and Windows paths are compiled on Linux (`cargo check`
//! and clippy for x86_64-apple-darwin, aarch64-apple-darwin and x86_64-pc-windows-msvc) and have
//! not been run. The test binaries do not build there yet: `zed-rt`'s stack (`sysinfo`,
//! `MAP_STACK`, `mmap`) is Linux-only.
//!
//! The second measure is the bytes a run allocates, counted by the global allocator of the test
//! binaries (the crate `zed-alloc-count`): a block counts its size, a grown block its new size.
//! Its ratio is held to the same limit. It sees what the instruction count misses: a copy is a
//! few instructions per 32 bytes, so the old `resolve`, which copied a list of `k` overloads into
//! each of `k` uses, took 10.2 times the instructions at 8,000 against 1,000 but 51.8 times the
//! processor time. The count is of the run's thread and every thread it starts, however it starts
//! them, and the threads those start, as the instruction count is; tests running beside a run
//! have counts of their own and do not change it (zed-alloc-count gives each new thread the count
//! of the thread that started it). The bytes compared are those counted inside the thread
//! of each run, without its start: std records each thread that starts in a map of the live
//! threads, and whether that allocates depends on the other threads alive. A test
//! whose bytes grow faster than its order for a reason recorded in COMPLEXITY.md uses
//! [`check_instructions_only`], with a comment naming the item that fixes it. A larger run whose
//! thread counts no bytes is refused, since its bytes cannot be compared, and a count lost to 0
//! would otherwise pass unmeasured; a run that allocates nothing uses [`check_instructions_only`].
//!
//! Each run is on a new thread of its own (`alone`, by [`on_a_thread`]), so
//! the memos a thread keeps start empty in every run: zed-kernel keeps its tables of diagram
//! nodes and its emptiness results per thread. Run on one thread, every run after the first read
//! the first's results: the union of 16 and 128 morphism differences
//! (`l01_23_subtyping::scaling`) took 7.0 times the work from the second run and 48.0 times from
//! a fresh start (F44). A new thread does not empty the memos a run's input holds, such as a
//! `Db`'s results or a type's printed text, or a table the process keeps for all threads. On a
//! count of instructions each size runs once (author A160, 2026-11-20), so the run measured at
//! each size is its first and fills them alike; from SCALE-first-run to A160 a warm-up at `n` was
//! held against the first run at `8n` for this reason. A table the process keeps for all threads
//! and fills once is full when the run at `8n` starts in the same process, so on a count of
//! instructions that run is in a new process of the test binary, which starts as the check did
//! (TEST-scaling-cold-shared-memo; see `compare_by`).

use std::cell::Cell;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::{Duration, Instant};

#[cfg(target_os = "linux")]
use perf_event::Builder;
#[cfg(target_os = "linux")]
use perf_event::events::{Event, Hardware, Software};
#[cfg(any(target_os = "macos", windows))]
use zed_alloc_count::os;

/// How much larger the second run is.
pub const FACTOR: usize = 8;

/// The ratio of the work at 8n to the work at n that a pass of order n must stay under (author,
/// 2026-11-13). The instructions of one test differ from run to run by up to 6.5% in this ratio
/// (387 tests run three times, 2026-11-07: median 0.03%, 99th percentile 3%), from the order a
/// hash map's seed puts keys in, so a pass of order n log n measured at 10.4 may pass or fail.
pub const LIMIT: f64 = 10.5;

/// The ratio under which a pass of order n is strongly preferred (author, 2026-11-13): a check
/// that passes from it up to [`LIMIT`] prints a note naming the test.
pub const PREFERRED: f64 = 9.0;

/// How many times the limit a meter of processor time or cycles allows: those change with load.
/// A linear loop run at 10^5 and 8 × 10^5 passes took 5.6 to 8.8 times the processor time, the
/// fastest of five each, and a quadratic one 33 to 82 times for 64 (2026-11-07, load 20 to 25).
pub const TIME_ALLOWANCE: f64 = 2.0;

/// `8^(power − 1)`: the ratio at 8n of work of order `n^power` to work of order n, by which
/// [`LIMIT`] and [`PREFERRED`] are scaled for a test of another order.
fn scale(power: u32) -> f64 {
    (FACTOR as f64).powi(power as i32 - 1)
}

/// The ratio of the work at 8n to the work at n that work of order `n^power` must stay under:
/// [`LIMIT`] times `8^(power − 1)`. Power 1 is a pass of the compiler or the runtime, 10.5; power
/// 2 a Zed program whose own algorithm is quadratic, such as an O(n) operation in an O(n) loop,
/// 84; power 0 work of order 1 or `log n`, 1.3125. One rule for every power keeps a single
/// constant, at the cost of power 0 allowing more than before at large n: the limit until
/// 2026-11-13, `ln(8n) / ln(n) × 1.1`, was 1.32 at n = 30,000 and falls toward 1.1 as n grows,
/// while work of order `log n` is 1.20 times at n = 30,000.
pub fn limit(power: u32) -> f64 {
    LIMIT * scale(power)
}

/// Holds the ratio `large / small` of two counts of `measure` (instructions, bytes, nodes,
/// characters), at sizes n and 8n, to [`limit`]`(power)`: it panics at the limit or over it, and
/// otherwise prints the ratio, with a note naming the test when the ratio is from [`PREFERRED`]
/// to [`LIMIT`] (each times `8^(power − 1)`). `what` names the pass and its sizes. A count of 0
/// is read as 1. It returns the ratio.
pub fn hold(what: &str, measure: &str, small: u64, large: u64, power: u32) -> f64 {
    let ratio = large.max(1) as f64 / small.max(1) as f64;
    let limit = limit(power);
    record(
        what,
        (None, Bound::Order(power)),
        limit,
        (small, large, ratio, measure),
        None,
        None,
    );
    assert!(
        ratio < limit,
        "{what}: {small} and {large} {measure}, {ratio:.2} times at 8n; {}",
        why(power)
    );
    eprintln!(
        "{what}: passed: {small} and {large} {measure}, {ratio:.2} times; the limit is {limit:.2}"
    );
    note_if_near(what, measure, ratio, power);
    ratio
}

/// [`hold`] for a count that is linear in n by its construction and does not change with the
/// load (calls of a function, nodes made or entered, bytes of a text), held also to
/// [`PREFERRED`]: such a count measures near 8 times on every run, so a bound of 9 still finds an
/// extra factor of `log n` (`8 ln(8n) / ln(n)`, 10.4 at n = 1000) that [`LIMIT`] lets through.
/// The tests that use it held their count under 9, or under 5 at 4n, before the limit became 13 on
/// 2026-11-13.
pub fn hold_linear(what: &str, measure: &str, small: u64, large: u64) -> f64 {
    let ratio = hold(what, measure, small, large, 1);
    assert!(
        ratio < PREFERRED,
        "{what}: {small} and {large} {measure}, {ratio:.2} times at 8n; a count linear in n is \
         under {PREFERRED} times"
    );
    ratio
}

/// Where the limit of a test of order `n^power` comes from, for the messages.
fn why(power: u32) -> String {
    let limit = limit(power);
    match power {
        1 => format!(
            "the rule of low complexity allows less than {limit:.2} times at 8n (DESIGN.md Part G)"
        ),
        _ => format!(
            "for work of order n^{power} the rule of low complexity allows less than {LIMIT} × \
             8^({power} − 1) = {limit:.2} times at 8n (DESIGN.md Part G)"
        ),
    }
}

/// Prints a note naming the test when `ratio`, of `measure` at 8n against n for work of order
/// `n^power`, is from [`PREFERRED`] to [`LIMIT`] times `8^(power − 1)`: under the limit, but
/// over the ratio the author strongly prefers. The test is the name of this thread, which
/// libtest gives each test and [`on_a_thread`] passes on.
fn note_if_near(what: &str, measure: &str, ratio: f64, power: u32) {
    if ratio < PREFERRED * scale(power) {
        return;
    }
    let thread = std::thread::current();
    let test = thread.name().unwrap_or("a test on an unnamed thread");
    eprintln!(
        "note: {test}: {what}: {ratio:.2} times the {measure} at 8n, from {:.2} to {:.2}: under \
         the limit, but a method under {:.2} is strongly preferred",
        PREFERRED * scale(power),
        limit(power),
        PREFERRED * scale(power)
    );
}

/// How many measurements of processor time must all be over the limit before the test fails.
pub const TRIES: usize = 3;

/// How many runs of each size a meter of processor time or cycles takes the fastest of, in each
/// of its [`TRIES`] measurements. Author A160 (2026-11-20) has each size run once, unless a
/// single run's ratio was measured to spread by more than [`TIME_ALLOWANCE`] under load; it
/// was, so processor time keeps five. Measured by BENCH-limit-counts-setup, 2026-11-20, load
/// 30 falling to 23 on 32 cores, 120 pairs of single runs at n and 8n of each linear method of
/// tests/src/scaling_tests.rs, against 20 pairs of the fastest of five:
///
/// | method | single runs: min, median, max | fastest of five: min, median, max |
/// |---|---|---|
/// | `work(n, 1, 10_000)`, n = 100 | 2.91, 5.58, 9.00 (3.1 times apart) | 2.74, 5.68, 6.48 |
/// | `work(n, 1, 100_000)`, n = 100 | 4.93, 6.71, 9.47 (1.9 times) | 5.98, 6.53, 8.58 |
/// | `linear_bytes(n)`, n = 1,000,000 | 5.83, 8.08, 11.20 (1.9 times) | 6.13, 8.17, 10.99 |
///
/// No ratio of either kind passed 21 ([`LIMIT`] × [`TIME_ALLOWANCE`]). The fastest of five
/// cuts the top of the spread (9.00 to 6.48 on the shortest method), which is what keeps a
/// linear method clear of the limit when load rises; a single run of `work(n, 2, 20)` at 100
/// and 800, quadratic but short, measured 11.19 to 35.40, under 21 in 87 of 120 runs, so time
/// cannot tell orders apart at that size either way.
pub const TIME_RUNS: usize = 5;

/// Runs `f` on a new thread and waits for it, so that every memo a thread keeps starts empty. The
/// thread's stack is what is left of the caller's, less about 5 KiB of the thread's own, so a
/// test that sets the stack of the thread it checks on, or sets none, sets it for its runs too.
/// It returns the bytes the thread and the threads it started allocated, which count in this
/// thread's count too, and the elapsed time of `f` in nanoseconds (see [`counted_on_a_thread`]). A
/// panic in `f` goes on in the caller.
pub(crate) fn alone(f: &(impl Fn() + Sync)) -> (u64, u64) {
    let stack = stacker::remaining_stack().expect("the size of this thread's stack");
    let ((), bytes, ns) = counted_on_a_thread(stack, f);
    (bytes, ns)
}

/// The processor time this thread has used, which time spent waiting for a processor does not
/// add to. For a limit on the time of one run that starts no thread; a comparison of two runs
/// uses [`Meter`].
#[cfg(unix)]
pub fn cpu_time() -> Duration {
    use rustix::time::{ClockId, clock_gettime};
    let t = clock_gettime(ClockId::ThreadCPUTime);
    Duration::new(t.tv_sec as u64, t.tv_nsec as u32)
}

/// The processor time this thread has used, by `GetThreadTimes`, in kernel and user mode.
#[cfg(windows)]
pub fn cpu_time() -> Duration {
    os::thread_cpu_time()
}

/// The least [`cpu_time`] of `runs` runs of `f`, in nanoseconds, and what the last run returned.
/// The least, since the load only adds to a run's time. What a run returns is dropped after its
/// time is read, so the drop is not timed. For a run that starts no thread: the time of other
/// threads is not counted. `runs` is 1 or more.
pub fn least_cpu_ns<T>(runs: usize, mut f: impl FnMut() -> T) -> (u128, T) {
    let mut least = u128::MAX;
    let mut last = None;
    for _ in 0..runs {
        let start = cpu_time();
        let out = black_box(f());
        least = least.min((cpu_time() - start).as_nanos());
        last = Some(out);
    }
    (least, last.expect("one run or more"))
}

/// The most milliseconds a step stopped at its limit of counted work may take in a benchmark of
/// [`per_unit_bound`]: 250 ms times 2.
///
/// The 250 ms is the time QUESTIONS A99 allows a predicted computation (zed-kernel `poly.rs`
/// `LIMIT`); the work limits of zedc-presburger, `meter::EXACT_LIMIT` (the exact cover and the
/// two-pin reading) and `row_sums::JOIN_LIMIT` (the join of row sums), were each set from a
/// measured time per unit so that a run stopped at the limit takes 250 ms or less (their
/// comments give the measurements). The factor 2 is for the load of the test machine, the same
/// factor as [`TIME_ALLOWANCE`] and for the same reason: a thread's CPU time for the same work
/// changes with the load (shared caches, memory bus and, on a core running two threads, the
/// core): the least CPU time of a linear loop at 8 times the work was 5.6 to 8.8 times that at
/// the base size, at load 20 to 25 (2026-11-07). It is a margin, measured and not proved. What
/// relies on it: only the benchmarks that call [`per_unit_bound`] (`exact::tests::bench`,
/// `l01_38_omega_test::bench::exact_cover` and `disj_groups`); no checker result depends on it. A
/// benchmark failing it means a cost per unit the limit's fit did not predict: the limit is fitted
/// again (A96), never this margin widened. Before DRY-test-helpers each of the three wrote `500.0`
/// itself.
pub const AT_THE_LIMIT_MS: f64 = 500.0;

/// Holds a step's time per unit of its counted work to [`AT_THE_LIMIT_MS`] at `limit` units:
/// each case is `(name, ns, units)`, its CPU time and the units it counted, and must count
/// `min_units` or more, so that its time is not the fixed costs of the step. The worst
/// nanoseconds per unit, times `limit`, is the most time a run stopped at the limit takes;
/// it panics when that is over [`AT_THE_LIMIT_MS`], and otherwise returns it, in milliseconds.
/// `what` names the step in the messages.
pub fn per_unit_bound(
    what: &str,
    cases: &[(String, u128, u64)],
    min_units: u64,
    limit: u64,
) -> f64 {
    let mut worst = 0f64;
    for (name, ns, units) in cases {
        assert!(
            *units >= min_units,
            "{what}: {name}: {units} units; the case must count {min_units} units or more, or \
             its time is the fixed costs"
        );
        let per = *ns as f64 / *units as f64;
        eprintln!("{what}: {name}: {units} units in {ns} ns of CPU time, {per:.2} ns per unit");
        worst = worst.max(per);
    }
    let most = worst * limit as f64 / 1e6;
    eprintln!("{what}: worst {worst:.2} ns per unit; the limit takes at most {most:.0} ms");
    assert!(
        most <= AT_THE_LIMIT_MS,
        "{what}: {most:.0} ms at the limit of {limit} units; at most {AT_THE_LIMIT_MS} ms"
    );
    most
}

/// Reads a counter of work.
pub(crate) type Read = Box<dyn FnMut() -> u64>;

/// Counts work in the unit the machine offers.
pub struct Meter {
    /// Reads the counter.
    pub(crate) read: Read,
    /// The name of the unit `read` counts in, for the messages.
    pub(crate) unit: &'static str,
    /// Whether the count is of instructions, which does not change with load, and not of
    /// processor time or cycles, which do.
    pub(crate) instructions: bool,
    /// Whether a check by this meter of instructions runs its size 8n in a new process of the
    /// test binary (see [`compare_by`]): true for [`Meter::new`]'s count of instructions; false
    /// for the meters the tests of the harness make, which count the runs of each size in this
    /// process, and for processor time and cycles, which run each size several times.
    pub(crate) fresh: bool,
}

impl Meter {
    /// A meter of instructions where the hardware counts them, or where DynamoRIO's client
    /// `zed_icount` counts them in software, or else of the processor time of this thread and
    /// the threads it starts. With no counter at all a test cannot measure the work, so it stops;
    /// see `no_counter`.
    #[cfg(target_os = "linux")]
    pub fn new() -> Self {
        stop_unless_the_settings_are_in_effect();
        Self::in_software()
            .or_else(|| Self::open(Hardware::INSTRUCTIONS, "instructions", true))
            .or_else(|| {
                // The new image runs the process's tests from the start, so only a process that
                // runs this test alone starts again; the call returns where it does not.
                if std::thread::current().name().is_some_and(runs_alone) {
                    zed_meter_settings::start_under_dynamorio();
                }
                Self::open(Software::TASK_CLOCK, "ns of processor time", false)
            })
            .unwrap_or_else(|| no_counter())
    }

    /// The instructions the DynamoRIO client `zed_icount` counts, when this process runs under
    /// it (zed_meter_settings::start_under_dynamorio says when it does). It comes first: the
    /// process runs under the client only where the hardware counter did not open or did not
    /// move, and
    /// a hardware counter that did would count DynamoRIO's own work too.
    #[cfg(target_os = "linux")]
    fn in_software() -> Option<Self> {
        zed_alloc_count::os::software_instructions()?;
        let read = || {
            zed_alloc_count::os::software_instructions()
                .expect("zed_icount answered at the meter's start")
        };
        Self::first_that_moves([(
            Box::new(read) as Read,
            "instructions (counted in software by DynamoRIO's zed_icount)",
            true,
        )])
    }

    /// A meter of the instructions of the whole process where the kernel counts them, or else of
    /// its cycles. Both count every thread of the process, so the tests must run one at a time;
    /// see [`one_test_at_a_time`].
    #[cfg(target_os = "macos")]
    pub fn new() -> Self {
        stop_unless_one_test_at_a_time("macOS", "proc_pid_rusage");
        Self::first_that_moves([
            (
                Box::new(os::process_instructions) as Read,
                "instructions of the whole process (proc_pid_rusage, ri_instructions)",
                true,
            ),
            (
                Box::new(os::process_cycles),
                "cycles of the whole process (proc_pid_rusage, ri_cycles: ri_instructions does \
                 not count here)",
                false,
            ),
        ])
        .unwrap_or_else(|| no_counter())
    }

    /// A meter of the cycles of the whole process. It counts every thread of the process, so the
    /// tests must run one at a time; see [`one_test_at_a_time`].
    #[cfg(windows)]
    pub fn new() -> Self {
        stop_unless_one_test_at_a_time("Windows", "QueryProcessCycleTime");
        Self::first_that_moves([(
            Box::new(os::process_cycles) as Read,
            "cycles of the whole process (QueryProcessCycleTime)",
            false,
        )])
        .unwrap_or_else(|| no_counter())
    }

    /// No meter: this system has no counter the scaling tests read.
    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    pub fn new() -> Self {
        no_counter()
    }

    /// A meter of processor time, whatever the hardware offers.
    #[cfg(target_os = "linux")]
    pub fn of_cpu_time() -> Self {
        stop_unless_the_settings_are_in_effect();
        Self::open(Software::TASK_CLOCK, "ns of processor time", false)
            .unwrap_or_else(|| no_counter())
    }

    /// The counter of `event`, of this thread and the threads it starts.
    #[cfg(target_os = "linux")]
    fn open(event: impl Event, unit: &'static str, instructions: bool) -> Option<Self> {
        let mut builder = Builder::new(event);
        let mut counter = builder.inherit(true).enabled(true).build().ok()?;
        let read = move || counter.read().expect("reading the counter");
        Self::first_that_moves([(Box::new(read) as Read, unit, instructions)])
    }

    /// The first of `counters` that moves while this thread does work, with its unit and whether
    /// it counts instructions. Some virtual machines open the instructions counter and leave it
    /// at 0, and macOS leaves `ri_instructions` at 0 where it does not read the hardware counter,
    /// so a counter that does not move is not used.
    pub(crate) fn first_that_moves<const N: usize>(
        counters: [(Read, &'static str, bool); N],
    ) -> Option<Self> {
        counters
            .into_iter()
            .find_map(|(mut read, unit, instructions)| {
                let start = read();
                spin(100_000);
                (read() != start).then_some(Self {
                    read,
                    unit,
                    instructions,
                    fresh: instructions,
                })
            })
    }

    /// The work `f` does, in instructions or nanoseconds, and the bytes it allocates on this
    /// thread, the threads it starts and the threads those start; each never 0. Off Linux both
    /// are of the whole process (see the module's documentation).
    ///
    /// `f` allocates from a heap of its own, as a run of [`check_order`] does
    /// (`zed_alloc_count::metered`, TEST-meter-allocator-bias), unless this thread is in such a
    /// run already; the start and end of that heap are outside the count. A block of the C
    /// library's made before `f` and grown by `realloc` inside it stays the C library's, so its
    /// cost is glibc's.
    pub fn work(&mut self, f: impl FnOnce()) -> Work {
        zed_alloc_count::metered(|| self.work_on_the_c_heap(f))
    }

    /// [`Meter::work`] with `f` allocating from the C library's `malloc`, unless this thread is
    /// in a metered run: for the test that compares the two, and for the crossover benchmarks
    /// (`zed_benches::runs`), which compare the absolute work of two methods and so count it on
    /// the heap programs run with (PERF-crossover-heap).
    pub fn work_on_the_c_heap(&mut self, f: impl FnOnce()) -> Work {
        let bytes = zed_alloc_count::allocated();
        let start = (self.read)();
        f();
        let units = (self.read)() - start;
        Work {
            units: units.max(1),
            bytes: (zed_alloc_count::allocated() - bytes).max(1),
        }
    }

    /// The count as it reads now, in the unit of [`Meter::unit`]: what the tests of
    /// `zedc::work` read as instructions (TIME-report).
    pub fn read(&mut self) -> u64 {
        (self.read)()
    }

    /// The name of the unit of [`Work::units`].
    pub fn unit(&self) -> &'static str {
        self.unit
    }

    /// How many runs to take the least of, and how many measurements must all be over a limit.
    ///
    /// A count of instructions takes one run of each size and one measurement: a check runs n
    /// once and 8n once, about 9 times the time at n (author A160, 2026-11-20: "Just run each
    /// once"). From TEST-scaling-runs to A160 a warm-up at n ran before the run at n measured,
    /// and the first run at 8n was held against the warm-up; on 2026-11-15 a second run at 8n
    /// was added when the first was over the limit or at the note of [`PREFERRED`]
    /// (FAIL-scaling-cold-8n-bytes, PERF-permission-reverse-first-run), since the run at 8n was
    /// cold and the run at n measured was not: so a check ran n twice and 8n once or twice, 10
    /// or 18 times the time at n. With each size run once both runs are cold, and neither is
    /// needed. Until TEST-scaling-runs it took the least of two runs of each size, 3 runs at n and
    /// 2 at 8n, about 19 times the time at n, so a benchmark whose time at n was the 1 s the author
    /// asks for (P169, P175) did not fit in the 20 s a piece may take. The least of two was meant
    /// to remove the spread of single runs, but measured it barely changes the ratio: 58 checks in
    /// 57 benchmarks sampled from 19 groups (checker, runtime, Presburger, e-graph, parser,
    /// lowering, the kernel), each run in 5 processes, 295 comparisons (2026-11-14, under
    /// tools/run_tests.sh's malloc and memcpy settings, load 23 to 32). The ratio of the first
    /// run at 8n to the second at n differed from the ratio of the least of two runs at each
    /// size by at most 0.88% in instructions (mean 0.03%, the largest in `l01_29_diagnostics`'
    /// `rejecting_many_binders_that_name_types_scales`, whose single runs differ by up to 1.4%
    /// in one process) and by at most 0.05% in bytes, both under the 1% the row allowed. Across
    /// the 5 processes the single-run ratio of each check spread by at most 0.52%, the
    /// least-of-two ratio by up to 1.26%. Processor time and cycles change with load, so they
    /// keep the fastest of [`TIME_RUNS`] and [`TRIES`] measurements (see [`TIME_RUNS`] for why
    /// A160's one run of each size does not hold for them).
    fn repeats(&self) -> (usize, usize) {
        if self.instructions {
            (1, 1)
        } else {
            (TIME_RUNS, TRIES)
        }
    }

    /// How many times the limit of a check this meter allows: [`TIME_ALLOWANCE`] for processor time
    /// and cycles, which change with load, and 1 for instructions.
    fn allowance(&self) -> f64 {
        if self.instructions {
            1.0
        } else {
            TIME_ALLOWANCE
        }
    }

    /// At most how many times [`compare`] runs the smaller and the larger size, so that a test
    /// can build a fresh input for each run before any is timed: once each on a count of
    /// instructions (author A160, 2026-11-20), and [`TIME_RUNS`] × [`TRIES`] each on processor
    /// time or cycles, of which a check that passes on an earlier measurement leaves the rest
    /// unused.
    pub fn runs(&self) -> (usize, usize) {
        let (least, measurements) = self.repeats();
        (least * measurements, least * measurements)
    }

    /// The least work and the least bytes of the runs of `f`, as many as [`Meter::repeats`] says,
    /// with `before` run before each run of `f`, outside what is measured.
    pub(crate) fn least(&mut self, before: impl Fn(), f: impl Fn()) -> Work {
        (0..self.repeats().0)
            .map(|_| {
                before();
                self.work(&f)
            })
            .reduce(|a, b| Work {
                units: a.units.min(b.units),
                bytes: a.bytes.min(b.bytes),
            })
            .expect("at least one run")
    }
}

impl Default for Meter {
    fn default() -> Self {
        Self::new()
    }
}

/// What one run did.
#[derive(Clone, Copy, Debug)]
pub struct Work {
    /// The work, in the unit of [`Meter::unit`].
    pub units: u64,
    /// The bytes allocated.
    pub bytes: u64,
}

/// Which measures a check holds to its limit.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Measures {
    /// The work and the bytes allocated.
    Both,
    /// The work only, for a test whose bytes are known to grow faster: see
    /// [`check_instructions_only`].
    WorkOnly,
}

/// Stops a test whose process did not start with the C library settings the work is counted
/// under (`zed_meter_settings::GLIBC_TUNABLES`), which would otherwise give a verdict other than
/// the one `tools/run_tests.sh` gives. A binary started without them starts itself again with
/// them before `main` (crate `zed-meter-settings`), so this stops only where that could not
/// happen: a setuid binary, an `execve` that failed, `GLIBC_TUNABLES` changed by hand, a thread
/// already running when the binary started (a library preloaded with `LD_PRELOAD` that starts
/// one; PROOF-meter-no-thread-before-main), or a run under valgrind, which the variable must
/// reach before valgrind starts (TOOL-meter-reexec-profilers).
#[cfg(target_os = "linux")]
fn stop_unless_the_settings_are_in_effect() {
    zed_alloc_count::ready_to_meter();
    if !zed_meter_settings::in_effect() {
        let args: Vec<String> = std::env::args().collect();
        // Under valgrind the arguments are those of the binary, after valgrind's own.
        let valgrind = if zed_meter_settings::running_on_valgrind() {
            "valgrind <its options> "
        } else {
            ""
        };
        panic!(
            "this scaling test counts work under the C library settings of \
             tools/run_tests.sh, and this process did not start with them, so its verdict could \
             differ from that of tools/run_tests.sh (TEST-scaling-direct-run-verdict). Run it as \
             env GLIBC_TUNABLES='{}' {valgrind}{}",
            zed_meter_settings::GLIBC_TUNABLES,
            args.join(" ")
        );
    }
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(target_os = "linux")]
pub(crate) fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: perf_event_open opens neither the instructions \
         counter nor the task clock here, and it does not run under DynamoRIO's zed_icount. Run \
         it where kernel.perf_event_paranoid is 2 or less and no sandbox refuses that system \
         call, or set ZED_METER_DRRUN and ZED_METER_ICOUNT (crate zed-meter-settings) and start \
         it with --exact"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(target_os = "macos")]
pub(crate) fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: proc_pid_rusage counts neither instructions \
         (ri_instructions) nor cycles (ri_cycles) of this process here"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(windows)]
pub(crate) fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: QueryProcessCycleTime does not count the cycles \
         of this process here"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
pub(crate) fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: the scaling tests read the counters of Linux \
         (perf_event_open), macOS (proc_pid_rusage) and Windows (QueryProcessCycleTime), and this \
         system is none of them"
    )
}

/// Stops a test whose meter counts the whole process, as `call` does on `system`, unless the
/// harness runs one test at a time: tests running beside it would add their work and bytes.
#[cfg(any(target_os = "macos", windows))]
fn stop_unless_one_test_at_a_time(system: &str, call: &str) {
    let threads = std::env::var("RUST_TEST_THREADS").ok();
    if !one_test_at_a_time(std::env::args(), threads.as_deref()) {
        panic!(
            "this scaling test cannot measure its own work: on {system} the counter of work \
             ({call}) and the count of bytes are of the whole process, so tests running beside it \
             would add to them. Run the tests one at a time: cargo test -- --test-threads=1"
        )
    }
}

/// Whether libtest, given the arguments `args` (with the program's name first) and the value
/// `threads` of `RUST_TEST_THREADS`, runs one test at a time. Its option `--test-threads N` or
/// `--test-threads=N` overrides the variable, and with neither it runs as many tests at once as
/// the machine has processors.
#[cfg_attr(
    not(any(test, target_os = "macos", windows)),
    expect(dead_code, reason = "only macOS and Windows measure the whole process")
)]
pub(crate) fn one_test_at_a_time(
    args: impl IntoIterator<Item = String>,
    threads: Option<&str>,
) -> bool {
    let mut args = args.into_iter();
    let mut option = None;
    while let Some(arg) = args.next() {
        if arg == "--test-threads" {
            option = args.next();
        } else if let Some(n) = arg.strip_prefix("--test-threads=") {
            option = Some(n.to_owned());
        }
    }
    option.as_deref().or(threads).map(str::trim) == Some("1")
}

/// `n` passes of a loop that the compiler cannot remove.
pub(crate) fn spin(n: u64) {
    for i in 0..n {
        black_box(i);
    }
}

/// Runs `f` on a thread of its own with a stack of `stack` bytes. The bytes the thread allocates
/// count in this thread's count, as those of every thread it starts do.
pub fn on_a_thread<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    counted_on_a_thread(stack, f).0
}

/// The line a check prints once, as it ends, passed or failed (TEST-bench-split): `bench <what>
/// n=<n> ns=<small>/<large> instr=<small>/<large> bytes=<small>/<large> ratio=<ratio>`, where
/// `ns` is the least elapsed time of the runs of each size in the last measurement (see
/// [`counted_on_a_thread`]), `instr` the least count of the meter (`work=` for a meter of
/// processor time or cycles, which are not instructions), `bytes` the least bytes, and `ratio`
/// that of the count. `n` is `-` for a [`compare`]. A guard that prints on drop prints the line on
/// every way out of a check, a panic included, with what was measured last; a check that panics
/// before its first measurement prints none. The time is never a pass condition.
struct BenchLine<'a> {
    what: &'a str,
    n: Option<usize>,
    key: &'static str,
    last: Option<Measured>,
}

/// One measurement of a check, for [`BenchLine`].
#[derive(Clone, Copy)]
struct Measured {
    ns: (u64, u64),
    units: (u64, u64),
    bytes: (u64, u64),
}

impl BenchLine<'_> {
    fn text(&self) -> Option<String> {
        let Measured { ns, units, bytes } = self.last?;
        let n = self.n.map_or("-".into(), |n| n.to_string());
        Some(format!(
            "bench {} n={n} ns={}/{} {}={}/{} bytes={}/{} ratio={:.3}",
            self.what,
            ns.0,
            ns.1,
            self.key,
            units.0,
            units.1,
            bytes.0,
            bytes.1,
            units.1 as f64 / units.0.max(1) as f64
        ))
    }
}

impl Drop for BenchLine<'_> {
    fn drop(&mut self) {
        if let Some(line) = self.text() {
            eprintln!("{line}");
        }
    }
}

/// [`on_a_thread`], returning the bytes the thread allocated too, and the elapsed time of `f`
/// in nanoseconds, by [`Instant`] inside the thread from just before `f` is called to just after
/// it returns: the start of the thread and the waiting for it are not timed. The time is reported
/// by the checks, never held to a limit: it changes with the load, which the count of
/// instructions does not (see the module's documentation). A panic in `f` goes on in the caller,
/// with its own message.
fn counted_on_a_thread<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> (T, u64, u64) {
    // The run, the start of its thread, and the threads it starts allocate from heaps of their
    // own, whose instructions per call depend on nothing but their own calls
    // (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
    zed_alloc_count::metered(|| counted_in_scope(stack, f))
}

/// [`counted_on_a_thread`] inside its metered heap.
fn counted_in_scope<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> (T, u64, u64) {
    on_a_stack(stack, || {
        let start = zed_alloc_count::allocated();
        let clock = Instant::now();
        let out = f();
        let ns = u64::try_from(clock.elapsed().as_nanos()).unwrap_or(u64::MAX);
        (out, zed_alloc_count::allocated() - start, ns)
    })
}

/// Runs `f` on a thread of its own with a stack of `stack` bytes and waits for it: for a test
/// whose run needs a stack of a given size (a deep input, or the 2 MiB of a test thread whatever
/// `RUST_MIN_STACK` says). The thread takes the test's name, which libtest gives its thread, so
/// a note of [`hold`] names the test. A panic in `f` goes on in the caller with its own message
/// and payload, which a `join().unwrap()` would replace with "called `Result::unwrap()` on an
/// `Err` value: Any { .. }". Nothing is metered: [`on_a_thread`] runs in the metered heap, for
/// the runs a check measures.
pub fn on_a_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let mut thread = std::thread::Builder::new().stack_size(stack);
        if let Some(name) = std::thread::current().name() {
            thread = thread.name(name.to_owned());
        }
        let run = thread
            .spawn_scoped(scope, f)
            .expect("starting the thread of a run");
        run.join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// The inputs `make` gives at sizes `n` and `FACTOR * n`, built before any run is timed, so
/// that a check times the pass and not the building of its input.
pub fn inputs<T>(n: usize, make: impl Fn(usize) -> T) -> std::collections::HashMap<usize, T> {
    [n, FACTOR * n].into_iter().map(|m| (m, make(m))).collect()
}

/// [`check`] of `run` on the input `make` gives at each size, built before any run is measured,
/// and only at the sizes this process runs (`sizes_run_here`): a count of instructions runs
/// the size 8n in a new process (see `compare_by`), which builds the input at 8n and, for each
/// earlier check of the test, only the input at n it replays, where [`inputs`] builds both
/// sizes in every process, each process building an input it never reads
/// (BENCH-follow-group-near-60s). [`inputs`] stays for the checks that read their inputs
/// otherwise (309 call sites name its map's type, and some check every input outside the runs).
///
/// Complexity tradeoff: COMPLEXITY.md row BENCH-follow-group-near-60s. Naive ([`inputs`]): the
/// test's set-up for a check at place `k` costs `(k + 2) (B(n) + B(8n))` across its processes,
/// `B` the cost of building one input. New: `B(n) + B(8n)` for the check itself and `B(n)` for
/// each later check that replays it; no run measured changes, since each measured run reads the
/// input it read before, built before its phase as before.
pub fn check_inputs<T: Sync>(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> T,
    run: impl Fn(&T) + Sync,
) {
    check_order_inputs(what, n, 1, make, run)
}

/// [`check_inputs`] for work of order `n^power`, as [`check_order`] is [`check`] for it.
pub fn check_order_inputs<T: Sync>(
    what: &str,
    n: usize,
    power: u32,
    make: impl Fn(usize) -> T,
    run: impl Fn(&T) + Sync,
) {
    let mut meter = Meter::new();
    let fresh = meter.fresh && meter.repeats() == (1, 1);
    let (at_n, at_8n) = sizes_run_here(fresh);
    let (small, large) = (at_n.then(|| make(n)), at_8n.then(|| make(FACTOR * n)));
    fn input<'a, T>(built: &'a Option<T>, what: &str, size: usize) -> &'a T {
        built.as_ref().unwrap_or_else(|| {
            panic!(
                "{what}: the input at {size} was not built, since this check was to run that size \
                 in a new process of its test, which ran no test: this thread's name is not that \
                 of a test of this binary; run the check on the test's thread, whose name \
                 `scaling::on_a_stack` and `alone` keep"
            )
        })
    }
    check_by(&mut meter, Measures::Both, what, n, power, |k| {
        run(if k == n {
            input(&small, what, n)
        } else {
            input(&large, what, k)
        })
    });
}

/// [`check_order_fresh`] of `run` on what `make` builds for each size, at power 1, for an input
/// that the run reads and does not change; each input is built on a thread of its own, as the
/// l01_26 benchmarks of deep types need (their inputs at 8n are built on a 2 MiB stack). The
/// input is kept after its run and released before the next is built.
pub fn check_fresh_inputs<T: Send + Sync>(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> T + Sync,
    run: impl Fn(&T) + Sync,
) {
    let make = |k: usize, _: usize| {
        std::thread::scope(|s| {
            s.spawn(|| make(k))
                .join()
                .unwrap_or_else(|p| std::panic::resume_unwind(p))
        })
    };
    check_order_fresh(what, n, 1, make, |_, input: T| {
        run(&input);
        input
    })
}

/// [`check_order`] with an input of its own for each run: `make(k, i)` builds the input of the
/// `i`-th run at size `k` (`i` from 0 at each size, so a test can give each run's types names of
/// their own), outside what is measured, so the run is cold: no fact a run finds and keeps in
/// its input (such as a row's keys) is there for the next (FAIL-ratio-meet-deep). `run(k, input)`
/// is measured; what it returns is kept until the next input is built and released then, outside
/// what is measured, so a run that should not pay for the release of its input returns it, and
/// a run that measures a release drops it. One input or output is held at a time: before each
/// run the output of the run before is released, then the run's input is built, both on the
/// thread the check is on, which built the inputs of every such test before. A size this process
/// does not run (one run in a new process, see `compare_by`) is never built here.
///
/// Why (MEM-l0126-40gb, 2026-11-22): the tests built every input of the check, [`Meter::runs`]
/// per size, before the first run, and kept all of them to the end. On a meter of processor time,
/// which a machine without a hardware counter of instructions uses (Colab VMs:
/// /sys/bus/event_source/devices has no `cpu`), that is [`TIME_RUNS`] × [`TRIES`] = 15 per size,
/// 30 held at once: `bench::deep_ops::fits_sig_takes_linear_time_in_the_depth` of l01_26 held
/// 37,066,996 kB alone at 1 test thread (hm5), against 2.49 GB where instructions are counted
/// (2 inputs), and ran a 50 GB VM out of memory at 8 test threads. Holding the [`TIME_RUNS`]
/// inputs of one size at once, built side by side, still held 11,022,424 kB for that test alone,
/// and the binary at 8 test threads 39,144,428 kB.
///
/// Complexity tradeoff: the same `make` calls as before at most (`Meter::runs` per size, fewer
/// when a measurement passes before the last), and the same runs; the inputs held at once fall
/// from `Meter::runs` per size, both sizes (30 on processor time, 2 on instructions), to 1. Wall
/// time: the builds of a size come one after another between its runs, never side by side; on a
/// count of instructions each size builds one input, as before, and on processor time the
/// [`TIME_RUNS`] builds of a size are inside the time limit of its phase
/// (`start_bench_phase`), the 5 builds at 8n against 10.5 times the phase at n, which holds the
/// 5 builds at n.
pub fn check_order_fresh<T: Send, O: Send>(
    what: &str,
    n: usize,
    power: u32,
    make: impl Fn(usize, usize) -> T + Sync,
    run: impl Fn(usize, T) -> O + Sync,
) {
    let what = format!("{what}: sizes {n} and {}", FACTOR * n);
    let bound = Bound::Order(power);
    let (meter, sizes) = (&mut Meter::new(), (n, FACTOR * n));
    fresh_inputs_by(
        meter,
        Measures::Both,
        Some(n),
        &what,
        bound,
        sizes,
        &make,
        &run,
    )
}

/// [`check_order_fresh`] without the bytes allocated, as [`check_instructions_only`] is
/// [`check_order`] without them.
pub fn check_instructions_only_fresh<T: Send, O: Send>(
    what: &str,
    n: usize,
    power: u32,
    make: impl Fn(usize, usize) -> T + Sync,
    run: impl Fn(usize, T) -> O + Sync,
) {
    let what = format!("{what}: sizes {n} and {}", FACTOR * n);
    let bound = Bound::Order(power);
    let (meter, sizes) = (&mut Meter::new(), (n, FACTOR * n));
    fresh_inputs_by(
        meter,
        Measures::WorkOnly,
        Some(n),
        &what,
        bound,
        sizes,
        &make,
        &run,
    )
}

/// [`compare`] of `run` at the sizes `small` and `large` with an input of its own for each run,
/// as [`check_order_fresh`] gives them, for a test whose larger size is not 8 times the smaller.
pub fn compare_fresh<T: Send, O: Send>(
    what: &str,
    power: u32,
    (small, large): (usize, usize),
    make: impl Fn(usize, usize) -> T + Sync,
    run: impl Fn(usize, T) -> O + Sync,
) {
    let bound = Bound::Order(power);
    let (meter, sizes) = (&mut Meter::new(), (small, large));
    fresh_inputs_by(meter, Measures::Both, None, what, bound, sizes, &make, &run)
}

/// [`check_order_fresh`] by the given meter, measures, bound and sizes.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fresh_inputs_by<T: Send, O: Send>(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    (small, large): (usize, usize),
    make: &(dyn Fn(usize, usize) -> T + Sync),
    run: &(dyn Fn(usize, T) -> O + Sync),
) {
    /// What a check holds between its runs: the input built for the next run, of its size, or
    /// what the last run returned.
    enum Held<T, O> {
        Nothing,
        Input(usize, T),
        Output(O),
    }
    let held = std::sync::Mutex::new(Held::<T, O>::Nothing);
    let lock = || held.lock().unwrap_or_else(|e| e.into_inner());
    // How many inputs of each size have been built: the `i` of the next.
    let built = (AtomicUsize::new(0), AtomicUsize::new(0));
    let prepare = |is_large: bool| {
        let (k, count) = if is_large {
            (large, &built.1)
        } else {
            (small, &built.0)
        };
        // Released before the next input is built, so that one is held at a time.
        drop(std::mem::replace(&mut *lock(), Held::Nothing));
        let input = make(k, count.fetch_add(1, Relaxed));
        *lock() = Held::Input(k, input);
    };
    let read_at = |k: usize| {
        let input = match std::mem::replace(&mut *lock(), Held::Nothing) {
            Held::Input(size, input) => {
                assert_eq!(
                    size, k,
                    "{what}: the input built is of size {size}, not {k}"
                );
                input
            }
            Held::Nothing | Held::Output(_) => {
                panic!("{what}: no input at size {k}: a run with no `prepare` before it")
            }
        };
        let out = run(k, input);
        *lock() = Held::Output(out);
    };
    compare_by_dyn(
        meter,
        measures,
        n,
        what,
        bound,
        &|| read_at(small),
        &|| read_at(large),
        &prepare,
    );
}

/// Which of the sizes n and 8n of the check this thread enters next, by a meter that runs each
/// size in a new process when `fresh` is true, run in this process, as [`compare_by`] places
/// them: in a process a check started for its test (`target`), each check before the target's
/// place runs its size n only (and 8n when not `fresh`, as [`replay_or_measure`] replays it),
/// and the target check its measured size only; with no target, a `fresh` check on a test's
/// thread runs its size 8n in a new process, and its size n too unless this process runs the
/// test alone ([`runs_alone`]); anything else runs both here.
///
/// Proof that a size run here is reported as run here, case by case of [`compare_by_dyn`], whose
/// branches this follows: (1) no test name, or `main`: `enter_check` gives `None` and
/// [`compare_measured`] runs both sizes with `at` `None`: (true, true). (2) A target for this
/// test: `enter_check` gives the place `j`, the length of the test's list of checks before its
/// push, which is the length read here, as nothing between this read and that push enters a
/// check on this thread (the build of the inputs enters none: a check inside `make` would run
/// here first and be counted first, and both places then match, as both read after it).
/// `replay_or_measure` runs `small` and, unless `fresh`, `large` for `j < k`; for `j == k` only
/// the measured run; `j > k` is not reached, since the process ends at `k` (both run, to be
/// safe). (3) A target for another test: `at` `None`, both here. (4) No target and `fresh`:
/// `at` is given, so the run at 8n is in a new process, and the run at n is too when
/// `runs_alone` is false; each falls back to this process only when the new process ran no
/// test, which [`run_in_a_new_process`] gives for a thread whose name is not a test's (the
/// fallback reads an input not built and panics, naming the cause, never measuring a build).
/// (5) No target and not `fresh`: `at` `None`, both here. `fresh` here is computed as in
/// [`compare_by_dyn`], from the same meter.
pub(crate) fn sizes_run_here(fresh: bool) -> (bool, bool) {
    let thread = std::thread::current();
    let Some(test) = thread.name().filter(|name| *name != "main") else {
        return (true, true);
    };
    let j = OUTCOMES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(test)
        .map_or(0, Vec::len);
    match fresh_target() {
        Some((k, large, target, _)) if target == test => match j.cmp(k) {
            std::cmp::Ordering::Less => (true, !fresh),
            std::cmp::Ordering::Equal => (!large, *large),
            std::cmp::Ordering::Greater => (true, true),
        },
        Some(_) => (true, true),
        None if fresh => (runs_alone(test), false),
        None => (true, true),
    }
}

/// `base + 37 i^2 mod p` for `i < k`, distinct for `k <= (p + 1) / 2` when `p` is a prime other
/// than 37: `37 i^2 = 37 j^2 (mod p)` gives `p | (i - j)(i + j)`, and for `0 <= i < j < k` both
/// factors lie in `1..p`. Weights for the inputs of a scaling check that must not repeat at
/// either size: where the small size has distinct weights and the large one repeats some, the
/// atoms of equal weight can share a color, and only the large size pays the test of those ties
/// in `project_each` (PRES-project-each-naming), so the two sizes take two paths.
pub fn squares_mod(k: usize, base: i64, p: i64) -> Vec<i64> {
    (0..k as i64).map(|i| base + 37 * i * i % p).collect()
}

/// [`check_order`] for work of order `n` or `n log n`: every pass of the compiler and runtime.
pub fn check(what: &str, n: usize, run: impl Fn(usize) + Sync) {
    check_order(what, n, 1, run)
}

/// Runs `run` at sizes `n` and `FACTOR * n` and panics when the larger does [`limit`]`(power)`
/// times the work or more (as [`compare`] holds it), or allocates that many times the bytes or
/// more, or allocates none on its thread. `power` is the power of n in the order the work is
/// defined to have: for a Zed program, that of its own algorithm, so an O(n) operation in an
/// O(n) loop has power 2. `what` names the pass and its size.
pub fn check_order(what: &str, n: usize, power: u32, run: impl Fn(usize) + Sync) {
    check_by(&mut Meter::new(), Measures::Both, what, n, power, run)
}

/// [`check_order`] without the bytes allocated, for a run that allocates nothing, or for a test
/// whose bytes grow faster than its order for a known cause, recorded in COMPLEXITY.md with the
/// item that fixes it; the call site names that item in a comment.
pub fn check_instructions_only(what: &str, n: usize, power: u32, run: impl Fn(usize) + Sync) {
    check_by(&mut Meter::new(), Measures::WorkOnly, what, n, power, run)
}

/// [`check_order`] by the given meter and measures, for work of order `n^power`.
/// The body is [`check_by_dyn`], which is not generic: a generic body is compiled again for
/// each test's closure, and in a test binary those copies share one large codegen unit that is
/// optimized again after any edit that moves a line of the test file (BUILD-study: 11 to 16 s
/// of LLVM per such edit of l01_26, about 4 s with one copy). The call through `&dyn` costs
/// one indirect call per run, which no measured ratio can see.
pub(crate) fn check_by(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    n: usize,
    power: u32,
    run: impl Fn(usize) + Sync,
) {
    check_by_dyn(meter, measures, what, n, power, &run)
}

/// [`check_by`], compiled once.
fn check_by_dyn(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    n: usize,
    power: u32,
    run: &(dyn Fn(usize) + Sync),
) {
    let what = format!("{what}: sizes {n} and {}", FACTOR * n);
    let (small, large) = (|| run(n), || run(FACTOR * n));
    compare_by_dyn(
        meter,
        measures,
        Some(n),
        &what,
        Bound::Order(power),
        &small,
        &large,
        &|_| {},
    );
}

/// Panics when `large`, the run at size 8n, does [`limit`]`(power)` times the work of `small`,
/// the run at size n, or more, or allocates that many times its bytes or more, or allocates none
/// on its thread; for a test whose input is not made from n by one function, as [`check`]'s is.
/// `what` names the pass and its two sizes. The limit is of instructions: a meter of processor
/// time or cycles allows [`TIME_ALLOWANCE`] times the work, and the bytes are held to the limit
/// itself. A test that counts its own measure, not instructions, holds it by [`hold`].
pub fn compare(what: &str, power: u32, small: impl Fn() + Sync, large: impl Fn() + Sync) {
    compare_by(
        &mut Meter::new(),
        Measures::Both,
        None,
        what,
        Bound::Order(power),
        small,
        large,
    )
}

/// [`compare`] for two runs that are not one pass at n and 8n, such as two methods at one size:
/// panics when `second` does more than `limit` times the work of `first`, or allocates more than
/// `limit` times its bytes. `why` says where the limit comes from. Benchmarks call it to compare
/// two methods or two shapes of one input at one size (l01_23, l01_26, l01_38, l01_39 and others).
pub fn compare_costs(
    what: &str,
    why: &str,
    limit: f64,
    first: impl Fn() + Sync,
    second: impl Fn() + Sync,
) {
    compare_by(
        &mut Meter::new(),
        Measures::Both,
        None,
        what,
        Bound::Given(limit, why),
        first,
        second,
    )
}

/// What a comparison holds the ratio of its two runs to.
#[derive(Clone, Copy)]
pub(crate) enum Bound<'a> {
    /// A pass at n and 8n of order `n^power`: under [`limit`]`(power)`, with the note of
    /// [`hold`] from [`PREFERRED`] up.
    Order(u32),
    /// Two runs that are not one pass at n and 8n: at most the limit, for the reason given.
    Given(f64, &'a str),
}

/// The variable that makes a process of a test binary the one a check started for one of its
/// runs (see [`compare_by`]): `<k>\t<size>\t<test>\t<what>`, the check's place among the checks
/// of the test `test`, counted from 0, the run it measures (`8n`, or `n` when the process that
/// started it may run other tests, see [`runs_alone`]), and its `what`. Variables
/// [`FRESH_FAILED`]`<j>` give the panic message of each earlier check `j` of the test that
/// panicked in the process that started it.
const FRESH_VAR: &str = "ZED_SCALING_FRESH";

/// The prefix of the variables that give the message of each earlier check that panicked; see
/// [`FRESH_VAR`].
const FRESH_FAILED: &str = "ZED_SCALING_FRESH_FAILED_";

/// The head of the line a process started for a run at 8n writes to its standard output, with
/// its counts: `zed-scaling-fresh\t<units>\t<bytes>\t<ns>`.
const FRESH_LINE: &str = "zed-scaling-fresh";

/// The check this process was started to run, as [`FRESH_VAR`] names it: its place, whether it
/// measures the run at 8n (else the run at n), its test and its `what`; `None` in a process no
/// check started.
fn fresh_target() -> Option<&'static (usize, bool, String, String)> {
    static TARGET: std::sync::OnceLock<Option<(usize, bool, String, String)>> =
        std::sync::OnceLock::new();
    TARGET
        .get_or_init(|| {
            let value = std::env::var(FRESH_VAR).ok()?;
            let mut parts = value.splitn(4, '\t');
            let k = parts.next()?.parse().ok()?;
            let large = match parts.next()? {
                "8n" => true,
                "n" => false,
                _ => return None,
            };
            Some((k, large, parts.next()?.to_owned(), parts.next()?.to_owned()))
        })
        .as_ref()
}

/// Whether this process runs the test `test` and no other, as tools/run_tests.sh runs each
/// benchmark (`<binary> --exact <test> --nocapture`) and as [`run_in_a_new_process`] starts
/// one: its arguments are `--exact`, `test` as the only filter, and only flags that change the
/// output or the number of test threads. Any other argument, known or not, gives false
/// (FAIL-lr4-bench-annotation-update).
///
/// Proof that true means no other test runs here: libtest with `--exact` runs the tests whose
/// whole name equals a filter, the one filter is `test`, and a test binary's names are unique;
/// `--nocapture`, `--show-output`, `--quiet`/`-q` change what is printed and `--test-threads=`
/// how many threads run the tests selected, and none of them selects a test. A false answer
/// where the process does run the test alone costs one more process start (see
/// [`compare_measured`]), never a wrong count.
fn runs_alone(test: &str) -> bool {
    let (mut exact, mut named) = (false, false);
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--exact" => exact = true,
            "--nocapture" | "--show-output" | "--quiet" | "-q" => {}
            a if a == test => named = true,
            a if a.starts_with("--test-threads=") => {}
            _ => return false,
        }
    }
    exact && named
}

/// For each test, the checks it has entered in this process, in order: the message of each
/// that panicked, `None` for one that passed or has not ended.
static OUTCOMES: std::sync::Mutex<std::collections::BTreeMap<String, Vec<Option<String>>>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// The test this thread runs, as libtest names its thread (with any number of test threads) and
/// [`on_a_thread`] and [`alone`] pass the name on, and the place of the check now entered among
/// the checks of that test, counted from 0. A thread with no name, or libtest's `main` (a test
/// binary run with no harness), has no test.
fn enter_check() -> Option<(String, usize)> {
    let thread = std::thread::current();
    let test = thread.name().filter(|name| *name != "main")?.to_owned();
    let mut outcomes = OUTCOMES.lock().unwrap_or_else(|e| e.into_inner());
    let checks = outcomes.entry(test.clone()).or_default();
    checks.push(None);
    Some((test, checks.len() - 1))
}

/// Records that the check at place `j` of `test` panicked with `payload`.
fn note_panic(test: &str, j: usize, payload: &(dyn std::any::Any + Send)) {
    let message = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap_or_else(|| "a panic with no message".to_owned());
    let mut outcomes = OUTCOMES.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(slot) = outcomes.get_mut(test).and_then(|checks| checks.get_mut(j)) {
        *slot = Some(message);
    }
}

/// The command that starts `exe`, this test binary, as the process of one check's run
/// ([`run_in_a_new_process`]); on Linux that process is killed when this one ends.
///
/// Why: tools/bench_limit.sh stops a benchmark past its limit by signaling the test binary. Until
/// 2026-11-20 it signaled that pid only; the test binary died, its process for the run at 8n
/// passed to systemd and ran on (l01_39a_bit_words, rung 2, sizes 600 and 4800: 19 minutes, 67 to
/// 71 GB, killed by hand). Any other way the test binary can die (an outer `timeout` that signals
/// one pid, the OOM killer, a kill by pid) left the same orphan. So the child asks the kernel for
/// SIGKILL when its parent ends, `prctl(PR_SET_PDEATHSIG, SIGKILL)`, set between the fork and the
/// exec ([`zed_meter_settings::kill_with_parent`], which holds the kernel's promise, the proof
/// that a parent dying between the fork and the prctl is caught too, and the unsafe hook; the
/// workspace forbids unsafe code in this crate). tools/bench_limit.sh now signals the processes
/// under the binary too, as a second guard. The signal comes when the thread that forks ends:
/// here the thread that calls `Command::output`, which waits there until the child ends, so
/// while this process lives the signal never comes early.
///
/// Test: scaling_tests::a_fresh_child_ends_when_its_parent_is_killed (a child of a parent
/// killed with SIGKILL ends within 5 s; it failed before this).
pub(crate) fn fresh_command(exe: &std::path::Path) -> std::process::Command {
    let mut command = std::process::Command::new(exe);
    zed_meter_settings::kill_with_parent(&mut command);
    command
}

/// Runs the run at 8n (`large`) or at n of the check at place `k` of `test` in a new process of
/// this test binary, which runs the test alone up to that check (see [`compare_by`]), and gives
/// the work, the bytes and the elapsed time it measured there. Earlier checks of the test that
/// panicked here panic with the same message there. `None` when the new process ran no test:
/// the thread's name is not that of a test (a thread the test named itself), so the run stays
/// in this process.
fn run_in_a_new_process(test: &str, k: usize, large: bool, what: &str) -> Option<(Work, u64, u64)> {
    let size = if large { "8n" } else { "n" };
    let exe = std::env::current_exe().expect("this test binary");
    let mut command = fresh_command(&exe);
    command.args([test, "--exact", "--test-threads=1", "--quiet"]);
    // What this process was itself given as a process for one check, and the files a check
    // writes to, which the check writes to from this process.
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with(FRESH_VAR) {
            command.env_remove(key);
        }
    }
    command.env_remove(RATIOS_FILE).env_remove(BENCH_LIMIT_FILE);
    command.env(FRESH_VAR, format!("{k}\t{size}\t{test}\t{what}"));
    let outcomes = OUTCOMES.lock().unwrap_or_else(|e| e.into_inner());
    for (j, message) in outcomes[test][..k].iter().enumerate() {
        if let Some(message) = message {
            command.env(format!("{FRESH_FAILED}{j}"), message);
        }
    }
    drop(outcomes);
    let out = command.output().unwrap_or_else(|e| {
        panic!(
            "{what}: starting {} for the run at {size}: {e}",
            exe.display()
        )
    });
    let stdout = String::from_utf8_lossy(&out.stdout);
    let counts = stdout.lines().find_map(|line| {
        let mut fields = line.strip_prefix(FRESH_LINE)?.split('\t').skip(1);
        let mut next = || fields.next()?.parse::<u64>().ok();
        Some((next()?, next()?, next()?))
    });
    let Some((units, bytes, ns)) = counts else {
        if out.status.success() && stdout.lines().any(|line| line == "running 0 tests") {
            return None;
        }
        panic!(
            "{what}: the run at {size}, in a new process of this test binary running {test} \
             alone up to this check, gave no count ({}); its output:\n{stdout}\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    };
    Some((Work { units, bytes }, bytes, ns))
}

/// In a process started for the run at 8n (`measure_large`), or at n, of the check at place `k`
/// of this test: the check at place `j` does what it did in the process that started this one,
/// so that the check at `k` starts from that process's state. Before `k` it runs its run at n,
/// and its run at 8n too when that ran in that process (`fresh` false), unmeasured, and panics
/// with the message it panicked with there, if it did; at `k` it measures the run it was
/// started for, writes the counts and ends the process. `prepare` runs before each run here, as
/// in [`compare_by_dyn`].
#[allow(clippy::too_many_arguments)]
fn replay_or_measure(
    meter: &mut Meter,
    (k, measure_large, test, target): &(usize, bool, String, String),
    j: usize,
    what: &str,
    fresh: bool,
    small: &(dyn Fn() + Sync),
    large: &(dyn Fn() + Sync),
    prepare: &(dyn Fn(bool) + Sync),
) {
    use std::io::Write;
    if j < *k {
        prepare(false);
        alone(&small);
        if !fresh {
            prepare(true);
            alone(&large);
        }
        if let Ok(message) = std::env::var(format!("{FRESH_FAILED}{j}")) {
            panic!("{message}");
        }
        return;
    }
    assert!(
        j == *k && what == target,
        "{what}: this process was started for a run of the check `{target}`, place {k} of \
         {test}, and came to the check at place {j} as that place; a test whose checks run in \
         an order that changes from run to run cannot run its runs in a new process"
    );
    let run = if *measure_large { large } else { small };
    let (bytes, ns) = (Cell::new(0), Cell::new(0));
    let work = meter.least(
        || prepare(*measure_large),
        || {
            let (b, n) = alone(&run);
            bytes.set(b);
            ns.set(n);
        },
    );
    // Written to the standard output itself, which libtest's capture of `print!` does not hold,
    // on a line of its own after what libtest printed.
    let mut stdout = std::io::stdout().lock();
    let (units, bytes, ns) = (work.units, bytes.get(), ns.get());
    writeln!(stdout, "\n{FRESH_LINE}\t{units}\t{bytes}\t{ns}")
        .and_then(|()| stdout.flush())
        .expect("writing the counts of the run");
    std::process::exit(0);
}

/// [`compare`] by the given meter and measures. Each run is [`alone`]. A count of instructions
/// runs each size once, the smaller first, and measures once (author A160, 2026-11-20; see
/// [`Meter::repeats`]); processor time and cycles take the fastest of [`TIME_RUNS`] runs of
/// each size and up to [`TRIES`] measurements. The bytes do not change with load, so the first
/// measurement over the limit fails. The runs at each size are a phase with a time limit of its
/// own (see [`start_bench_phase`]).
///
/// On a count of instructions both runs are the first of their size, so a memo that outlives a
/// run's thread (a table the process keeps and does not key by thread, or one in the test's
/// input, such as a `Db`'s results or a type's printed text) is filled at both sizes alike; a
/// meter of processor time or cycles, whose later runs find it filled, holds the bytes of the
/// first run of each size to the limit too, but not their work.
///
/// What the process builds once for all threads and keeps (a `OnceLock`, a global table: the
/// grammar, an interner) was filled by the run at n before the run at 8n began, so in one
/// process it counted in the run at n only: a set-up that grows faster than the pass, hidden in
/// such a memo, went unseen (TEST-scaling-cold-shared-memo). So on a count of instructions the
/// run at 8n runs in a new process of the test binary ([`run_in_a_new_process`]), which runs the
/// same test alone up to this check and measures there the run at 8n in place of the run at n:
/// both runs measured then start from one state, that of this process as the check began, and
/// each pays what the process builds on first use, at its own size. The proof that the state is
/// the same: a test is a function of what its process holds as it starts and of what its checks
/// return. The new process starts as this one did (the same binary, environment and arguments
/// that select this test), libtest runs the test on one thread named after it, and each earlier
/// check `j` of the test ([`replay_or_measure`]) runs there the runs this process ran (its run at
/// n, and its run at 8n where that ran here), unmeasured, and returns or panics as it did here
/// ([`FRESH_FAILED`]); so the test reaches check `k` with the memos this process held at the
/// start of check `k`, given that the test does the same thing from run to run (a check that
/// finds the wrong check at its place says so). What the process held from other tests running
/// beside this one is not there, as it is not in a run of the test alone; so when this process
/// may run other tests ([`runs_alone`] false: a run of the whole binary, or a filter matching
/// several tests), the run at n moves to a new process of its own too, started the same way. Both
/// runs measured then start from one state, that of a process running this test alone up to
/// check `k`. Kept here, the run at n found what earlier tests built and the run at 8n paid for
/// it: the l01_08_parser benches `a_long_annotation_list_is_linear` and
/// `a_long_update_path_is_linear` ran in one process gave 1,949,230 and 21,178,567 instructions,
/// 10.9 times, against 8,285,358 and 21,178,615, 2.6 times, each run alone
/// (FAIL-lr4-bench-annotation-update, 2026-11-20): about 6.3 million instructions a process
/// spends once, on first use, which a cold run pays and a warm one does not (not traced to a
/// single memo; the parser's grammar and the table of forms are `OnceLock`s). The cost: a second
/// process start, set-up
/// and replay per check, only where the process may run other tests; tools/run_tests.sh runs
/// each benchmark alone and pays nothing more. The other way, a count
/// of each memo emptied before the run at 8n, needs every memo of every crate to be found and
/// reset, and one missed is the hole again; a new process empties all of them. The cost: a
/// process start, the test's set-up up to the check and the runs at n of its earlier checks,
/// once per check; the run at 8n is no longer than before. A check on a thread whose name is not
/// a test's (one the test named itself), or with no name, and a meter of processor time or
/// cycles, which takes the least of several runs, keep both runs in this process and the hole.
/// The body is [`compare_measured`], compiled once for the reason [`check_by`] gives.
pub(crate) fn compare_by(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    small: impl Fn() + Sync,
    large: impl Fn() + Sync,
) {
    compare_by_dyn(meter, measures, n, what, bound, &small, &large, &|_| {})
}

/// [`compare_by`], compiled once: where the run at 8n runs, and the check's outcome kept for the
/// process a later check of the test starts ([`replay_or_measure`]). `prepare(large)` runs
/// before each run of `large` (`true`) or of `small` (`false`) in this process, outside what is
/// measured, as [`check_fresh_inputs`] builds the input of the run there.
#[allow(clippy::too_many_arguments)]
fn compare_by_dyn(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    small: &(dyn Fn() + Sync),
    large: &(dyn Fn() + Sync),
    prepare: &(dyn Fn(bool) + Sync),
) {
    // A meter that takes the least of several runs would start a process per run.
    let fresh = meter.fresh && meter.repeats() == (1, 1);
    let Some((test, j)) = enter_check() else {
        return compare_measured(meter, measures, n, what, bound, small, large, prepare, None);
    };
    if let Some(target) = fresh_target() {
        // A process started for one check: the checks of its test replay, and nothing else
        // starts a process.
        if target.2 == test {
            return replay_or_measure(meter, target, j, what, fresh, small, large, prepare);
        }
        return compare_measured(meter, measures, n, what, bound, small, large, prepare, None);
    }
    let at = fresh.then_some((test.as_str(), j));
    let run = std::panic::AssertUnwindSafe(|| {
        compare_measured(meter, measures, n, what, bound, small, large, prepare, at)
    });
    if let Err(payload) = std::panic::catch_unwind(run) {
        note_panic(&test, j, &*payload);
        std::panic::resume_unwind(payload);
    }
}

/// [`compare_by`]'s comparison, with the run at 8n in a new process for the check at place `at`
/// of its test when that is given (see [`compare_by`]).
#[allow(clippy::too_many_arguments)]
fn compare_measured(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    small: &(dyn Fn() + Sync),
    large: &(dyn Fn() + Sync),
    prepare: &(dyn Fn(bool) + Sync),
    at: Option<(&str, usize)>,
) {
    let (limit, why) = match bound {
        Bound::Order(power) => (limit(power), why(power)),
        Bound::Given(limit, why) => (limit, why.to_owned()),
    };
    // A comparison of its own holds its limit itself, as it did before the limit became 13 on
    // 2026-11-13.
    let over = |ratio: f64, limit: f64| match bound {
        Bound::Order(_) => ratio >= limit,
        Bound::Given(..) => ratio > limit,
    };
    let mut line = BenchLine {
        what,
        n,
        key: if meter.instructions { "instr" } else { "work" },
        last: None,
    };
    // The bytes of the first run of each size, on a meter that takes the least of several runs:
    // a memo that outlives a run's thread (kept by the process or in the test's input) is
    // filled by the first run of a size, and the later runs find the work done, so the least
    // measures memo hits. They are held to the limit as the warm-up and the first run at 8n
    // were before A160, from the runs measured, with no run added; their work is not, since
    // one run of a count that changes with load cannot give [`TRIES`] measurements. On a count
    // of instructions each size runs once, so the runs measured are the first.
    let first_bytes = (Cell::new(None), Cell::new(None));
    let mut seen = Vec::new();
    for _ in 0..meter.repeats().1 {
        // The bytes compared are those `alone` counts inside its thread, not the meter's: those
        // hold every thread the run starts, whole, but not the start of `alone`'s own thread,
        // whose bookkeeping in std depends on the other threads alive (see zed-alloc-count).
        // The least of the runs of each size, and the most of the larger for the refusal. The
        // elapsed times are the least of the same runs, for the bench line only.
        let (small_bytes, large_bytes, large_most) =
            (Cell::new(u64::MAX), Cell::new(u64::MAX), Cell::new(0));
        let (small_ns, large_ns) = (Cell::new(u64::MAX), Cell::new(u64::MAX));
        // Each size runs once on a count of instructions, n first, and each run is a phase of
        // the benchmark with a time limit of its own (author A160, 2026-11-20): the phase at n
        // has the runner's limit, and the phase at 8n max(20 s, [`LIMIT`] × t1) from its own
        // start, t1 the time the phase at n took (see [`start_bench_phase`]). Until A160 a
        // warm-up at n ran first, and the run at n measured was the second, held against the
        // first run at 8n, with a second run at 8n when the first was over the limit or at the
        // note (FAIL-scaling-cold-8n-bytes, PERF-permission-reverse-first-run): about 10 t1 for
        // a check that passed, 18 t1 for one that did not, all counted against max(20 s, 10.5
        // t1) from the start of the piece (BENCH-limit-counts-setup). The two runs measured now
        // are both the first of their size, so a memo the first run of each size fills (one the
        // process keeps, or one in the test's input) counts at both sizes alike. What the
        // process builds once for all sizes, such as the grammar or a table in a `OnceLock`,
        // counted in the run at n only, until the run at 8n of a count of instructions moved
        // to a new process that starts as this check did (see [`compare_by`]); no run outside
        // the two measured ones is added (A160).
        let phase = Instant::now();
        let set_small = |bytes: u64, ns: u64| {
            small_bytes.set(small_bytes.get().min(bytes));
            small_ns.set(small_ns.get().min(ns));
            first_bytes.0.set(first_bytes.0.get().or(Some(bytes)));
        };
        // The run at n in a new process too when this process may run other tests, which can
        // have filled what the process keeps for all threads before this check began; see
        // [`compare_by`] (FAIL-lr4-bench-annotation-update).
        // Complexity tradeoff: COMPLEXITY.md row FAIL-lr4-bench-annotation-update. Naive: the
        // run at n in this process, no extra cost, but warm against a cold run at 8n after
        // other tests (10.9 times for a linear parse). New: one more process start, set-up and
        // replay per check, only where `runs_alone` is false; the counts are those of a run of
        // the test alone.
        let small_elsewhere = at
            .filter(|(test, _)| !runs_alone(test))
            .and_then(|(test, k)| run_in_a_new_process(test, k, false, what));
        let small = match small_elsewhere {
            Some((work, bytes, ns)) => {
                set_small(bytes, ns);
                work
            }
            None => meter.least(
                || prepare(false),
                || {
                    let (bytes, ns) = alone(&small);
                    set_small(bytes, ns);
                },
            ),
        };
        // Written after the phase at n, so its work is not counted in either run's.
        start_bench_phase(Some(phase.elapsed()));
        // In a new process when `at` is given (see [`compare_by`]), which runs the test's
        // set-up again inside this phase's time limit.
        let set = |bytes: u64, ns: u64| {
            large_bytes.set(large_bytes.get().min(bytes));
            large_most.set(large_most.get().max(bytes));
            large_ns.set(large_ns.get().min(ns));
            first_bytes.1.set(first_bytes.1.get().or(Some(bytes)));
        };
        let elsewhere = at.and_then(|(test, k)| run_in_a_new_process(test, k, true, what));
        let large = match elsewhere {
            Some((work, bytes, ns)) => {
                set(bytes, ns);
                work
            }
            None => meter.least(
                || prepare(true),
                || {
                    let (bytes, ns) = alone(&large);
                    set(bytes, ns);
                },
            ),
        };
        // What follows, up to the next phase at 8n, has the runner's limit again.
        start_bench_phase(None);
        line.last = Some(Measured {
            ns: (small_ns.get(), large_ns.get()),
            units: (small.units, large.units),
            bytes: (small_bytes.get(), large_bytes.get()),
        });
        if measures == Measures::Both && large_most.get() == 0 {
            panic!(
                "{what}: the larger run allocated no bytes, on its thread or any thread it \
                 started, so its bytes cannot be compared. A run that allocates nothing is \
                 checked by check_instructions_only"
            );
        }
        // Taken once, after the first measurement.
        if let (Some(small), Some(large)) = (first_bytes.0.take(), first_bytes.1.take())
            && measures == Measures::Both
            && meter.repeats().0 > 1
        {
            let bytes = large.max(1) as f64 / small.max(1) as f64;
            if over(bytes, limit) {
                panic!(
                    "{what}: the first runs allocated {small} and {large} bytes, {bytes:.1} times \
                     the bytes; the runs after the first of a size can find its work done in a \
                     memo that outlives a run's thread, kept by the process or in the test's \
                     input, so the first runs are held to the limit too; {why}"
                );
            }
        }
        let (small_bytes, large_bytes) = (small_bytes.get(), large_bytes.get());
        // Never 0 in the ratio, as [`Meter::work`] counts them; the messages print the counts.
        let bytes = large_bytes.max(1) as f64 / small_bytes.max(1) as f64;
        let ratio = large.units as f64 / small.units as f64;
        record(
            what,
            (n, bound),
            limit,
            (small.units, large.units, ratio, meter.unit()),
            Some((small_bytes, large_bytes, bytes)),
            Some((small_ns.get(), large_ns.get())),
        );
        if measures == Measures::Both && over(bytes, limit) {
            panic!(
                "{what}: allocated {small_bytes} and {large_bytes} bytes, {bytes:.1} times the bytes; {why}"
            );
        }
        if !over(ratio, limit * meter.allowance()) {
            let held = match measures {
                Measures::Both => "",
                Measures::WorkOnly => ", not held to the limit",
            };
            let earlier = if seen.is_empty() {
                String::new()
            } else {
                format!("; before, over the limit: {}", seen.join("; then "))
            };
            // Shown by libtest's --show-output or --nocapture: a pass near the limit is seen.
            eprintln!(
                "{what}: passed: took {} and {} {}, {ratio:.1} times the work; allocated \
                 {small_bytes} and {large_bytes} bytes, {bytes:.1} times the bytes{held}; \
                 the limit is {limit:.2}{earlier}",
                small.units,
                large.units,
                meter.unit()
            );
            if let Bound::Order(power) = bound {
                note_if_near(what, meter.unit(), ratio, power);
            }
            return;
        }
        seen.push(format!(
            "{} and {}, {ratio:.1} times the work",
            small.units, large.units
        ));
    }
    let allowed = if meter.instructions {
        String::new()
    } else {
        format!(", times {TIME_ALLOWANCE} for a count that changes with load")
    };
    panic!(
        "{what}: took {} in {}; {why}{allowed}",
        seen.join("; then "),
        meter.unit()
    );
}

/// The variable naming the file a benchmark writes the start and the time limit of each of its
/// phases to, when it is set (tools/run_tests.sh --bench sets it; tools/bench_limit.sh reads
/// it). Each phase has a limit of its own, counted from its own start (author A160,
/// 2026-11-20: "The time limit applies to each phase"): the run at n has the runner's limit,
/// max(20 s, 20 s × load / cores), and the run at 8n max(that, [`LIMIT`] × t1), where t1 is the
/// time the run at n took (author P214: a fixed 20 s failed a benchmark that scaled well but was
/// large). Until A160 a benchmark had one limit, max(20 s, 10.5 × t1) counted from the start of
/// the piece, which held the set-up, the warm-up and the run at n, the run at 8n and any second
/// run at 8n against the 10.5 t1 meant for the run at 8n, so a benchmark whose ratio passed was
/// killed when t1 was above about 1.8 s and its ratio above about 9.5
/// (BENCH-limit-counts-setup). The ratio of the sizes is held to [`LIMIT`] as before.
pub const BENCH_LIMIT_FILE: &str = "ZED_BENCH_LIMIT_FILE";

/// The time limit in milliseconds that a run at 8n asks for when its run at n took `t1_ns`
/// nanoseconds: [`LIMIT`] × t1, rounded up. The runner takes the larger of this and its own
/// limit.
pub fn bench_limit_ms(t1_ns: u64) -> u64 {
    (LIMIT * t1_ns as f64 / 1e6).ceil() as u64
}

/// Starts a new phase of the benchmark's time limit, now, in the file [`BENCH_LIMIT_FILE`]
/// names, if it is set: given `t1`, the time of the run at n just measured, a phase at 8n of
/// [`bench_limit_ms`]`(t1)`; given none, a phase with the runner's limit, for what follows a run
/// at 8n (the next check's inputs and its run at n). The runner reads it at its next look,
/// within 0.1 s; tools/test_bench_limit.sh tests its side.
pub(crate) fn start_bench_phase(t1: Option<Duration>) {
    let Some(path) = std::env::var_os(BENCH_LIMIT_FILE) else {
        return;
    };
    let ms = t1.map_or(0, |t1| bench_limit_ms(t1.as_nanos() as u64));
    write_bench_phase(
        std::path::Path::new(&path),
        std::time::SystemTime::now(),
        ms,
    );
}

/// [`start_bench_phase`] to the file `path`: the line `<start> <ms>`, `start` in milliseconds
/// since 1970 (the clock tools/bench_limit.sh reads as `EPOCHREALTIME`) and `ms` the limit the
/// phase asks for, 0 for the runner's. It is written to `<path>.new` and renamed over `path`, so
/// the runner never reads the file empty or half written.
pub(crate) fn write_bench_phase(path: &std::path::Path, start: std::time::SystemTime, ms: u64) {
    let start = start
        .duration_since(std::time::UNIX_EPOCH)
        .expect("a clock past 1970")
        .as_millis();
    let new = path.with_extension("new");
    std::fs::write(&new, format!("{start} {ms}\n"))
        .and_then(|()| std::fs::rename(&new, path))
        .unwrap_or_else(|e| panic!("{BENCH_LIMIT_FILE}: writing to {}: {e}", path.display()));
}

/// The variable naming the file every check ([`check_order`], [`compare`] and the rest) appends a
/// line to for each measurement, when it is set: the test, `what`, n (`-` for [`compare`] and
/// [`hold`]), the power (`-` for [`compare_costs`]), the limit, the work of the two sizes and its
/// ratio, the unit, the bytes of the two sizes and their ratio (`-` for [`hold`]), and the elapsed
/// nanoseconds of the two sizes (`-` for [`hold`]; see `counted_on_a_thread`), separated by tabs.
/// It lists the ratios the tests measure (SCALE-ratio, TESTS-scaling-limit-13,
/// TESTS-scaling-limit-10_5) and, since TEST-bench-split, their times.
pub const RATIOS_FILE: &str = "ZED_SCALING_RATIOS";

/// Appends one measurement to the file [`RATIOS_FILE`] names, if it is set. One `write` call per
/// line to a file opened for appending, so lines of tests running at once do not mix.
fn record(
    what: &str,
    (n, bound): (Option<usize>, Bound),
    limit: f64,
    (small, large, ratio, unit): (u64, u64, f64, &str),
    bytes: Option<(u64, u64, f64)>,
    ns: Option<(u64, u64)>,
) {
    use std::io::Write;
    let Some(path) = std::env::var_os(RATIOS_FILE) else {
        return;
    };
    let thread = std::thread::current();
    let test = thread.name().unwrap_or("-");
    let n = n.map_or("-".into(), |n| n.to_string());
    let power = match bound {
        Bound::Order(power) => power.to_string(),
        Bound::Given(..) => "-".into(),
    };
    let bytes = bytes.map_or("-\t-\t-".into(), |(small, large, ratio)| {
        format!("{small}\t{large}\t{ratio:.3}")
    });
    let ns = ns.map_or("-\t-".into(), |(small, large)| format!("{small}\t{large}"));
    let line = format!(
        "{test}\t{what}\t{n}\t{power}\t{limit}\t{small}\t{large}\t{ratio:.3}\t{unit}\t{bytes}\t{ns}\n"
    );
    std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .and_then(|mut file| file.write_all(line.as_bytes()))
        .unwrap_or_else(|e| panic!("{RATIOS_FILE}: writing to {}: {e}", path.display()));
}
