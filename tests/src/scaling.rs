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
//! 8.0 times the instructions on every try.
//!
//! The count has three limits. Work in the kernel is not counted. A `rep movsb` or `rep stosb`
//! counts as one instruction or few, whatever its length, and glibc's memcpy and memset use
//! them on a CPU with erms or fsrm, so `tools/run_tests.sh` keeps glibc from them, and
//! `copies_and_fills_count_by_their_length` fails on a machine where they are hidden. The
//! instructions glibc's malloc spends depend on what earlier threads left in the arena a new
//! thread takes over and on the order the hash seed frees blocks in: one check of the same
//! program took 0.26 billion instructions (0.9%) more in some runs than in others, all of it in
//! malloc, and a difference of two such counts, of about 0.5 billion, came out 1.5 times its
//! size. So `tools/run_tests.sh` turns off malloc's cache per thread, and
//! `malloc_keeps_no_state_from_earlier_threads` fails where it does not.//!
//! Where the hardware has no counter, as in most virtual machines, [`Meter`] falls back on the
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
//! `Db`'s results or a type's printed text, or a table the process keeps for all threads, so the
//! first run of each size, which fills them, is held to the limit too: the warm-up at `n`
//! against the first run at `8n` (SCALE-first-run).

use std::cell::Cell;
use std::hint::black_box;
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
/// The tests that use it held their count under 9, or under 5 at 4n, before the limit was 13.
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
}

impl Meter {
    /// A meter of instructions where the hardware counts them, or else of the processor time of
    /// this thread and the threads it starts. With no counter at all a test cannot measure the
    /// work, so it stops; see `no_counter`.
    #[cfg(target_os = "linux")]
    pub fn new() -> Self {
        Self::open(Hardware::INSTRUCTIONS, "instructions", true)
            .or_else(|| Self::open(Software::TASK_CLOCK, "ns of processor time", false))
            .unwrap_or_else(|| no_counter())
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
                })
            })
    }

    /// The work `f` does, in instructions or nanoseconds, and the bytes it allocates on this
    /// thread, the threads it starts and the threads those start; each never 0. Off Linux both
    /// are of the whole process (see the module's documentation).
    pub fn work(&mut self, f: impl FnOnce()) -> Work {
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
    /// A count of instructions takes one run of each size and one measurement: with the warm-up
    /// at n, a check runs n twice and 8n once, about 10 times the time at n. Until
    /// TEST-scaling-runs it took the least of two runs of each size, 3 runs at n and 2 at 8n,
    /// about 19 times the time at n, so a benchmark whose time at n was the 1 s the author asks
    /// for (P169, P175) did not fit in the 20 s a piece may take. The least of two was meant to
    /// remove the spread of single runs, but measured it barely changes the ratio: 58 checks in
    /// 57 benchmarks sampled from 19 groups (checker, runtime, Presburger, e-graph, parser,
    /// lowering, the kernel), each run in 5 processes, 295 comparisons (2026-11-14, under
    /// tools/run_tests.sh's malloc and memcpy settings, load 23 to 32). The ratio of the first
    /// run at 8n to the second at n differed from the ratio of the least of two runs at each
    /// size by at most 0.88% in instructions (mean 0.03%, the largest in `l01_29_diagnostics`'
    /// `rejecting_many_binders_that_name_types_scales`, whose single runs differ by up to 1.4%
    /// in one process) and by at most 0.05% in bytes, both under the 1% the row allowed. Across
    /// the 5 processes the single-run ratio of each check spread by at most 0.52%, the
    /// least-of-two ratio by up to 1.26%. The warm-up stays, held against the first run at 8n,
    /// which is now also the measured run at 8n (see [`compare_by`]). Processor time and cycles
    /// change with load, so they keep the fastest of five and [`TRIES`] measurements.
    ///
    /// The one run at 8n is cold while the run at n follows the warm-up, so a memo filled by the
    /// first run of each size (one the process keeps, or one in the test's input) counts at 8n
    /// only. A count of instructions therefore runs 8n a second time when the comparison of the
    /// first is over the limit, and takes the least of the two (FAIL-scaling-cold-8n-bytes; see
    /// [`Meter::again_when_over`]).
    fn repeats(&self) -> (usize, usize) {
        if self.instructions {
            (1, 1)
        } else {
            (5, TRIES)
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

    /// Whether a comparison whose one run at the larger size is over the limit runs that size
    /// once more and takes the least of the two: on a count of instructions, which takes one run
    /// of each size (see [`Meter::repeats`]). Processor time already takes the fastest of five.
    pub(crate) fn again_when_over(&self) -> bool {
        self.instructions
    }

    /// At most how many times [`compare`] runs the smaller and the larger size, so that a test
    /// can build a fresh input for each run before any is timed. On a count of instructions a
    /// check that passes on its first run at the larger size leaves the last larger input unused
    /// (see `Meter::again_when_over`).
    pub fn runs(&self) -> (usize, usize) {
        let (least, measurements) = self.repeats();
        (
            1 + least * measurements,
            least * measurements + usize::from(self.again_when_over()),
        )
    }

    /// The least work and the least bytes of the runs of `f`.
    pub(crate) fn least(&mut self, f: impl Fn()) -> Work {
        self.least_with(None, f)
    }

    /// [`Meter::least`] of `first`, a run of `f` already measured, and as many more runs of `f`
    /// as make up the meter's count.
    fn least_with(&mut self, first: Option<Work>, f: impl Fn()) -> Work {
        let more = self.repeats().0 - usize::from(first.is_some());
        first
            .into_iter()
            .chain((0..more).map(|_| self.work(&f)))
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

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(target_os = "linux")]
pub(crate) fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: perf_event_open opens neither the instructions \
         counter nor the task clock here. Run it where kernel.perf_event_paranoid is 2 or less \
         and no sandbox refuses that system call"
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
    std::thread::scope(|scope| {
        // The test's name, which libtest gives its thread, so a note of [`hold`] names the test.
        let mut thread = std::thread::Builder::new().stack_size(stack);
        if let Some(name) = std::thread::current().name() {
            thread = thread.name(name.to_owned());
        }
        let counted = || {
            let start = zed_alloc_count::allocated();
            let clock = Instant::now();
            let out = f();
            let ns = u64::try_from(clock.elapsed().as_nanos()).unwrap_or(u64::MAX);
            (out, zed_alloc_count::allocated() - start, ns)
        };
        let run = thread
            .spawn_scoped(scope, counted)
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
/// `limit` times its bytes. `why` says where the limit comes from. No scaling test calls it.
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

/// [`compare`] by the given meter and measures. Each run is [`alone`]. Counts of instructions
/// need one run of each size and one measurement (see [`Meter::repeats`]), and a second run at
/// the larger size when the first is over the limit (see [`Meter::again_when_over`]), and processor time
/// the fastest of five and three measurements. The bytes do not change with load, so the first
/// measurement over the limit fails.
///
/// Before the least is taken, the first run of each size is held to the same limit: the warm-up
/// at the smaller size against the first run at the larger. A memo that outlives a run's thread
/// (a table the process keeps and does not key by thread, or one in the test's input, such as a
/// `Db`'s results or a type's printed text) is filled by the first run of a size, and every later
/// run of that size finds the work done, so the least of the runs measures memo hits. The
/// warm-up also builds what the process keeps once for all threads, such as the grammar, which
/// raises its count a little and so loosens this ratio a little at a small `n`. The bytes of the
/// first runs are held on every meter, their work only on a count of instructions, since one run
/// cannot give processor time's three measurements. The body is [`compare_by_dyn`], compiled
/// once for the reason [`check_by`] gives.
pub(crate) fn compare_by(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    small: impl Fn() + Sync,
    large: impl Fn() + Sync,
) {
    compare_by_dyn(meter, measures, n, what, bound, &small, &large)
}

/// [`compare_by`], compiled once.
fn compare_by_dyn(
    meter: &mut Meter,
    measures: Measures,
    n: Option<usize>,
    what: &str,
    bound: Bound,
    small: &(dyn Fn() + Sync),
    large: &(dyn Fn() + Sync),
) {
    let (limit, why) = match bound {
        Bound::Order(power) => (limit(power), why(power)),
        Bound::Given(limit, why) => (limit, why.to_owned()),
    };
    // A comparison of its own holds its limit itself, as it did before the limit of 13.
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
    let warm_bytes = Cell::new(0);
    let mut warm = Some(meter.work(|| warm_bytes.set(alone(&small).0)));
    let mut first_runs = String::new();
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
        let small = meter.least(|| {
            let (bytes, ns) = alone(&small);
            small_bytes.set(small_bytes.get().min(bytes));
            small_ns.set(small_ns.get().min(ns));
        });
        let run_large = || {
            let (bytes, ns) = alone(&large);
            large_bytes.set(large_bytes.get().min(bytes));
            large_most.set(large_most.get().max(bytes));
            large_ns.set(large_ns.get().min(ns));
        };
        // The first run at the larger size, before any other: its bytes are the only ones in
        // `large_bytes` until the rest of the runs.
        let first = warm.map(|warm| (warm, meter.work(run_large), large_bytes.get()));
        let mut large = meter.least_with(first.map(|(_, run, _)| run), run_large);
        // On a count of instructions the run at n measured is the second, after the warm-up, and
        // the run at 8n the first, so a memo that the first run of each size fills (kept by the
        // process or in the test's input) counts at 8n and not at n: a method that allocates
        // 8000 bytes on its first run at n and 64000 on its first at 8n, and nothing after,
        // compared 0 bytes with 64000 (FAIL-scaling-cold-8n-bytes; 20 checks of
        // l01_23_subtyping failed so). Three ways to measure 8n warm too were weighed: a warm-up
        // at 8n, or the least of two runs at 8n, each always, costs 1 + 1 + 8 + 8 = 18 times the
        // time at n (TEST-scaling-runs's 1 + 1 + 8 = 10 was cut from 19 by dropping the second run
        // at 8n); comparing the warm-up at n with the run at 8n drops the check of the second run
        // at n, which catches a first run at n that builds what the process keeps
        // (`the_bytes_of_the_second_run_at_n_are_held_against_the_run_at_8n`). Taken: run 8n
        // again only when the comparison of its first run is over the limit, in work or in
        // bytes, and take the least of the two. Its verdict is that of the least of two runs at
        // 8n always, since the least is never over when the first is not, and a passing check
        // still costs 10 times the time at n; only a check over on its cold run costs 18. A
        // passing check prints and records the ratio of the cold run at 8n, at most a little over
        // that of the least of two.
        let over_now = |large: &Work| {
            let bytes = large_bytes.get().max(1) as f64 / small_bytes.get().max(1) as f64;
            (measures == Measures::Both && over(bytes, limit))
                || over(
                    large.units as f64 / small.units as f64,
                    limit * meter.allowance(),
                )
        };
        if meter.again_when_over() && over_now(&large) {
            let again = meter.work(run_large);
            large.units = large.units.min(again.units);
            large.bytes = large.bytes.min(again.bytes);
        }
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
        if let Some((warm, run, run_bytes)) = first {
            let ratio = run.units as f64 / warm.units as f64;
            let warm_bytes = warm_bytes.get();
            let bytes = run_bytes.max(1) as f64 / warm_bytes.max(1) as f64;
            let memo = "the runs after the first of a size can find its work done in a memo \
                        that outlives a run's thread, kept by the process or in the test's \
                        input, so the first runs are held to the limit too";
            if measures == Measures::Both && over(bytes, limit) {
                panic!(
                    "{what}: the first runs allocated {warm_bytes} and {run_bytes} bytes, \
                     {bytes:.1} times the bytes; {memo}; {why}"
                );
            }
            if meter.instructions && over(ratio, limit) {
                panic!(
                    "{what}: the first runs took {} and {} {}, {ratio:.1} times the work; \
                     {memo}; {why}",
                    warm.units,
                    run.units,
                    meter.unit()
                );
            }
            first_runs = format!(
                "; the first runs took {} and {}, {ratio:.1} times the work, and allocated \
                 {warm_bytes} and {run_bytes} bytes, {bytes:.1} times the bytes",
                warm.units, run.units
            );
        }
        warm = None;
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
                 the limit is {limit:.2}{first_runs}{earlier}",
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

/// The variable naming the file every check ([`check_order`], [`compare`] and the rest) appends a
/// line to for each measurement, when it is set: the test, `what`, n (`-` for [`compare`] and
/// [`hold`]), the power (`-` for [`compare_costs`]), the limit, the work of the two sizes and its ratio, the unit, the
/// bytes of the two sizes and their ratio (`-` for [`hold`]), and the elapsed nanoseconds of the
/// two sizes (`-` for [`hold`]; see `counted_on_a_thread`), separated by tabs. It lists the
/// ratios the tests measure (SCALE-ratio, TESTS-scaling-limit-13, TESTS-scaling-limit-10_5) and,
/// since TEST-bench-split, their times.
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
