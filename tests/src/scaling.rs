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
//! `malloc_keeps_no_state_from_earlier_threads` fails where it does not.
//!
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
use std::time::Duration;

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
/// thread's count too. A panic in `f` goes on in the caller.
fn alone(f: &(impl Fn() + Sync)) -> u64 {
    let stack = stacker::remaining_stack().expect("the size of this thread's stack");
    counted_on_a_thread(stack, f).1
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
type Read = Box<dyn FnMut() -> u64>;

/// Counts work in the unit the machine offers.
pub struct Meter {
    /// Reads the counter.
    read: Read,
    /// The name of the unit `read` counts in, for the messages.
    unit: &'static str,
    /// Whether the count is of instructions, which does not change with load, and not of
    /// processor time or cycles, which do.
    instructions: bool,
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
    fn first_that_moves<const N: usize>(counters: [(Read, &'static str, bool); N]) -> Option<Self> {
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
    fn repeats(&self) -> (usize, usize) {
        if self.instructions {
            (2, 1)
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

    /// How many times [`compare`] runs the smaller and the larger size, so that a test can build
    /// a fresh input for each run before any is timed.
    pub fn runs(&self) -> (usize, usize) {
        let (least, measurements) = self.repeats();
        (1 + least * measurements, least * measurements)
    }

    /// The least work and the least bytes of the runs of `f`.
    fn least(&mut self, f: impl Fn()) -> Work {
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
enum Measures {
    /// The work and the bytes allocated.
    Both,
    /// The work only, for a test whose bytes are known to grow faster: see
    /// [`check_instructions_only`].
    WorkOnly,
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(target_os = "linux")]
fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: perf_event_open opens neither the instructions \
         counter nor the task clock here. Run it where kernel.perf_event_paranoid is 2 or less \
         and no sandbox refuses that system call"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(target_os = "macos")]
fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: proc_pid_rusage counts neither instructions \
         (ri_instructions) nor cycles (ri_cycles) of this process here"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(windows)]
fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: QueryProcessCycleTime does not count the cycles \
         of this process here"
    )
}

/// Stops a test that cannot measure work, which would otherwise pass unmeasured.
#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn no_counter() -> ! {
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
fn one_test_at_a_time(args: impl IntoIterator<Item = String>, threads: Option<&str>) -> bool {
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
fn spin(n: u64) {
    for i in 0..n {
        black_box(i);
    }
}

/// Runs `f` on a thread of its own with a stack of `stack` bytes. The bytes the thread allocates
/// count in this thread's count, as those of every thread it starts do.
pub fn on_a_thread<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    counted_on_a_thread(stack, f).0
}

/// [`on_a_thread`], returning the bytes the thread allocated too. A panic in `f` goes on in the
/// caller, with its own message.
fn counted_on_a_thread<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> (T, u64) {
    let (out, bytes) = std::thread::scope(|scope| {
        // The test's name, which libtest gives its thread, so a note of [`hold`] names the test.
        let mut thread = std::thread::Builder::new().stack_size(stack);
        if let Some(name) = std::thread::current().name() {
            thread = thread.name(name.to_owned());
        }
        let counted = || {
            let start = zed_alloc_count::allocated();
            let out = f();
            (out, zed_alloc_count::allocated() - start)
        };
        let run = thread
            .spawn_scoped(scope, counted)
            .expect("starting the thread of a run");
        run.join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    });
    (out, bytes)
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
fn check_by(
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
enum Bound<'a> {
    /// A pass at n and 8n of order `n^power`: under [`limit`]`(power)`, with the note of
    /// [`hold`] from [`PREFERRED`] up.
    Order(u32),
    /// Two runs that are not one pass at n and 8n: at most the limit, for the reason given.
    Given(f64, &'a str),
}

/// [`compare`] by the given meter and measures. Each run is [`alone`]. Counts of instructions
/// need the least of two runs and one measurement, and processor time the fastest of five and
/// three measurements. The bytes do not change with load, so the first measurement over the
/// limit fails.
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
fn compare_by(
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
    let warm_bytes = Cell::new(0);
    let mut warm = Some(meter.work(|| warm_bytes.set(alone(&small))));
    let mut first_runs = String::new();
    let mut seen = Vec::new();
    for _ in 0..meter.repeats().1 {
        // The bytes compared are those `alone` counts inside its thread, not the meter's: those
        // hold every thread the run starts, whole, but not the start of `alone`'s own thread,
        // whose bookkeeping in std depends on the other threads alive (see zed-alloc-count).
        // The least of the runs of each size, and the most of the larger for the refusal.
        let (small_bytes, large_bytes, large_most) =
            (Cell::new(u64::MAX), Cell::new(u64::MAX), Cell::new(0));
        let small = meter.least(|| small_bytes.set(small_bytes.get().min(alone(&small))));
        let run_large = || {
            let bytes = alone(&large);
            large_bytes.set(large_bytes.get().min(bytes));
            large_most.set(large_most.get().max(bytes));
        };
        // The first run at the larger size, before any other: its bytes are the only ones in
        // `large_bytes` until the rest of the runs.
        let first = warm.map(|warm| (warm, meter.work(run_large), large_bytes.get()));
        let large = meter.least_with(first.map(|(_, run, _)| run), run_large);
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
/// [`hold`]), the power (`-` for [`compare_costs`]), the limit, the work of the two sizes and its ratio, the unit, and the
/// bytes of the two sizes and their ratio (`-` for [`hold`]), separated by tabs. It lists the
/// ratios the tests measure (SCALE-ratio, TESTS-scaling-limit-13, TESTS-scaling-limit-10_5).
pub const RATIOS_FILE: &str = "ZED_SCALING_RATIOS";

/// Appends one measurement to the file [`RATIOS_FILE`] names, if it is set. One `write` call per
/// line to a file opened for appending, so lines of tests running at once do not mix.
fn record(
    what: &str,
    (n, bound): (Option<usize>, Bound),
    limit: f64,
    (small, large, ratio, unit): (u64, u64, f64, &str),
    bytes: Option<(u64, u64, f64)>,
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
    let line = format!(
        "{test}\t{what}\t{n}\t{power}\t{limit}\t{small}\t{large}\t{ratio:.3}\t{unit}\t{bytes}\n"
    );
    std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .and_then(|mut file| file.write_all(line.as_bytes()))
        .unwrap_or_else(|e| panic!("{RATIOS_FILE}: writing to {}: {e}", path.display()));
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// Work of order `n^1.25`, which the limit of 24 for k = 1 let pass (13.5 times at 8n), fails
    /// at n = 1000, and work of order `n log n` passes there and at n = 2000 (10.2 times).
    #[test]
    fn work_a_quarter_power_above_n_log_n_fails() {
        let n_log_n = |n: usize| spin((n as f64 * (n as f64).log2() * 50.0) as u64);
        check_instructions_only("n log n work", 1000, 1, n_log_n);
        check_instructions_only("n log n work", 2000, 1, n_log_n);
        let quarter = |n: usize| spin(((n as f64).powf(1.25) * 500.0) as u64);
        assert!(fails(|| check_instructions_only(
            "work of order n^1.25",
            1000,
            1,
            quarter
        )));
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
    /// and work of order n log n at 1000 (10.4 times) print a note, a ratio of 8 none.
    #[test]
    fn ratios_near_the_limit_pass() {
        hold("ten times", "nodes", 100, 1000, 1);
        hold("eight times", "nodes", 100, 800, 1);
        let n_log_n = |n: usize| spin((n as f64 * (n as f64).log2() * 50.0) as u64);
        check_instructions_only("n log n work", 1000, 1, n_log_n);
    }

    #[test]
    fn a_ratio_from_9_to_10_5_prints_a_note_naming_the_test() {
        let run = std::process::Command::new(std::env::current_exe().expect("this test binary"))
            .args([
                "--exact",
                "scaling::tests::ratios_near_the_limit_pass",
                "--show-output",
                "--test-threads=1",
            ])
            .output()
            .expect("running this test binary");
        let out = String::from_utf8_lossy(&run.stdout);
        assert!(run.status.success(), "{out}");
        let note = "note: scaling::tests::ratios_near_the_limit_pass: ";
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
        let runs = meter.runs();
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
                "scaling::tests::bytes_of_the_order_given_pass",
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
            let measured = s
                .spawn(|| -> Vec<u64> { (0..50).map(|_| alone(&|| linear_bytes(1000))).collect() });
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
        assert_eq!(alone(&|| linear_bytes(1000)), 8 * (2048 - 4));
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
        assert_eq!(alone(&|| linear_bytes(1000)), list);
        let spawned = || std::thread::spawn(|| linear_bytes(1000)).join().unwrap();
        let joined = alone(&spawned);
        assert!(joined >= list, "{joined}");
        // The list is allocated on the second thread down only. The starts of the threads differ
        // by the other threads alive (see zed-alloc-count), so the two counts are not compared.
        let nested = alone(&|| std::thread::spawn(spawned).join().unwrap());
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
        assert_eq!(meter.runs(), (3, 2));
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
            message
                .contains("the first runs took 1000000 and 64000000 passes, 64.0 times the work"),
            "{message}"
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
}
