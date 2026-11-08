//! The scaling test of the rule of low complexity (DESIGN.md Part G, "Six standing rules"): a
//! pass runs at sizes n and 8n, and the larger run may do at most `24 × 8^(k−1)` times the
//! work, where `n^k` is the order the measured work is defined to have. A run of order `n^k`
//! or `n^k log n` stays near `8^k` to `1.4 × 8^k` times, and one a power of n above it near
//! `8^(k+1)`.
//!
//! Work is counted in instructions retired, in user mode, by this thread and the threads it
//! starts. The count does not change with the load on the machine. Elapsed time and processor
//! time both do, and by more for the larger run: at load 55 with half the load copying memory,
//! a linear walk of 1000 and 8000 terms took 96 times as long by the clock and 44 times by
//! processor time, because the larger run lost the caches and was preempted, and it retired
//! 8.0 times the instructions on every try.
//!
//! The count has two limits. Work in the kernel is not counted. A `rep movsb` or `rep stosb`
//! counts as one instruction or few, whatever its length, and glibc's memcpy and memset use
//! them on a CPU with erms or fsrm, so `tools/run_tests.sh` keeps glibc from them, and
//! `copies_and_fills_count_by_their_length` fails on a machine where they are hidden.
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

/// The most times the work of the first the second run may do, for work of order `n`.
pub const RATIO: f64 = 24.0;

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
        let thread = std::thread::Builder::new().stack_size(stack);
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

/// Runs `run` at sizes `n` and `FACTOR * n` and panics when the larger does more than
/// `RATIO * FACTOR^(power - 1)` times the work, or allocates more than that many times the
/// bytes, or allocates none on its thread. `power` is the power of n in the order the work is
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

/// [`check_order`] by the given meter and measures.
fn check_by(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    n: usize,
    power: u32,
    run: impl Fn(usize) + Sync,
) {
    let limit = RATIO * (FACTOR as f64).powi(power as i32 - 1);
    let why = format!(
        "for work of order n^{power} the rule of low complexity allows at most {limit} times \
         (DESIGN.md Part G)"
    );
    let what = format!("{what}: sizes {n} and {}", FACTOR * n);
    let (small, large) = (|| run(n), || run(FACTOR * n));
    compare_by(meter, measures, &what, &why, limit, small, large);
}

/// Panics when `large` does more than `limit` times the work of `small`, or allocates more than
/// `limit` times its bytes, or allocates none on its thread, for sizes that are not `n` and
/// `8n`. `why` says where the limit comes from.
pub fn compare(
    what: &str,
    why: &str,
    limit: f64,
    small: impl Fn() + Sync,
    large: impl Fn() + Sync,
) {
    compare_by(
        &mut Meter::new(),
        Measures::Both,
        what,
        why,
        limit,
        small,
        large,
    )
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
/// cannot give processor time's three measurements.
fn compare_by(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    why: &str,
    limit: f64,
    small: impl Fn() + Sync,
    large: impl Fn() + Sync,
) {
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
            if measures == Measures::Both && bytes > limit {
                panic!(
                    "{what}: the first runs allocated {warm_bytes} and {run_bytes} bytes, \
                     {bytes:.1} times the bytes; {memo}; {why}"
                );
            }
            if meter.instructions && ratio > limit {
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
        if measures == Measures::Both && bytes > limit {
            panic!(
                "{what}: allocated {small_bytes} and {large_bytes} bytes, {bytes:.1} times the bytes; {why}"
            );
        }
        let ratio = large.units as f64 / small.units as f64;
        if ratio <= limit {
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
                 the limit is {limit}{first_runs}{earlier}",
                small.units,
                large.units,
                meter.unit()
            );
            return;
        }
        seen.push(format!(
            "{} and {}, {ratio:.1} times the work",
            small.units, large.units
        ));
    }
    panic!(
        "{what}: took {} in {}; {why}",
        seen.join("; then "),
        meter.unit()
    );
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

    // Only Linux has a meter of processor time.
    #[cfg(target_os = "linux")]
    #[test]
    fn processor_time_tells_the_orders_apart_too() {
        let mut meter = Meter::of_cpu_time();
        let cpu = &mut meter;
        check_by(cpu, Measures::WorkOnly, "linear work", 100_000, 1, |n| {
            work(n, 1, 10)
        });
        assert!(fails(|| check_by(
            cpu,
            Measures::WorkOnly,
            "quadratic work",
            1000,
            1,
            |n| { work(n, 2, 2) }
        )));
    }

    /// `run` on a thread of its own, as a test on a stack of its own does.
    fn on_a_bare_thread(f: impl FnOnce() + Send) {
        std::thread::scope(|s| s.spawn(f).join().unwrap());
    }

    #[test]
    fn the_work_of_a_thread_a_run_starts_counts() {
        let quadratic = |n| on_a_bare_thread(|| work(n, 2, 2));
        assert!(fails(|| check_instructions_only(
            "quadratic work on a thread",
            1000,
            1,
            quadratic
        )));
        // Only Linux has a meter of processor time.
        #[cfg(target_os = "linux")]
        {
            let cpu = &mut Meter::of_cpu_time();
            assert!(fails(|| check_by(
                cpu,
                Measures::WorkOnly,
                "quadratic, by time",
                1000,
                1,
                quadratic
            )));
        }
    }

    #[test]
    fn a_comparison_holds_two_sizes_to_the_limit_given() {
        // Lists of 2^17 and 2^21 words at most: 16 times the work and the bytes.
        let (small, large) = (|| linear_bytes(100_000), || linear_bytes(1_600_000));
        compare("16 times", "the limit is 24", 24.0, small, large);
        assert!(fails(|| compare(
            "16 times",
            "the limit is 8",
            8.0,
            small,
            large
        )));
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
            "counted runs",
            "the limit is 24",
            24.0,
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
            " times the bytes; the limit is 24".into(),
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
            "memo runs",
            "the limit is 24",
            24.0,
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
