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
//! The second measure is the bytes a run allocates, counted by the global allocator of the test
//! binaries (the crate `zed-alloc-count`): a block counts its size, a grown block its new size.
//! Its ratio is held to the same limit. It sees what the instruction count misses: a copy is a
//! few instructions per 32 bytes, so the old `resolve`, which copied a list of `k` overloads into
//! each of `k` uses, took 10.2 times the instructions at 8,000 against 1,000 but 51.8 times the
//! processor time. The count is kept per thread, so tests running beside a run do not change it;
//! a thread the run starts adds its count to the run's when it ends, which [`on_a_thread`] and
//! `deep::on_main_sized_stack` do and a bare `std::thread::spawn` inside the run does not. A test
//! whose bytes grow faster than its order for a reason recorded in COMPLEXITY.md uses
//! [`check_instructions_only`], with a comment naming the item that fixes it.

use std::hint::black_box;
use std::time::Duration;

use perf_event::Builder;
use perf_event::events::{Event, Hardware, Software};
use rustix::time::{ClockId, clock_gettime};

/// How much larger the second run is.
pub const FACTOR: usize = 8;

/// The most times the work of the first the second run may do, for work of order `n`.
pub const RATIO: f64 = 24.0;

/// How many measurements of processor time must all be over the limit before the test fails.
pub const TRIES: usize = 3;

/// The processor time this thread has used, which time spent waiting for a processor does not
/// add to. For a limit on the time of one run that starts no thread; a comparison of two runs
/// uses [`Meter`].
pub fn cpu_time() -> Duration {
    let t = clock_gettime(ClockId::ThreadCPUTime);
    Duration::new(t.tv_sec as u64, t.tv_nsec as u32)
}

/// Counts work in the unit the machine offers.
pub struct Meter {
    counter: perf_event::Counter,
    /// Whether `counter` counts instructions and not the nanoseconds of the task clock.
    instructions: bool,
}

impl Meter {
    /// A meter of instructions where the hardware counts them, or else of the processor time of
    /// this thread and the threads it starts. With no counter at all a test cannot measure the
    /// work, so it stops; see [`no_counter`].
    pub fn new() -> Self {
        Self::open(Hardware::INSTRUCTIONS, true)
            .or_else(|| Self::open(Software::TASK_CLOCK, false))
            .unwrap_or_else(|| no_counter())
    }

    /// A meter of processor time, whatever the hardware offers.
    pub fn of_cpu_time() -> Self {
        Self::open(Software::TASK_CLOCK, false).unwrap_or_else(|| no_counter())
    }

    /// The counter of `event`. Some virtual machines open the instructions counter and leave it
    /// at 0, so a counter that does not move is not used.
    fn open(event: impl Event, instructions: bool) -> Option<Self> {
        let mut builder = Builder::new(event);
        let mut counter = builder.inherit(true).enabled(true).build().ok()?;
        let start = counter.read().expect("reading the counter");
        spin(100_000);
        let moved = counter.read().expect("reading the counter") != start;
        moved.then_some(Self {
            counter,
            instructions,
        })
    }

    /// The work `f` does, in instructions or nanoseconds, and the bytes it allocates on this
    /// thread and the threads that add their count to it; each never 0.
    pub fn work(&mut self, f: impl FnOnce()) -> Work {
        let bytes = zed_alloc_count::allocated();
        let start = self.counter.read().expect("reading the counter");
        f();
        let units = self.counter.read().expect("reading the counter") - start;
        Work {
            units: units.max(1),
            bytes: (zed_alloc_count::allocated() - bytes).max(1),
        }
    }

    /// The name of the unit of [`Work::units`].
    pub fn unit(&self) -> &'static str {
        if self.instructions {
            "instructions"
        } else {
            "ns of processor time"
        }
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
        (0..self.repeats().0)
            .map(|_| self.work(&f))
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
fn no_counter() -> ! {
    panic!(
        "this scaling test cannot measure work: perf_event_open opens neither the instructions \
         counter nor the task clock here. Run it where kernel.perf_event_paranoid is 2 or less \
         and no sandbox refuses that system call"
    )
}

/// `n` passes of a loop that the compiler cannot remove.
fn spin(n: u64) {
    for i in 0..n {
        black_box(i);
    }
}

/// Runs `f` on a thread of its own with a stack of `stack` bytes, and adds the bytes the thread
/// allocates to this thread's count, so a run that measures it counts them.
pub fn on_a_thread<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    let (out, bytes) = std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(stack);
        let counted = || {
            let start = zed_alloc_count::allocated();
            let out = f();
            (out, zed_alloc_count::allocated() - start)
        };
        thread.spawn_scoped(scope, counted).unwrap().join().unwrap()
    });
    zed_alloc_count::add(bytes);
    out
}

/// [`check_order`] for work of order `n` or `n log n`: every pass of the compiler and runtime.
pub fn check(what: &str, n: usize, run: impl Fn(usize)) {
    check_order(what, n, 1, run)
}

/// Runs `run` at sizes `n` and `FACTOR * n` and panics when the larger does more than
/// `RATIO * FACTOR^(power - 1)` times the work, or allocates more than that many times the
/// bytes. `power` is the power of n in the order the work is defined to have: for a Zed program,
/// that of its own algorithm, so an O(n) operation in an O(n) loop has power 2. `what` names the
/// pass and its size.
pub fn check_order(what: &str, n: usize, power: u32, run: impl Fn(usize)) {
    check_by(&mut Meter::new(), Measures::Both, what, n, power, run)
}

/// [`check_order`] without the bytes allocated, for a test whose bytes grow faster than its order
/// for a known cause, recorded in COMPLEXITY.md with the item that fixes it; the call site names
/// that item in a comment.
pub fn check_instructions_only(what: &str, n: usize, power: u32, run: impl Fn(usize)) {
    check_by(&mut Meter::new(), Measures::WorkOnly, what, n, power, run)
}

/// [`check_order`] by the given meter and measures.
fn check_by(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    n: usize,
    power: u32,
    run: impl Fn(usize),
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
/// `limit` times its bytes, for sizes that are not `n` and `8n`. `why` says where the limit comes
/// from.
pub fn compare(what: &str, why: &str, limit: f64, small: impl Fn(), large: impl Fn()) {
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

/// [`compare`] by the given meter and measures. The least of two runs leaves out what the first
/// run builds and the second reuses; counts of instructions need no more than that and one
/// measurement, and processor time needs the fastest of five and three measurements. The bytes
/// do not change with load, so the first measurement over the limit fails.
fn compare_by(
    meter: &mut Meter,
    measures: Measures,
    what: &str,
    why: &str,
    limit: f64,
    small: impl Fn(),
    large: impl Fn(),
) {
    // A first run warms caches.
    small();
    let mut seen = Vec::new();
    for _ in 0..meter.repeats().1 {
        let small = meter.least(&small);
        let large = meter.least(&large);
        let bytes = large.bytes as f64 / small.bytes as f64;
        if measures == Measures::Both && bytes > limit {
            panic!(
                "{what}: allocated {} and {} bytes, {bytes:.1} times the bytes; {why}",
                small.bytes, large.bytes
            );
        }
        let ratio = large.units as f64 / small.units as f64;
        if ratio <= limit {
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
    fn work_of_the_order_given_passes() {
        check("linear work", 1000, |n| work(n, 1, 10));
        check_order("quadratic work", 100, 2, |n| work(n, 2, 2));
    }

    #[test]
    fn work_a_power_of_n_above_the_order_given_fails() {
        assert!(fails(|| check("quadratic work", 100, |n| work(n, 2, 2))));
        assert!(fails(|| check_order("cubic work", 10, 2, |n| work(
            n, 3, 20
        ))));
    }

    #[test]
    fn processor_time_tells_the_orders_apart_too() {
        let mut meter = Meter::of_cpu_time();
        let cpu = &mut meter;
        check_by(cpu, Measures::Both, "linear work", 100_000, 1, |n| {
            work(n, 1, 10)
        });
        assert!(fails(|| check_by(
            cpu,
            Measures::Both,
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
        assert!(fails(|| check(
            "quadratic work on a thread",
            1000,
            quadratic
        )));
        let cpu = &mut Meter::of_cpu_time();
        assert!(fails(|| check_by(
            cpu,
            Measures::Both,
            "quadratic, by time",
            1000,
            1,
            quadratic
        )));
    }

    #[test]
    fn a_comparison_holds_two_sizes_to_the_limit_given() {
        let (small, large) = (|| spin(100_000), || spin(1_600_000));
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
        let (small, large) = (std::cell::Cell::new(0), std::cell::Cell::new(0));
        let mut meter = Meter::new();
        let runs = meter.runs();
        compare_by(
            &mut meter,
            Measures::Both,
            "counted runs",
            "the limit is 24",
            24.0,
            || small.set(small.get() + 1),
            || large.set(large.get() + 1),
        );
        assert_eq!((small.get(), large.get()), runs);
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

    #[test]
    fn bytes_a_power_of_n_above_the_order_given_fail_though_the_work_does_not() {
        let failed = std::panic::catch_unwind(|| check("n² bytes", 1000, square_of_bytes));
        let message = *failed.unwrap_err().downcast::<String>().unwrap();
        assert!(message.contains("64.0 times the bytes"), "{message}");
        check_instructions_only("n² bytes", 1000, 1, square_of_bytes);
    }

    #[test]
    fn the_bytes_of_a_thread_a_run_starts_count_when_it_adds_them() {
        let on_a_thread = |n| on_a_thread(1 << 20, || square_of_bytes(n));
        assert!(fails(|| check("n² bytes on a thread", 1000, on_a_thread)));
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

    #[test]
    fn the_bytes_of_a_run_do_not_depend_on_tests_running_beside_it() {
        let stop = std::sync::atomic::AtomicBool::new(false);
        let mut meter = Meter::new();
        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(|| {
                    while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                        black_box(vec![0u8; 100]);
                    }
                });
            }
            let bytes: Vec<u64> = (0..20)
                .map(|_| meter.work(|| linear_bytes(1000)).bytes)
                .collect();
            stop.store(true, std::sync::atomic::Ordering::Relaxed);
            // 1000 words in lists of 4, 8, ..., 1024 of them.
            assert_eq!(bytes, vec![8 * (2048 - 4); 20]);
        });
    }
}
