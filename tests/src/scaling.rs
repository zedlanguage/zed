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
//! 8.0 times the instructions on every try. Where the hardware counter cannot be opened, as in
//! most virtual machines, [`Meter`] falls back on the processor time of the thread, which needs
//! more runs: each size the fastest of five, three measurements in a row over the limit.

use std::hint::black_box;
use std::time::Duration;

use perf_event::Builder;
use perf_event::events::Hardware;
use rustix::time::{ClockId, clock_gettime};

/// How much larger the second run is.
pub const FACTOR: usize = 8;

/// The most times the work of the first the second run may do, for work of order `n`.
pub const RATIO: f64 = 24.0;

/// How many measurements of processor time must all be over the limit before the test fails.
pub const TRIES: usize = 3;

/// The processor time this thread has used, which time spent waiting for a processor does not
/// add to. For a limit on the time of one run; a comparison of two runs uses [`Meter`].
pub fn cpu_time() -> Duration {
    let t = clock_gettime(ClockId::ThreadCPUTime);
    Duration::new(t.tv_sec as u64, t.tv_nsec as u32)
}

/// Counts work in the unit the machine offers.
pub struct Meter {
    /// The instructions counter, or `None` for the processor time of the thread.
    instructions: Option<perf_event::Counter>,
}

impl Meter {
    /// A meter of instructions where the hardware counts them. Some virtual machines open the
    /// counter and leave it at 0, so a counter that does not move is not used.
    pub fn new() -> Self {
        let mut counter = Builder::new(Hardware::INSTRUCTIONS)
            .inherit(true)
            .enabled(true)
            .build()
            .ok();
        if let Some(c) = &mut counter {
            let start = c.read().expect("reading the instructions counter");
            spin(1000);
            if c.read().expect("reading the instructions counter") == start {
                counter = None;
            }
        }
        Self {
            instructions: counter,
        }
    }

    /// A meter of the processor time of the thread, whatever the hardware offers.
    pub fn of_cpu_time() -> Self {
        Self { instructions: None }
    }

    /// The work `f` does, in instructions or nanoseconds, never 0.
    pub fn work(&mut self, f: impl FnOnce()) -> u64 {
        let start = self.count();
        f();
        (self.count() - start).max(1)
    }

    /// The name of the unit of [`Meter::work`].
    pub fn unit(&self) -> &'static str {
        match self.instructions {
            Some(_) => "instructions",
            None => "ns of processor time",
        }
    }

    fn count(&mut self) -> u64 {
        match &mut self.instructions {
            Some(c) => c.read().expect("reading the instructions counter"),
            None => cpu_time().as_nanos() as u64,
        }
    }

    /// The least work of `runs` runs of `f`.
    fn least(&mut self, runs: usize, f: impl Fn()) -> u64 {
        (0..runs)
            .map(|_| self.work(&f))
            .min()
            .expect("at least one run")
    }
}

impl Default for Meter {
    fn default() -> Self {
        Self::new()
    }
}

/// `n` passes of a loop that the compiler cannot remove.
fn spin(n: u64) {
    for i in 0..n {
        black_box(i);
    }
}

/// [`check_order`] for work of order `n` or `n log n`: every pass of the compiler and runtime.
pub fn check(what: &str, n: usize, run: impl Fn(usize)) {
    check_order(what, n, 1, run)
}

/// Runs `run` at sizes `n` and `FACTOR * n` and panics when the larger does more than
/// `RATIO * FACTOR^(power - 1)` times the work. `power` is the power of n in the order the work
/// is defined to have: for a Zed program, that of its own algorithm, so an O(n) operation in an
/// O(n) loop has power 2. `what` names the pass and its size.
pub fn check_order(what: &str, n: usize, power: u32, run: impl Fn(usize)) {
    check_by(&mut Meter::new(), what, n, power, run)
}

/// [`check_order`] by the given meter. The least of two runs leaves out what the first run
/// builds and the second reuses; counts of instructions need no more than that and one
/// measurement, and processor time needs the fastest of five and three measurements.
fn check_by(meter: &mut Meter, what: &str, n: usize, power: u32, run: impl Fn(usize)) {
    let (runs, measurements) = match meter.instructions {
        Some(_) => (2, 1),
        None => (5, TRIES),
    };
    let limit = RATIO * (FACTOR as f64).powi(power as i32 - 1);
    // A first run warms caches.
    run(n);
    let mut seen = Vec::new();
    for _ in 0..measurements {
        let small = meter.least(runs, || run(n));
        let large = meter.least(runs, || run(FACTOR * n));
        let ratio = large as f64 / small as f64;
        if ratio <= limit {
            return;
        }
        seen.push(format!("{small} and {large}, {ratio:.1} times the work"));
    }
    panic!(
        "{what}: sizes {n} and {} took {} {}; for work of order n^{power} the rule of low \
         complexity allows at most {limit} times (DESIGN.md Part G)",
        FACTOR * n,
        meter.unit(),
        seen.join("; then ")
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
        check_by(cpu, "linear work", 100_000, 1, |n| work(n, 1, 10));
        assert!(fails(|| check_by(cpu, "quadratic work", 1000, 1, |n| {
            work(n, 2, 2)
        })));
    }

    /// `run` on a thread of its own, as a test on a stack of its own does.
    fn on_a_thread(f: impl FnOnce() + Send) {
        std::thread::scope(|s| s.spawn(f).join().unwrap());
    }

    #[test]
    fn the_work_of_a_thread_a_run_starts_counts() {
        assert!(fails(|| check("quadratic work on a thread", 100, |n| {
            on_a_thread(|| work(n, 2, 2));
        })));
    }

    #[test]
    fn a_meter_counts_the_work_of_a_run_and_not_the_time_it_sleeps() {
        let mut meter = Meter::new();
        let spun = meter.work(|| spin(10_000_000));
        let slept = meter.work(|| std::thread::sleep(Duration::from_millis(20)));
        assert!(spun > slept, "spun {spun}, slept {slept}");
    }
}
