//! The scaling test of the rule of low complexity (DESIGN.md Part G, "Six standing rules"): a
//! pass runs at sizes n and 8n, and the larger run may take at most 24 times as long. A linear
//! or n log n pass stays near 8 to 11 times, and a quadratic one is near 64.

use std::time::{Duration, Instant};

/// How much larger the second run is.
pub const FACTOR: usize = 8;

/// The most times as long as the first the second run may take.
pub const RATIO: f64 = 24.0;

/// Runs `run` at sizes `n` and `FACTOR * n`, each the fastest of five runs, and panics when
/// the larger takes more than [`RATIO`] times as long. `what` names the pass and its size.
pub fn check(what: &str, n: usize, run: impl Fn(usize)) {
    let time = |m: usize| {
        (0..5)
            .map(|_| {
                let start = Instant::now();
                run(m);
                start.elapsed()
            })
            .min()
            .expect("five runs")
    };
    // A first run warms caches and the evaluation thread.
    run(n);
    let small = time(n).max(Duration::from_micros(1));
    let large = time(FACTOR * n);
    let ratio = large.as_secs_f64() / small.as_secs_f64();
    assert!(
        ratio <= RATIO,
        "{what}: size {n} takes {small:?} and size {} takes {large:?}, {ratio:.1} times as \
         long; the rule of low complexity allows at most {RATIO} times (DESIGN.md Part G)",
        FACTOR * n
    );
}
