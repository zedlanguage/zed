//! The scaling test of the rule of low complexity (DESIGN.md Part G, "Six standing rules"): a
//! pass runs at sizes n and 8n, and the larger run may take at most `24 × 8^(k−1)` times as
//! long, where `n^k` is the order the measured work is defined to have. A run of order `n^k`
//! or `n^k log n` stays near `8^k` to `1.4 × 8^k` times, and one a power of n above it near
//! `8^(k+1)`. The test fails only when three measurements in a row are over the limit.

use std::time::{Duration, Instant};

/// How much larger the second run is.
pub const FACTOR: usize = 8;

/// The most times as long as the first the second run may take, for work of order `n`.
pub const RATIO: f64 = 24.0;

/// How many measurements must all be over the limit before the test fails.
pub const TRIES: usize = 3;

/// [`check_order`] for work of order `n` or `n log n`: every pass of the compiler and runtime.
pub fn check(what: &str, n: usize, run: impl Fn(usize)) {
    check_order(what, n, 1, run)
}

/// Runs `run` at sizes `n` and `FACTOR * n`, each the fastest of five runs, and panics when
/// the larger takes more than `RATIO * FACTOR^(power - 1)` times as long in each of [`TRIES`]
/// measurements. `power` is the power of n in the order the work is defined to have: for a
/// Zed program, that of its own algorithm, so an O(n) operation in an O(n) loop has power 2.
/// `what` names the pass and its size.
pub fn check_order(what: &str, n: usize, power: u32, run: impl Fn(usize)) {
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
    let limit = RATIO * (FACTOR as f64).powi(power as i32 - 1);
    // A first run warms caches and the evaluation thread.
    run(n);
    let mut seen = Vec::new();
    for _ in 0..TRIES {
        let small = time(n).max(Duration::from_micros(1));
        let large = time(FACTOR * n);
        let ratio = large.as_secs_f64() / small.as_secs_f64();
        if ratio <= limit {
            return;
        }
        seen.push(format!("{small:?} and {large:?}, {ratio:.1} times as long"));
    }
    panic!(
        "{what}: sizes {n} and {} took {}; for work of order n^{power} the rule of low \
         complexity allows at most {limit} times (DESIGN.md Part G)",
        FACTOR * n,
        seen.join("; then ")
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hint::black_box;

    /// `n^power` additions.
    fn work(n: usize, power: u32) {
        let mut sum = 0u64;
        for i in 0..n.pow(power) {
            sum = black_box(sum.wrapping_add(i as u64));
        }
        black_box(sum);
    }

    fn fails(run: impl FnOnce()) -> bool {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)).is_err()
    }

    #[test]
    fn work_of_the_order_given_passes() {
        check("linear work", 200_000, |n| work(n, 1));
        check_order("quadratic work", 400, 2, |n| work(n, 2));
    }

    #[test]
    fn work_a_power_of_n_above_the_order_given_fails() {
        assert!(fails(|| check("quadratic work", 400, |n| work(n, 2))));
        assert!(fails(|| check_order("cubic work", 40, 2, |n| work(n, 3))));
    }
}
