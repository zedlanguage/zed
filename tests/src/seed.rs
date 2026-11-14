//! The seed of a random test (TEST-bench-move-crates, author P169). Each run draws a new seed,
//! so a run covers cases the runs before it did not, and prints it on every run: setting
//! `ZED_TEST_SEED` to the printed number repeats that run.
//!
//! The line goes straight to the process's standard error, past the test harness's capture, so
//! it is in the log of a run that passes as well as of one that fails, where it comes before
//! the failure's message.

use std::io::Write;

/// The variable that fixes the seed: [`seed`] returns its value when it is set.
pub const SEED_VAR: &str = "ZED_TEST_SEED";

/// The seed of the random test `test`: the value of `ZED_TEST_SEED` when it is set, else a new
/// one from the clock and the process id. Prints `<test>: seed <seed>; ZED_TEST_SEED=<seed>
/// repeats this run` to standard error.
///
/// # Panics
///
/// If `ZED_TEST_SEED` is set to anything but a decimal `u64`.
pub fn seed(test: &str) -> u64 {
    let seed = match std::env::var(SEED_VAR) {
        Ok(s) => s
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("{SEED_VAR}={s} is not a decimal u64")),
        Err(_) => {
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos() as u64);
            mix(nanos ^ u64::from(std::process::id()) << 40)
        }
    };
    let line = format!("{test}: seed {seed}; {SEED_VAR}={seed} repeats this run\n");
    // One write of the whole line, so lines of tests running at once do not mix. A failed write
    // to standard error leaves nothing to report it to.
    let _ = std::io::stderr().write_all(line.as_bytes());
    seed
}

/// The SplitMix64 finalizer: spreads the clock's low bits, which change fastest, over all 64.
pub(crate) fn mix(x: u64) -> u64 {
    let x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}
