//! The seed of a random test (TEST-bench-move-crates, author P169). Each run draws a new seed,
//! so a run covers cases the runs before it did not, and prints it on every run: setting
//! `ZED_TEST_SEED` to the printed number repeats that run.
//!
//! The line goes straight to the process's standard error, past the test harness's capture, so
//! it is in the log of a run that passes as well as of one that fails, where it comes before
//! the failure's message.
//!
//! The generators themselves are zed-hash's (DRY-hash-crate-2026-11-26), where their sources,
//! proofs and tests are: [`Rng`] is its `SplitMix64` with a seed from [`seed`], and
//! `zed_hash::Xorshift64` is the xorshift64 the tests with recorded seeds draw from.

use std::io::Write;
use std::ops::{Deref, DerefMut};

use zed_hash::{SplitMix64, mix};

/// The variable that fixes the seed: [`seed`] returns its value when it is set.
pub const SEED_VAR: &str = "ZED_TEST_SEED";

/// The seed of the random test `test`: the value of `ZED_TEST_SEED` when it is set, else a new
/// one from the clock and the process id, spread over 64 bits by splitmix64's `mix` (the clock's
/// low bits change fastest). Prints `<test>: seed <seed>; ZED_TEST_SEED=<seed> repeats this run`
/// to standard error.
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

/// The generator of every random test (DRY-test-helpers): zed-hash's `SplitMix64` (why that
/// generator: its comment), from a seed of [`seed`] ([`Rng::fresh`]) or a fixed one
/// ([`Rng::new`]). Its draws are `SplitMix64`'s, reached through `Deref`.
///
/// This was `instances::Rng`, which re-exports it; its streams are unchanged by both moves.
pub struct Rng(SplitMix64);

impl Rng {
    /// A generator from `seed`; every seed is good, 0 too.
    pub fn new(seed: u64) -> Self {
        Rng(SplitMix64::new(seed))
    }

    /// A generator with a new seed on each run, for a random test (author P169: random tests
    /// run fewer cases, with a new seed each run, printed): the seed of [`seed`], printed with
    /// `what` on standard error, which `ZED_TEST_SEED=<seed>` repeats. The seed is also
    /// returned, for the test's failure messages.
    pub fn fresh(what: &str) -> (Self, u64) {
        let seed = seed(what);
        (Rng::new(seed), seed)
    }
}

impl Deref for Rng {
    type Target = SplitMix64;

    fn deref(&self) -> &SplitMix64 {
        &self.0
    }
}

impl DerefMut for Rng {
    fn deref_mut(&mut self) -> &mut SplitMix64 {
        &mut self.0
    }
}
