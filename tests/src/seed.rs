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

/// One step of SplitMix64 from the state `x`: the state's increment, then the finalizer, which
/// spreads the clock's low bits, which change fastest, over all 64.
///
/// The constants are those of G. L. Steele, D. Lea and C. H. Flood, "Fast splittable
/// pseudorandom number generators", OOPSLA 2014, pp. 453-472, doi:10.1145/2660193.2660195
/// (`mix64variant13` of Stafford's list): `0x9e37_79b9_7f4a_7c15` is 2^64 divided by the
/// golden ratio, made odd, so the states `x + k·γ` visit all 2^64 values before one repeats;
/// the two multipliers and the shifts 30, 27 and 31 are the finalizer that passes BigCrush on
/// that sequence. [`Rng::next_u64`] and the clock seed of [`seed`] rely on them.
///
/// Checked 2026-11-20: Crossref gave the citation above; the paper's text was not read (no free
/// copy found), so the sketch is from memory. The paper describes the JDK's `SplittableRandom`,
/// and on JDK 26 `new SplittableRandom(0).nextLong()` printed `e220a8397b1dcdaf` and
/// `new SplittableRandom(1).nextLong()` printed `910a2dec89025cc1`, which are `mix(0)` and
/// `mix(1)` here. `the_mix_is_splitmix64` checks both values, so it catches a changed constant,
/// shift or order of steps; it cannot tell whether the generator is a good one, which rests on
/// the paper's BigCrush runs.
///
/// A copy of zed-kernel's `digest::step(0, x)`, kept on purpose: this file is compiled by
/// `#[path]` into the unit tests of zed-graph and zedc-solvers, which do not depend on
/// zed-kernel, and a dependency added for six lines would put the kernel in their build.
pub(crate) fn mix(x: u64) -> u64 {
    let x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// The generator of every random test (DRY-test-helpers): SplitMix64, from a seed of [`seed`]
/// ([`Rng::fresh`]) or a fixed one ([`Rng::new`]).
///
/// Why SplitMix64. Its state is one `u64` that steps by an odd constant, so every seed,
/// 0 included, starts a sequence of period 2^64, and its output passes BigCrush (Steele, Lea and
/// Flood 2014). The xorshift64 generators it replaced had 0 as a fixed point: seeded with
/// `ZED_TEST_SEED=0` without `| 1`, every draw was 0 and a test ran one degenerate case 4,000
/// times (`seed_zero_gives_varied_draws`). xorshift64's bits also fail BigCrush's
/// linear-complexity tests, and the 64-bit LCGs' low bits have short periods (bit k repeats
/// every 2^(k+1) steps), which their `>> 33` hid at the cost of half the bits. A generator with
/// more state (xoshiro256**, PCG64) passes the same tests and buys nothing a test needs at
/// these draw counts.
///
/// This was `instances::Rng`, which re-exports it; its streams are unchanged by the move.
///
/// The draws take and give fixed types (`usize` and `u64` counts, `i64` and `i128` integers),
/// not any integer type: a method generic over the type left the type of `rng.int(0, 5) + x`
/// to the literal's fallback, `i32`, and broke the callers' type inference.
pub struct Rng(u64);

impl Rng {
    /// A generator from `seed`; every seed is good, 0 too.
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    /// A generator with a new seed on each run, for a random test (author P169: random tests
    /// run fewer cases, with a new seed each run, printed): the seed of [`seed`], printed with
    /// `what` on standard error, which `ZED_TEST_SEED=<seed>` repeats. The seed is also
    /// returned, for the test's failure messages.
    pub fn fresh(what: &str) -> (Self, u64) {
        let seed = seed(what);
        (Rng::new(seed), seed)
    }

    /// The next 64 random bits.
    pub fn next_u64(&mut self) -> u64 {
        let x = self.0;
        self.0 = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        mix(x)
    }

    /// A number in `0..n`: the next 64 bits mod `n`.
    ///
    /// Why `% n` and not a method free of bias, such as Lemire's (D. Lemire, "Fast random
    /// integer generation in an interval", ACM TOMACS 29(1), 2019, article 3, pp. 1-12,
    /// doi:10.1145/3230636; Crossref, 2026-11-20; named as the road not taken, nothing of it is
    /// used). The remainder makes the first `2^64 mod n` results more likely by one part in
    /// `⌊2^64 / n⌋`, which for any `n` below 2^32 is under 2^-32: no test draws enough to see
    /// it. And this generator was `instances::Rng` before it moved here, whose `below` was
    /// `% n`: tests pin cases found by sweeps to its seeds (`gen_cells(&mut Rng::new(1140))`
    /// in l01_23), and another mapping from bits to numbers would draw other cases from the
    /// same seeds and lose them.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    pub fn below(&mut self, n: usize) -> usize {
        self.below_u64(n as u64) as usize
    }

    /// [`Rng::below`] on `u64`.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    pub fn below_u64(&mut self, n: u64) -> u64 {
        assert!(n > 0, "Rng::below(0): an empty range");
        self.next_u64() % n
    }

    /// A number in `lo..=hi`, every one equally likely.
    ///
    /// # Panics
    ///
    /// If `hi < lo`.
    pub fn int(&mut self, lo: i64, hi: i64) -> i64 {
        self.int_i128(lo.into(), hi.into()) as i64
    }

    /// [`Rng::int`] on `i128`.
    ///
    /// # Panics
    ///
    /// If `hi < lo`, or the range holds more than 2^64 numbers.
    pub fn int_i128(&mut self, lo: i128, hi: i128) -> i128 {
        assert!(lo <= hi, "Rng::int({lo}, {hi}): an empty range");
        // `hi - lo + 1` overflows only for ranges far above 2^64, which the panic below names.
        let span = hi.checked_sub(lo).and_then(|d| d.checked_add(1));
        match span {
            Some(s) if s == 1 << 64 => lo + i128::from(self.next_u64()),
            Some(s) if s < 1 << 64 => lo + i128::from(self.below_u64(s as u64)),
            _ => panic!("Rng::int({lo}, {hi}): more than 2^64 numbers"),
        }
    }

    /// True one time in two.
    pub fn coin(&mut self) -> bool {
        self.next_u64() >> 63 == 1
    }

    /// One element of `xs`.
    ///
    /// # Panics
    ///
    /// If `xs` is empty.
    pub fn pick<T: Clone>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len())].clone()
    }

    /// A sequence of at most `max_len` elements of `alphabet`, its length uniform.
    pub fn seq<T: Clone>(&mut self, alphabet: &[T], max_len: usize) -> Vec<T> {
        let n = self.below(max_len + 1);
        (0..n).map(|_| self.pick(alphabet)).collect()
    }

    /// `xs` in a random order, every order equally likely (Fisher and Yates, as Durstenfeld's
    /// algorithm P: n − 1 swaps).
    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            xs.swap(i, self.below(i + 1));
        }
    }
}

/// Marsaglia's xorshift64 with the shifts 13, 7, 17 (G. Marsaglia, "Xorshift RNGs", J. Stat.
/// Softw. 8(14), 2003, doi:10.18637/jss.v008.i14): (13, 7, 17) is one of the 275 triples the
/// paper lists as giving "64×64 matrices T = (I + L^a)(I + R^b)(I + L^c) whose order is
/// 2^64 − 1", and its example `xor64` is `x^=(x<<13); x^=(x>>7); return (x^=(x<<17));`, the
/// step below. Checked 2026-11-20: Crossref, and the paper's text (the journal's PDF) read for
/// the list and the example. `seed_zero_gives_varied_draws` checks the first step from 1 by
/// hand; no test checks the period, which rests on the paper.
///
/// For the tests whose cases are pinned to its stream: a seed a sweep found a failure at, a
/// benchmark's input, a chain whose cliff the test names (`Gen` in zedc-preimage,
/// `chains_are_read_exactly_on_both_sides_of_the_cliff`). Each of those tests kept a private
/// copy of these lines (DRY-test-helpers); a new test uses [`Rng`].
///
/// The seed 0 is replaced by `mix(0)`: 0 is xorshift's fixed point, and the copies this
/// replaced, seeded from [`seed`] without `| 1`, drew 0 forever under `ZED_TEST_SEED=0`. Any
/// other seed gives the copies' stream unchanged, so the pinned seeds, none of them 0, draw
/// the cases they were pinned to. The value `mix(0)` is only some nonzero state; the period
/// from any nonzero state is 2^64 − 1.
pub struct Xorshift64(u64);

impl Xorshift64 {
    /// A generator from `seed`, 0 replaced by `mix(0)`.
    pub fn new(seed: u64) -> Self {
        Xorshift64(if seed == 0 { mix(0) } else { seed })
    }

    /// The next state, which is also the output.
    pub fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// The next output mod `n`, as the copies drew.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}
