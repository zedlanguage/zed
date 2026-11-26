//! Hash steps and seeded generators of fixed definition, shared by every crate of the workspace
//! (DRY-hash-crate-2026-11-26; docs/layout.md, "Library DAG"): the splitmix64 finalizer and
//! generator, the step that folds a word into a digest, FNV-1a over bytes, Marsaglia's xorshift64
//! and Knuth's MMIX linear congruential generator.
//!
//! Every function here is fixed by its definition, the same on every run and machine: tests pin
//! their outputs (hashes of signatures, seeds a sweep found, benchmark inputs), and a change of
//! a constant, a shift or the order of steps changes those pins. The unit tests check each
//! against values computed apart from this crate.
//!
//! The crate depends on nothing, so the lowest libraries (zed-numtheory, zed-graph) and a build
//! script (zed-native's) can use it.

#[cfg(test)]
mod tests;

/// The increment of splitmix64's state: "the odd integer closest to 2^64/φ" (Steele, Lea and
/// Flood 2014, sec. 3, p. 464, `GOLDEN_GAMMA` in Figure 16, p. 465; full citation at
/// [`finalize`]). "To ensure that every instance has period 2^64, it is necessary to require that
/// the gamma value always be odd" (same page): an odd step generates the group of residues
/// modulo 2^64, so the states `x + k·γ` visit all 2^64 values before one repeats.
pub const GAMMA: u64 = 0x9e37_79b9_7f4a_7c15;

/// splitmix64's finalizer of `z`: shifts 30, 27 and 31 with the multipliers
/// `0xbf58476d1ce4e5b9` and `0x94d049bb133111eb`, a bijection of `u64`.
///
/// Sources. G. L. Steele Jr., D. Lea and C. H. Flood, "Fast splittable pseudorandom number
/// generators", OOPSLA 2014, ACM, pp. 453-472, doi:10.1145/2660193.2660195 (read 2026-11-21 in
/// the publisher's PDF; Crossref checked 2026-11-20). This finalizer is the paper's
/// `mix64variant13`, "David Stafford's Mix13 variant of the MurmurHash3 finalizer" (p. 464).
/// S. Vigna, `splitmix64.c` (2015, public domain, <https://prng.di.unimi.it/splitmix64.c>,
/// checked 2026-11-20), "a fixed-increment version of Java 8's SplittableRandom generator", whose
/// `next` is this finalizer of the state after adding [`GAMMA`]; the constants here equal his.
///
/// Departure from the paper: its Figure 16 `nextLong` applies `mix64`, the MurmurHash3
/// finalizer (three shifts of 33, multipliers `0xff51afd7ed558ccd` and `0xc4ceb9fe1a85ec53`),
/// and uses `mix64variant13` only to make new gammas; the JDK's `SplittableRandom`, Vigna's
/// code and this one apply Mix13 to the output. The paper's BigCrush runs (Table 1, p. 468) test
/// the Figure 16 generator, whose output is `mix64`, so no published BigCrush run covers this
/// exact output function.
///
/// Proof that it is a bijection: each of its five steps is invertible on `u64`. `z ^ (z >> s)`
/// for `s >= 1` is invertible because the top `s` bits of the result are those of `z`, and each
/// lower block of `s` bits is the result's xored with the block above it, already recovered.
/// Multiplication by an odd constant is invertible modulo 2^64 because an odd number is a unit
/// of the ring (its inverse exists by Euclid, gcd(c, 2^64) = 1). A composition of bijections is
/// one. ("xorshifts and multiplications by odd constants are invertible", Vigna.) The tests
/// `the_step_is_one_to_one_in_each_argument_and_depends_on_order` (on many words) and
/// [`unstep`] rely on it.
#[inline]
pub fn finalize(z: u64) -> u64 {
    let z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The first output of splitmix64 from the state `x`: [`finalize`] of `x + GAMMA`. It spreads
/// the low bits of `x`, which change fastest in a counter or a clock, over all 64.
///
/// On JDK 26 `new SplittableRandom(0).nextLong()` printed `e220a8397b1dcdaf` and
/// `new SplittableRandom(1).nextLong()` printed `910a2dec89025cc1` (2026-11-20), which are
/// `mix(0)` and `mix(1)`; `the_mix_is_splitmix64` checks both, so it catches a changed constant,
/// shift or order of steps. Equal to `step(0, x)`.
#[inline]
pub fn mix(x: u64) -> u64 {
    finalize(x.wrapping_add(GAMMA))
}

/// The digest `h` with the word `x` added: [`mix`] of `h` rotated left by 29, xored with `x`.
/// It is the step of zed-kernel's `digest::Digest`, the combination of two digests that `value`
/// and `types` build theirs with, and the step of `zedc_preimage::address`'s digest of terms.
///
/// Each argument enters through a bijection (a rotation, an xor with the other argument), and
/// [`mix`] is one (proof at [`finalize`]), so for a fixed `h` the step is one to one in `x`, and
/// for a fixed `x` one to one in `h`. The rotation of `h` makes the step depend on the order of
/// the words: `step(step(0, a), b)` and `step(step(0, b), a)` differ in general, where without it
/// `h ^ x` would be symmetric in the first step. [`unstep`] inverts it in `x`, and zed-kernel's
/// `bdd::set::tests` through it in `h` too.
#[inline]
pub fn step(h: u64, x: u64) -> u64 {
    mix(h.rotate_left(29) ^ x)
}

/// The word `x` whose [`step`]`(h, x)` is `z`, for tests that build inputs of a chosen digest
/// (zed-kernel's `bdd::set::tests` and `treap_set::bench`, which held a copy each).
///
/// Each step of [`finalize`] is undone in reverse order (the proof that each is invertible is
/// there). `y = z ^ (z >> s)` is undone by `z = y ^ (y >> s) ^ (y >> 2s) ^ ...` over every
/// multiple of `s` up to 64: the term `y >> ks` is `(z >> ks) ^ (z >> (k+1)s)`, so the xor of
/// the terms for `k = 0..=K` telescopes to `z ^ (z >> (K+1)s)`, and `(K+1)s > 64` at
/// `K = 64 / s` makes the shifted part 0. A multiplication by an odd
/// `c` is undone by `c`'s inverse modulo 2^64, found by Newton's iteration `y -> y(2 - cy)`
/// from `y = c`, which is correct to 3 bits (`c·c ≡ 1 (mod 8)` for odd `c`) and doubles the
/// correct low bits at each step: if `cy = 1 + e·2^k` then `c·y(2 - cy) = 1 - e²·2^2k`. Five
/// steps give 96 >= 64 bits. Then [`GAMMA`] is subtracted and `h` rotated left by 29 xored off.
/// The tests check `step(h, unstep(h, z)) == z` and the reverse on random words.
pub fn unstep(h: u64, z: u64) -> u64 {
    let unshift = |y: u64, s: u32| (1..=64 / s).fold(y, |acc, k| acc ^ (y >> (s * k)));
    let inverse = |c: u64| {
        (0..5).fold(c, |y: u64, _| {
            y.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(y)))
        })
    };
    let z = unshift(z, 31).wrapping_mul(inverse(0x94d0_49bb_1331_11eb));
    let z = unshift(z, 27).wrapping_mul(inverse(0xbf58_476d_1ce4_e5b9));
    unshift(z, 30).wrapping_sub(GAMMA) ^ h.rotate_left(29)
}

/// The splitmix64 generator: the state steps by [`GAMMA`] and each output is [`finalize`] of the
/// new state (Vigna's `splitmix64.c`; Steele, Lea and Flood 2014, cited at [`finalize`]). The
/// generator of every random test, through zed-testkit's `seed::Rng`, and of the Chaotic
/// schedule of zed-kernel's evaluator.
///
/// Why this generator for tests. Its state is one `u64` that steps by an odd constant, so every
/// seed, 0 included, starts a sequence of period 2^64. The xorshift64 generators it replaced had
/// 0 as a fixed point: seeded with `ZED_TEST_SEED=0` without `| 1`, every draw was 0 and a test
/// ran one degenerate case 4,000 times (`seed_zero_gives_varied_draws`). xorshift64's bits also
/// fail BigCrush's linear-complexity tests, and the 64-bit LCGs' low bits have short periods
/// (bit k repeats every 2^(k+1) steps), which their `>> 33` hid at the cost of half the bits. A
/// generator with more state (xoshiro256**, PCG64) passes the same tests and buys nothing a test
/// needs at these draw counts.
///
/// The draws take and give fixed types (`usize` and `u64` counts, `i64` and `i128` integers),
/// not any integer type: a method generic over the type left the type of `rng.int(0, 5) + x` to
/// the literal's fallback, `i32`, and broke the callers' type inference.
#[derive(Clone, Debug)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    /// A generator from `seed`; every seed is good, 0 too.
    #[inline]
    pub fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    /// The next 64 random bits: [`mix`] of the state, which then steps by [`GAMMA`].
    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        let x = self.0;
        self.0 = x.wrapping_add(GAMMA);
        mix(x)
    }

    /// A number in `0..n`: the next 64 bits mod `n`.
    ///
    /// Why `% n` and not a method free of bias, such as Lemire's (D. Lemire, "Fast random integer
    /// generation in an interval", ACM TOMACS 29(1), 2019, article 3, pp. 1-12,
    /// doi:10.1145/3230636; Crossref, 2026-11-20; named as the road not taken, nothing of it is
    /// used). The remainder makes the first `2^64 mod n` results more likely by one part in
    /// `⌊2^64 / n⌋`, which for any `n` below 2^32 is under 2^-32: no test draws enough to see it.
    /// And tests pin cases found by sweeps to this mapping's draws (`gen_cells(&mut
    /// Rng::new(1140))` in l01_23, the Chaotic schedule's shuffles); another mapping from bits to
    /// numbers would draw other cases from the same seeds and lose them.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    #[inline]
    pub fn below(&mut self, n: usize) -> usize {
        self.below_u64(n as u64) as usize
    }

    /// [`SplitMix64::below`] on `u64`.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    #[inline]
    pub fn below_u64(&mut self, n: u64) -> u64 {
        assert!(n > 0, "SplitMix64::below(0): an empty range");
        self.next_u64() % n
    }

    /// A number in `lo..=hi`, every one equally likely (up to the bias of [`SplitMix64::below`]).
    ///
    /// # Panics
    ///
    /// If `hi < lo`.
    pub fn int(&mut self, lo: i64, hi: i64) -> i64 {
        self.int_i128(lo.into(), hi.into()) as i64
    }

    /// [`SplitMix64::int`] on `i128`.
    ///
    /// # Panics
    ///
    /// If `hi < lo`, or the range holds more than 2^64 numbers.
    pub fn int_i128(&mut self, lo: i128, hi: i128) -> i128 {
        assert!(lo <= hi, "SplitMix64::int({lo}, {hi}): an empty range");
        // `hi - lo + 1` overflows only for ranges far above 2^64, which the panic below names.
        let span = hi.checked_sub(lo).and_then(|d| d.checked_add(1));
        match span {
            Some(s) if s == 1 << 64 => lo + i128::from(self.next_u64()),
            Some(s) if s < 1 << 64 => lo + i128::from(self.below_u64(s as u64)),
            _ => panic!("SplitMix64::int({lo}, {hi}): more than 2^64 numbers"),
        }
    }

    /// True one time in two: the top bit of the next output.
    #[inline]
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
    /// algorithm P: for `i` from the last index down to 1, swap `xs[i]` with `xs[below(i + 1)]`,
    /// n − 1 swaps). The order of draws is part of the pinned streams (the Chaotic schedule).
    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            xs.swap(i, self.below(i + 1));
        }
    }
}

/// Marsaglia's xorshift64 with the shifts 13, 7, 17 (G. Marsaglia, "Xorshift RNGs", J. Stat.
/// Softw. 8(14), 2003, doi:10.18637/jss.v008.i14): (13, 7, 17) is one of the 275 triples the
/// paper lists as giving "64×64 matrices T = (I + L^a)(I + R^b)(I + L^c) whose order is
/// 2^64 − 1", and its example `xor64` is `x^=(x<<13); x^=(x>>7); return (x^=(x<<17));`, the step
/// below. Checked 2026-11-20: Crossref, and the paper's text (the journal's PDF) read for the
/// list and the example. `seed_zero_gives_varied_draws` checks the first step from 1 by hand; no
/// test checks the period, which rests on the paper.
///
/// For the tests whose cases are pinned to its stream: a seed a sweep found a failure at, a
/// benchmark's input, a chain whose cliff the test names (`Gen` in zedc-preimage,
/// `chains_are_read_exactly_on_both_sides_of_the_cliff`), and the choice of `a` in
/// zed-numtheory's SIQS. A new test uses [`SplitMix64`].
///
/// The seed 0 is replaced by `mix(0)`: 0 is xorshift's fixed point, and copies seeded from a
/// clock seed without `| 1` drew 0 forever under `ZED_TEST_SEED=0`. Any other seed gives the
/// plain stream, so the pinned seeds, none of them 0, draw the cases they were pinned to. The
/// value `mix(0)` is only some nonzero state; the period from any nonzero state is 2^64 − 1.
#[derive(Clone, Debug)]
pub struct Xorshift64(u64);

impl Xorshift64 {
    /// A generator from `seed`, 0 replaced by `mix(0)`.
    #[inline]
    pub fn new(seed: u64) -> Self {
        Xorshift64(if seed == 0 { mix(0) } else { seed })
    }

    /// The next state, which is also the output.
    #[inline]
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
    #[inline]
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// The 64-bit linear congruential generator with Knuth's MMIX constants: the state `s` becomes
/// `6364136223846793005·s + 1442695040888963407 mod 2^64`, the multiplier and increment known as
/// Knuth's MMIX pair (D. E. Knuth, The Art of Computer Programming, vol. 2, 3rd ed., 1997, sec.
/// 3.3.4, lists the multiplier). Not checked against the book here (2026-11-26): the constants
/// are those of the 16 test copies this replaced, which pinned cases to their streams, and
/// `the_lcg_is_the_copies_recurrence` holds them to the copies' own lines.
///
/// The period is 2^64 for any seed, by Hull and Dobell's theorem (Knuth, sec. 3.2.1.2, Theorem
/// A): the increment is odd, so prime to 2^64, and the multiplier minus 1 is a multiple of 4
/// (6364136223846793004 = 4 · 1591034055961698251). Its low bits are weak (bit k has period
/// 2^(k+1)), so [`Lcg64::next_high`] and [`Lcg64::below`] read the top 31 bits, `>> 33`, as every
/// copy did. Kept for the tests pinned to these streams; a new test uses [`SplitMix64`].
#[derive(Clone, Debug)]
pub struct Lcg64(u64);

impl Lcg64 {
    /// The multiplier.
    pub const A: u64 = 6_364_136_223_846_793_005;
    /// The increment.
    pub const C: u64 = 1_442_695_040_888_963_407;

    /// A generator from the state `seed`; the first output is the state after one step.
    #[inline]
    pub fn new(seed: u64) -> Self {
        Lcg64(seed)
    }

    /// The state now, the last output of [`Lcg64::next_u64`] (or the seed): `Lcg64::new` of it
    /// goes on with the same stream, so a test can pin where a long run stands and resume there.
    #[inline]
    pub fn state(&self) -> u64 {
        self.0
    }

    /// The next state, all 64 bits (its low bits weak, above).
    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(Self::A).wrapping_add(Self::C);
        self.0
    }

    /// The top 31 bits of the next state, `>> 33`.
    #[inline]
    pub fn next_high(&mut self) -> u64 {
        self.next_u64() >> 33
    }

    /// [`Lcg64::next_high`] mod `n`.
    ///
    /// # Panics
    ///
    /// If `n` is 0.
    #[inline]
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_high() % n
    }
}

/// The 64-bit FNV offset basis, `0xCBF29CE484222325`.
pub const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// The 64-bit FNV prime, 2^40 + 2^8 + 0xB3.
pub const FNV_PRIME: u64 = 0x0100_0000_01b3;

/// The 64-bit FNV-1a hash of `bytes`: [`fnv1a_64_from`] the offset basis. O(n) for n bytes.
///
/// Source: G. Fowler, L. Noll, K.-P. Vo, D. Eastlake and T. Hansen, "The FNV Non-Cryptographic
/// Hash Algorithm", Internet-Draft draft-eastlake-fnv-35, June 2025,
/// <https://datatracker.ietf.org/doc/draft-eastlake-fnv/>. Section 2 gives FNV-1a as
/// "hash = offset_basis; for each octet_of_data to be hashed: hash = hash xor octet_of_data;
/// hash = hash * FNV_Prime mod 2**HashSize". Section 5 gives the 64-bit FNV_Prime as
/// 2**40 + 2**8 + 0xB3 = 0x00000100_000001B3 and the 64-bit offset_basis as 0xCBF29CE4_84222325.
/// The code follows it with no departure: `wrapping_mul` is the product mod 2^64.
///
/// Checked 2026-11-20: the constants against section 5 of the draft and the expected outputs
/// against `FNV64svalues` in its section 8.3 test code. Test: `the_drafts_test_vectors`, which
/// catches a wrong constant or the FNV-1 order (multiply before xor).
#[inline]
pub fn fnv1a_64(bytes: &[u8]) -> u64 {
    fnv1a_64_from(FNV_OFFSET, bytes)
}

/// FNV-1a over `bytes`, after the bytes whose hash is `h`: `fnv1a_64(a ++ b)` is
/// `fnv1a_64_from(fnv1a_64(a), b)`, so a text hashes alike in any blocks. The step is defined one
/// byte at a time from the running hash, so this is the definition's loop resumed.
#[inline]
pub fn fnv1a_64_from(h: u64, bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .fold(h, |h, &b| (h ^ u64::from(b)).wrapping_mul(FNV_PRIME))
}

/// A [`std::hash::Hasher`] by FNV-1a ([`fnv1a_64`]): `write` takes the bytes as given, and the
/// other `write_*` methods are the standard library's defaults, which write a number's
/// native-endian bytes, so the hash of a value is FNV-1a of the bytes its `Hash` writes on this
/// machine. `finish` gives the FNV-1a hash itself, unmixed. Its low bits are weak: xor and
/// multiplication modulo 2^64 agree with the same operations modulo 2^k on the low `k` bits, so
/// the low `k` bits of the hash depend only on the low `k` bits of each byte. A caller that
/// reduces the hash or keeps few of its bits applies [`mix`] first, as zedc-types' signature
/// hash does.
#[derive(Clone, Debug)]
pub struct Fnv1a(u64);

impl Default for Fnv1a {
    /// The hasher of no bytes: the offset basis.
    #[inline]
    fn default() -> Self {
        Fnv1a(FNV_OFFSET)
    }
}

impl std::hash::Hasher for Fnv1a {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.0 = fnv1a_64_from(self.0, bytes);
    }
}
