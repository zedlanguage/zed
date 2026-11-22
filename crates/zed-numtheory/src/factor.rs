//! The prime factors of a 64-bit integer: Miller-Rabin with the bases that decide every
//! 64-bit number, and Pollard's rho in Brent's form to split a composite, with Lehman's method
//! when that run ends without a factor; below 2^44 the cost per number has a proved bound
//! (comment at [`factor`]).
//!
//! Sources: G. L. Miller, "Riemann's hypothesis and tests for primality", J. Comput. Syst. Sci.
//! 13(3):300-317, 1976, doi:10.1016/S0022-0000(76)80043-8, and M. O. Rabin, "Probabilistic
//! algorithm for testing primality", J. Number Theory 12(1):128-138, 1980,
//! doi:10.1016/0022-314X(80)90084-0, for the strong-probable-prime test of [`is_prime`] (the
//! bases are cited there); J. M. Pollard, "A Monte Carlo method for factorization", BIT
//! 15(3):331-334, 1975, doi:10.1007/BF01933667, and R. P. Brent, BIT 20, 1980 (cited at
//! `rho`), for the rho walk; R. S. Lehman, Math. Comp. 28, 1974 (cited at `lehman`), for the
//! fallback; P. L. Montgomery, 1985 (cited at `Montgomery`), for the products. Read
//! 2026-11-21: Miller and Rabin in the publisher's PDFs as OpenAlex caches them, Pollard in a
//! scanned PDF from LibGen (verification only); Brent read earlier.
//!
//! Miller, sec. 2, pp. 302-303, defines the test A_f: for each `a ≤ f(n)`, "composite" if
//! `a | n`, if `a^(n-1) ≢ 1 mod n`, or if `1 < gcd((a^((n-1)/2^k) mod n) - 1, n) < n` for some
//! `1 ≤ k ≤ ν_2(n-1)`, after a check that `n` is no perfect power; with `f(n) = c |n|^2`,
//! `|n|` the bit length, it decides primality under the extended Riemann hypothesis (proof
//! of Theorem 2, p. 305). The explicit constant is E. Bach's: "Explicit bounds for primality
//! testing and related problems", Math. Comp. 55(191):355-380, 1990,
//! doi:10.1090/S0025-5718-1990-1023756-8, Theorem 2 (ERH), p. 372: for `G` a nontrivial
//! subgroup of `Z/(m)*` with `n ∈ G` for every positive `n < x`, "x < 2(log m)^2"; and pp.
//! 372-373: "if the ERH is true, then a composite number m has a witness for its compositeness
//! (in the sense of [30 or 43]) that is at most 2 log^2 m", its reference 30 being Miller's
//! paper (read 2026-11-21 in the published version's PDF, the exponents checked on the page
//! images). This bound is conditional on the hypothesis: a proof of GRH was announced on
//! 2026-11-20 (L. Alpoge, with a Lean 4 formalization) and its acceptance is pending. Nothing
//! here depends on it: [`is_prime`] is exact on every `u64`, with no hypothesis, by the fixed
//! bases below Sorenson and Webster's `psi_12` (cited there). Rabin, sec. 1, p. 130, takes the
//! same condition as his "witness to the compositeness of n" and proves without ERH
//! (Theorem 1) that if `4 < n` is composite then at least `3(n-1)/4` of the `1 ≤ b < n` are
//! witnesses; his note of 1978, p. 137, credits Knuth with the form without the gcd that
//! [`is_prime`] runs: with `n - 1 = 2^l m`, `x_0 = x^m`, `x_i = x_{i-1}^2`, a composite odd
//! `n` has, for at least
//! `3(n-1)/4` of the `x`, either `x_l ≠ 1` or some `x_i = 1` with `x_{i-1} ≠ n - 1`. Neither
//! paper gives the fixed bases that decide every 64-bit number; those are cited at
//! [`is_prime`]. Pollard, sec. 1, p. 331: `x_0 = 2`, `x_{i+1} = x_i^2 - 1 (mod n)`, the pairs
//! `(x_i, x_{2i})`, the products `Q_i = Π (x_{2j} - x_j) mod n`, and `gcd(Q_i, n)` every
//! `m` steps ("say, m = 100"), a prime factor `p` in "O(p^(1/2))" operations, a claim the
//! paper calls apparent and does not prove. Departures: `rho` walks `x^2 + 1` from 2, where
//! Pollard's example is `x^2 - 1` (he allows other polynomials and starts), and follows
//! Brent's form (one walk, rounds of sizes 1, 2, 4, ... in place of the pairs `(x_i, x_{2i})`),
//! cited there; it takes a gcd every 128 products, Pollard's `m`.

/// The prime factors of `n` with their multiplicities, in increasing order of prime; empty for
/// `n <= 1`.
// Complexity tradeoff: trial division is O(sqrt n) divisions, 2^32 for a 64-bit prime product;
// Pollard's rho finds a factor `p` in O(sqrt p) = O(n^(1/4)) expected products (Pollard's
// heuristic, unproved in general), and Miller-Rabin tells a prime in O(log n) products.
//
// Cost for `n < 2^44` (proof; PROOF-factored-coprime-cost, 2026-11-20). Every number `split`
// gets is an odd composite `m` dividing `n`, so `m < 2^44`, and its least prime `p` is at most
// `m^(1/2) < 2^22`.
// 1. The run with `c = 1` ([`rho`], Brent 1980, doi:10.1007/BF01933190) on `m` costs through its
//    last batch at most what the run on `p` costs (proof at `rho`), which is at most the table
//    `the_rho_cost_below_2_22_is_the_table` computes over every odd prime below 2^22: 25854
//    steps, 9471 products into `q` and 80 gcds. The search back adds at most 128 steps and 128
//    gcds (proof at `rho`). Each step is one Montgomery product and one addition.
// 2. When that run ends with `g = m`, Lehman's method (R. S. Lehman 1974,
//    doi:10.1090/S0025-5718-1974-0340163-2; proof at `lehman_search`) costs, with `r =
//    floor(m^(1/3)) <= floor((2^44 - 1)^(1/3)) = 26007` (`26008^3 > 2^44`): at most `r - 1 =
//    26006` divisions and `2.5 r + 0.75 < 65019` tries, and per `k <= r` two `isqrt` and one
//    division.
// 3. The odd part of `n` has at most 27 prime factors with multiplicity (`3^27 < 2^44 < 3^28`),
//    and each `split` adds one entry to `left`, so there are at most 26 splits; every entry ever
//    pushed is tested by `is_prime` once, at most `2 * 26 + 1 = 53` calls, each at most 12 bases
//    of at most `2 * 44` products for the power and 43 squarings, under 1600 products, and one
//    128-bit remainder in `Montgomery::new`.
// So `factor(n)` for `n < 2^44` costs at most 26 * (25982 steps + 9471 products + 208 gcds +
// 26006 divisions + 65019 tries + 26007 `k` values) + 53 * 1600 products, a constant: O(1) per
// input, with no expectation and no heuristic. The constant is large and loose (it adds the
// worst case of every part at once); `examples/timing.rs` measures the typical cost. What the
// tests cannot catch: the table test fixes the run's code at the time it ran, so the proof at
// `rho` (that the table covers composites) is checked only on samples
// (`a_run_stops_no_later_than_on_its_least_prime`).
pub fn factor(n: u64) -> Vec<(u64, u64)> {
    // 0 has no prime factorization, and `0 >> 0.trailing_zeros()` below would shift by 64.
    if n == 0 {
        return Vec::new();
    }
    let mut primes = Vec::new();
    let mut left = vec![n];
    while let Some(m) = left.pop() {
        if m == 1 {
            continue;
        }
        if m.is_multiple_of(2) {
            let z = m.trailing_zeros();
            primes.extend(std::iter::repeat_n(2, z as usize));
            left.push(m >> z);
        } else if is_prime(m) {
            primes.push(m);
        } else {
            let d = split(m);
            left.push(d);
            left.push(m / d);
        }
    }
    primes.sort_unstable();
    let mut out: Vec<(u64, u64)> = Vec::new();
    for p in primes {
        match out.last_mut() {
            Some((q, k)) if *q == p => *k += 1,
            _ => out.push((p, 1)),
        }
    }
    out
}

use crate::{gcd_u64, gcd_u128, inverse_mod_2_64};

/// A machine word that [`Montgomery`] works modulo: `u64`, for [`factor`] and [`is_prime`], and
/// `u128`, for `factor_u128` and `is_prime_u128` (FACTOR-u128, PRIME-u128). One generic form, not
/// a copy per width (DRY-number-theory: one routine per job); each width is compiled apart, so
/// the `u64` code is the same machine code as before the generalization.
pub(crate) trait Word:
    Copy
    + Eq
    + Ord
    + std::fmt::Debug
    + std::ops::Sub<Output = Self>
    + std::ops::Rem<Output = Self>
    + std::ops::Shr<u32, Output = Self>
    + std::ops::BitAnd<Output = Self>
    + From<u64>
{
    /// The product of two words, twice as wide.
    type Wide: Copy;
    const ZERO: Self;
    const ONE: Self;
    fn wide_mul(a: Self, b: Self) -> Self::Wide;
    /// The low and the high word of a wide value.
    fn halves(t: Self::Wide) -> (Self, Self);
    /// The wide value of one word.
    fn widen(self) -> Self::Wide;
    fn wrapping_mul(self, b: Self) -> Self;
    fn wrapping_add(self, b: Self) -> Self;
    fn wrapping_sub(self, b: Self) -> Self;
    fn overflowing_add(self, b: Self) -> (Self, bool);
    fn overflowing_sub(self, b: Self) -> (Self, bool);
    /// `self^-1 mod R`, for an odd `self`.
    fn inverse_mod_r(self) -> Self;
    fn gcd(self, b: Self) -> Self;
    fn trailing_zeros(self) -> u32;
    /// `R^2 mod n`, for an odd `n > 1`.
    fn r_squared_mod(n: Self) -> Self;
}

// `#[inline]` on these methods and on the small `Montgomery` ones: the dev profile builds with
// `lto = "off"` (Cargo.toml), and a generic instance may be placed in another codegen unit than
// its caller, where it is then called, not inlined. Without the attributes the debug test binary
// took 27.5 s at load 67 (over its 36 s limit in merge_check at load 57), with
// `the_rho_cost_below_2_22_is_the_table` at 45.6 s; with them 9.9 s and 5.8 s at load 48.
impl Word for u64 {
    type Wide = u128;
    const ZERO: u64 = 0;
    const ONE: u64 = 1;
    #[inline]
    fn wide_mul(a: u64, b: u64) -> u128 {
        u128::from(a) * u128::from(b)
    }
    #[inline]
    fn halves(t: u128) -> (u64, u64) {
        (t as u64, (t >> 64) as u64)
    }
    #[inline]
    fn widen(self) -> u128 {
        u128::from(self)
    }
    #[inline]
    fn wrapping_mul(self, b: u64) -> u64 {
        u64::wrapping_mul(self, b)
    }
    #[inline]
    fn wrapping_add(self, b: u64) -> u64 {
        u64::wrapping_add(self, b)
    }
    #[inline]
    fn wrapping_sub(self, b: u64) -> u64 {
        u64::wrapping_sub(self, b)
    }
    #[inline]
    fn overflowing_add(self, b: u64) -> (u64, bool) {
        u64::overflowing_add(self, b)
    }
    #[inline]
    fn overflowing_sub(self, b: u64) -> (u64, bool) {
        u64::overflowing_sub(self, b)
    }
    #[inline]
    fn inverse_mod_r(self) -> u64 {
        inverse_mod_2_64(self)
    }
    #[inline]
    fn gcd(self, b: u64) -> u64 {
        gcd_u64(self, b)
    }
    #[inline]
    fn trailing_zeros(self) -> u32 {
        u64::trailing_zeros(self)
    }
    /// `2^128 mod n = ((2^128 - 1) mod n + 1) mod n`, one 128-bit division.
    #[inline]
    fn r_squared_mod(n: u64) -> u64 {
        // Exact: the remainder is below `n`, a `u64`.
        ((u128::MAX % u128::from(n) + 1) % u128::from(n)) as u64
    }
}

impl Word for u128 {
    /// `(low, high)`.
    type Wide = (u128, u128);
    const ZERO: u128 = 0;
    const ONE: u128 = 1;
    /// Schoolbook on 64-bit halves: `a b = a1 b1 2^128 + (a0 b1 + a1 b0) 2^64 + a0 b0`. The
    /// middle sum `hi(a0 b0) + lo(a0 b1) + lo(a1 b0)` is below `3 * 2^64`, a `u128`, and its high
    /// part carries into the high word, which cannot overflow since `a b < 2^256`.
    #[inline]
    fn wide_mul(a: u128, b: u128) -> (u128, u128) {
        let lo64 = |x: u128| x & u128::from(u64::MAX);
        let (a0, a1, b0, b1) = (lo64(a), a >> 64, lo64(b), b >> 64);
        let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
        let mid = (p00 >> 64) + lo64(p01) + lo64(p10);
        (
            lo64(p00) | (mid << 64),
            p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64),
        )
    }
    #[inline]
    fn halves(t: (u128, u128)) -> (u128, u128) {
        t
    }
    #[inline]
    fn widen(self) -> (u128, u128) {
        (self, 0)
    }
    #[inline]
    fn wrapping_mul(self, b: u128) -> u128 {
        u128::wrapping_mul(self, b)
    }
    #[inline]
    fn wrapping_add(self, b: u128) -> u128 {
        u128::wrapping_add(self, b)
    }
    #[inline]
    fn wrapping_sub(self, b: u128) -> u128 {
        u128::wrapping_sub(self, b)
    }
    #[inline]
    fn overflowing_add(self, b: u128) -> (u128, bool) {
        u128::overflowing_add(self, b)
    }
    #[inline]
    fn overflowing_sub(self, b: u128) -> (u128, bool) {
        u128::overflowing_sub(self, b)
    }
    /// Newton's step `y (2 - x y)` from the inverse modulo `2^64` ([`inverse_mod_2_64`] on the
    /// low word, right in 64 bits) doubles the right bits once more, to 128 (the argument at
    /// [`inverse_mod_2_64`]).
    #[inline]
    fn inverse_mod_r(self) -> u128 {
        let y = u128::from(inverse_mod_2_64(self as u64));
        y.wrapping_mul(2u128.wrapping_sub(self.wrapping_mul(y)))
    }
    #[inline]
    fn gcd(self, b: u128) -> u128 {
        gcd_u128(self, b)
    }
    #[inline]
    fn trailing_zeros(self) -> u32 {
        u128::trailing_zeros(self)
    }
    /// `R mod n = ((2^128 - 1) mod n + 1) mod n`, then `R^2 mod n` by doubling it 128 times
    /// modulo `n`: 128 additions, where one division of the 256-bit `2^256` would need a
    /// 256-by-128-bit division routine, which `u128` lacks.
    #[inline]
    fn r_squared_mod(n: u128) -> u128 {
        let mut r = (u128::MAX % n + 1) % n;
        for _ in 0..128 {
            // `r < n`, so `2 r < 2 n`; one subtraction brings it below `n`, with the carry out of
            // `u128` when `2 r >= 2^128 > n`.
            let (s, carry) = r.overflowing_add(r);
            r = if carry || s >= n {
                s.wrapping_sub(n)
            } else {
                s
            };
        }
        r
    }
}

/// Products modulo an odd `n > 1` in Montgomery form (P. L. Montgomery, "Modular multiplication
/// without trial division", Math. Comp. 44(170):519-521, 1985,
/// doi:10.1090/S0025-5718-1985-0777282-X): a residue `x` is held as `x R mod n`, for
/// `R = 2^k`, `k` the bits of the word `W` (64 or 128), and the product of two held residues
/// `a R` and `b R` is `a b R mod n`, found with three multiplications and no division. Read
/// 2026-11-21 in the publisher's PDF as OpenAlex caches it (AMS's own link gave no PDF). Sec. 1,
/// p. 519, with `R R^-1 - N N' = 1` (so `N' = -N^-1 mod R`), "function REDC(T): m ← (T mod R)N'
/// mod R [so 0 ≤ m < R]; t ← (T + mN)/R; if t ≥ N then return t − N else return t", valid for
/// `0 ≤ T < RN`, since `mN ≡ −T mod R` makes `t` an integer, `t ≡ T R^-1 mod N`, and
/// `0 ≤ t < 2N`; `REDC(x y)` of two held residues is their held product, and a number enters as
/// `REDC((x mod N)(R^2 mod N))` (p. 520). Departure: [`Montgomery::reduce`] uses `+N^-1` and
/// subtracts, `(T - m N) / R`, adding `N` back on a borrow, so no sum can pass `R^2` and `n` may
/// be any odd word. The paper foresees this on p. 519: "If R and N are large, then T + mN may
/// exceed the largest double-precision value. One can circumvent this by adjusting m so −R < m
/// ≤ 0." `montgomery_arithmetic_agrees_with_division` checks every operation against plain
/// division, on moduli up to `2^64 - 1`, and `wide_montgomery_arithmetic_agrees_with_num_bigint`
/// on moduli up to `2^128 - 1`; they sample the moduli, so they cannot show that no odd modulus
/// fails.
// Complexity tradeoff: `mul_mod` divides a 128-bit product by `n`, a call of the 128-bit
// division routine; the form here costs one division per modulus (for `R^2 mod n`) and then
// three word multiplications per product (on `u128`, three schoolbook products of four 64-bit
// multiplications each, against a 256-by-128-bit division per product without it). Measured by
// `examples/timing.rs` (COMPLEXITY.md row DRY-number-theory). Its residues are in `[0, n)`, so
// equal residues are equal words.
pub(crate) struct Montgomery<W: Word> {
    pub(crate) n: W,
    /// `n^-1 mod R`.
    n_inv: W,
    /// `R^2 mod n`, which [`Montgomery::to`] multiplies by.
    r2: W,
}

impl<W: Word> Montgomery<W> {
    pub(crate) fn new(n: W) -> Montgomery<W> {
        debug_assert!(n & W::ONE == W::ONE && n > W::ONE, "an odd modulus above 1");
        Montgomery {
            n,
            n_inv: n.inverse_mod_r(),
            r2: W::r_squared_mod(n),
        }
    }

    /// `t R^-1 mod n`, in `[0, n)`, for `t < n R`.
    #[inline]
    pub(crate) fn reduce(&self, t: W::Wide) -> W {
        // `m = t n^-1 mod R` makes `m n = t mod R`, so the low words of `t` and `m n` are equal
        // and `(t - m n) / R = hi(t) - hi(m n)` exactly, `t R^-1` modulo `n`. Both high words
        // are below `n` (`t < n R` and `m n < R n`), so the difference is in `(-n, n)`: a
        // borrow means it is negative, and adding `n` (wrapping back past `R`) gives the
        // residue in `[0, n)`. This subtracting form needs no `n < R / 2`, unlike the adding one.
        let (lo, hi) = W::halves(t);
        let m = lo.wrapping_mul(self.n_inv);
        let (_, mn_hi) = W::halves(W::wide_mul(m, self.n));
        let (d, borrow) = hi.overflowing_sub(mn_hi);
        if borrow { d.wrapping_add(self.n) } else { d }
    }

    /// The product of two held residues, each below `n` (so `a b < n^2 < n R`).
    #[inline]
    pub(crate) fn mul(&self, a: W, b: W) -> W {
        self.reduce(W::wide_mul(a, b))
    }

    /// The sum of two held residues, each below `n`.
    #[inline]
    pub(crate) fn add(&self, a: W, b: W) -> W {
        let (s, carry) = a.overflowing_add(b);
        if carry || s >= self.n {
            s.wrapping_sub(self.n)
        } else {
            s
        }
    }

    /// The difference of two held residues, each below `n`.
    #[inline]
    pub(crate) fn sub(&self, a: W, b: W) -> W {
        let (d, borrow) = a.overflowing_sub(b);
        if borrow { d.wrapping_add(self.n) } else { d }
    }

    /// `x R mod n`, the held form of `x`.
    #[inline]
    pub(crate) fn to(&self, x: W) -> W {
        self.mul(x % self.n, self.r2)
    }

    /// `R mod n`, the held form of 1.
    #[inline]
    pub(crate) fn one(&self) -> W {
        self.reduce(self.r2.widen())
    }

    /// The held form of `a^e`, for `a` held, by squaring: O(log e) products.
    pub(crate) fn pow(&self, mut a: W, mut e: W) -> W {
        let mut r = self.one();
        while e > W::ZERO {
            if e & W::ONE == W::ONE {
                r = self.mul(r, a);
            }
            a = self.mul(a, a);
            e = e >> 1;
        }
        r
    }

    /// Whether the odd `n` passes the strong probable-prime test to each base of `bases`
    /// (Miller 1976 and Rabin 1980, cited at the top of this file): with `n - 1 = 2^s d`, `d`
    /// odd, `a^d = 1` or `a^(2^i d) = -1` for some `0 <= i < s`. A prime passes every base not
    /// divisible by it; a composite fails at least `3/4` of the bases below it (Rabin, Theorem
    /// 1). O(log n) products a base.
    pub(crate) fn strong_probable_prime(&self, bases: &[u64]) -> bool {
        let n = self.n;
        let (one, minus_one) = (self.one(), n - self.one());
        let s = (n - W::ONE).trailing_zeros();
        let d = (n - W::ONE) >> s;
        'bases: for &a in bases {
            let mut x = self.pow(self.to(W::from(a)), d);
            if x == one || x == minus_one {
                continue;
            }
            for _ in 1..s {
                x = self.mul(x, x);
                if x == minus_one {
                    continue 'bases;
                }
            }
            return false;
        }
        true
    }
}

/// Whether `n` is prime; exact for every 64-bit `n`: Miller-Rabin with the first twelve primes
/// as bases, or the first one, two or three below the least composite that passes them.
// Complexity tradeoff: trial division is O(sqrt n) divisions, 2^32 for a 64-bit prime; at most
// twelve Miller-Rabin rounds are O(12 log n) products modulo `n`, in Montgomery form.
pub fn is_prime(n: u64) -> bool {
    // The bases: the twelve primes 2 to 37. Miller-Rabin with the first `k` primes as bases
    // decides every `n` below the least strong pseudoprime to all of them, `psi_k`, and
    // `psi_12 = 318665857834031151167461 > 2^64` (Sorenson and Webster, "Strong pseudoprimes to
    // twelve prime bases", Math. Comp. 86, 2017, 985-1003, doi:10.1090/mcom/3134). So no
    // composite below 2^64 passes all twelve. Citation checked 2026-11-20: Crossref gives that
    // title, authors, volume and pages for the DOI, and the paper's own LaTeX (arXiv 1509.00864v1,
    // manybases-arxiv.tex line 120) states `\psi_{12} = 3186 65857 83403 11511 67461`, this
    // value. No test here can check `psi_12`, since it is above 2^64. The tests check it
    // against trial division below 2^16 and on strong pseudoprimes to small bases
    // (`factors_of_wide_numbers_are_their_primes`: 3215031751 passes bases 2, 3, 5 and 7). The
    // bases also serve as trial divisors: a multiple of one is prime only when equal to it,
    // which rejects every even candidate and about 70% of odd ones (the product of `1 - 1/p`
    // over the primes 3 to 37 is about 0.30) before any product.
    const BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    // Fewer bases below the least strong pseudoprimes to the first one, two and three primes:
    // `psi_1 = 2047`, `psi_2 = 1373653` and `psi_3 = 25326001` (Pomerance, Selfridge and
    // Wagstaff, "The pseudoprimes to 25 * 10^9", Math. Comp. 35, 1980, 1003-1026,
    // doi:10.1090/s0025-5718-1980-0572872-7). Read 2026-11-21 (PDF, LibGen, verification only;
    // title and authors checked on the copy). Sec. 9, p. 1023: "The first spsp(2) is 2047 =
    // 23 • 89. The first number which is both an spsp(2) and an spsp(3) is 1373653 = 829 •
    // 1657." Table 7, p. 1022, lists the strong pseudoprimes to all of the bases 2, 3 and 5
    // below 25 * 10^9 in increasing order; its first entry is 25326001 = 2251 * 11251. So the
    // three values here are the paper's, and the rule "n below psi_k needs only the first k
    // bases" is the definition of psi_k as the least composite that passes those k bases. The
    // paper's evidence is computation, not proof: "We have computed all psp(2)'s below
    // 25 • 10^9" (sec. 1), and every spsp(2) is a psp(2), so sec. 9 and Table 7 are a search of
    // that list, which this code does not repeat. They do not rest on the paper alone:
    // the test `primality_agrees_with_the_sieve_below_psi_3` checks every `n` below `psi_3`
    // against the sieve and checks that these three composites are rejected. A value too large
    // fails it (a composite below it would be tested with too few bases); a value too small
    // passes it but costs only extra rounds, never a wrong answer. Larger `psi_k` are not used:
    // no test here can check them, and above `psi_3` the saving is at most 9 of 12 rounds, for
    // primes only (a composite almost always fails the first base).
    const PSI: [u64; 3] = [2047, 1_373_653, 25_326_001];
    if n < 2 {
        return false;
    }
    for p in BASES {
        if n.is_multiple_of(p) {
            return n == p;
        }
    }
    // `n` is odd and above 37 here, so above every base.
    let k = PSI
        .iter()
        .position(|&psi| n < psi)
        .map_or(BASES.len(), |i| i + 1);
    Montgomery::new(n).strong_probable_prime(&BASES[..k])
}

/// A factor of the odd composite `n` other than 1 and `n`: Pollard's rho in Brent's form with
/// `c = 1` ([`rho`]), and Lehman's method ([`lehman`]) when that run ends without one.
// Complexity tradeoff: rho costs O(sqrt p) products for the least prime `p` in expectation by
// Pollard's heuristic (unproved), and Lehman's method O(n^(1/3)) operations, proved. Below 2^44
// both are bounded by proved constants (the cost comment at `factor`). Trying the next `c`
// instead of Lehman's method, as before 2026-11-20, is about as fast in expectation but has no
// proved bound short of `c = p - 2`, about `p` runs. Measured 2026-11-20: the run with `c = 1`
// ends with `g = n` on 111 of 200000 random products of two 22-bit primes and on none of 5000
// products of two 32-bit primes, so Lehman's method runs on few inputs; it takes 1.4 ms on the
// largest prime below 2^44 (a full search, which `split` never runs: `factor` calls it only on
// composites) and 11 ms on 4294967291 * 4294967279, nearly all of it trial division.
fn split(n: u64) -> u64 {
    let run = rho(&Montgomery::new(n));
    if run.g != n {
        return run.g;
    }
    lehman(n).0
}

/// What a run of [`rho`] cost up to the end of the batch where it stopped: calls of the step
/// `x^2 + 1`, products into `q`, and gcds with the modulus.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct RhoCost {
    steps: u64,
    products: u64,
    gcds: u64,
}

/// The run of Brent's search with `c = 1` on the odd modulus `n > 1` of `mont`.
pub(crate) struct RhoRun<W: Word> {
    /// The gcd it ends with: a factor of `n` above 1, `n` itself when the search back
    /// found every prime of `n` at once, and 1 when [`rho_within`] stopped at its step count.
    pub(crate) g: W,
    /// The cost through the batch whose gcd first passed 1. Read only by the tests that check
    /// the cost bound (counting costs a few additions a batch); the counts are made by this
    /// code, not by a copy, so the table test measures the walk `split` runs.
    #[cfg_attr(not(test), expect(dead_code, reason = "read by the cost tests"))]
    batches: RhoCost,
    /// The steps of the search back from that batch's start, each one step and one gcd; 0 when
    /// the batch's gcd was below `n`. At most 128, the batch's length (proof at `rho`).
    #[cfg_attr(not(test), expect(dead_code, reason = "read by the cost tests"))]
    back: u64,
}

/// Brent's cycle search on `x^2 + 1` modulo `n`, from 2 (R. P. Brent, "An improved Monte Carlo
/// factorization algorithm", BIT 20(2):176-184, 1980, doi:10.1007/BF01933190). The loop is the
/// paper's final algorithm of section 7, with its names: "repeat x := y; for i := 1 to r do
/// y := f(y); k := 0; repeat ys := y; for i := 1 to min(m, r - k) do begin y := f(y);
/// q := q × |x - y| mod N end; G := GCD(q, N); k := k + m until (k > r) or (G > 1); r := 2 × r
/// until G > 1", then, if `G = N`, "repeat ys := f(ys); G := GCD(|x - ys|, N) until G > 1".
/// Departures: the paper's tests took `x0 = 0`, `f(x) = x^2 + 3` and `m = 1`; here `x0 = 2`,
/// `c = 1` and `m = 128`; the inner loop stops at `k >= r`, which skips only the paper's last
/// batch of `min(m, 0) = 0` steps; and where the paper stops on "failure" (`G = N` again),
/// [`split`] goes on with Lehman's method, not another `c`. Checked 2026-11-20: the DOI on
/// Crossref and the algorithm read in the paper (the author's scan). The differences are
/// multiplied in batches of 128 and one gcd is taken per batch, so the O(log n) gcd costs 1/128
/// of a product per step; a batch that overshoots (`g = n`) is searched again one step at a
/// time from `ys`. Any batch size is exact; a larger one saves gcds and costs more steps when a
/// batch overshoots.
///
/// The walk is in Montgomery form (P. L. Montgomery 1985,
/// doi:10.1090/S0025-5718-1985-0777282-X; the full comment is at struct `Montgomery`): it holds
/// `x R` for each `x` of the walk above, since `(x R)^2 R^-1 + R = (x^2 + 1) R`. A difference of
/// held values is the difference of the values times `R`, and each product into `q` adds a
/// factor `R^-1`; `R = 2^64` is a unit modulo every odd number, so every gcd below is as for
/// the plain walk.
///
/// It ends, for every odd `n > 1`: the walk modulo `n` is eventually periodic, with tail `mu`
/// and period `lambda`. A round of size `r` sets `x` to the current `y`, moves `y` on `r` steps
/// with no comparison, then compares `x` with the next `r` values, at distances `r + 1` to `2 r`
/// from `x`, and leaves `y` `2 r` steps on. Rounds have sizes `1, 2, 4, ...`, so `x` of the round
/// of size `r` is the walk's value at index `2 (1 + 2 + ... + r / 2) = 2 r - 2`. Once `2 r - 2 >=
/// mu` and `r >= lambda`, `x` is in the cycle, and the `r` consecutive distances `r + 1` to `2 r`
/// hold a multiple of `lambda`, where `y = x`: a difference of 0, so `q = 0` and `g = n` at that
/// batch at the latest.
///
/// What the cost bound of [`factor`] rests on (proof). For a prime `p` dividing `n`, the run on
/// `n` and the run on the modulus `p` (this function with `mont` for `p`) see the same walk
/// modulo `p`: both hold `x R` for the same plain walk `x_0 = 2`, `x_(i+1) = x_i^2 + 1`, and
/// a held value modulo `n`, reduced modulo `p`, is the held value modulo `p` (`x R mod n mod p
/// = x R mod p`, as `p | n`). Their schedules (`r`, the batches) do not depend on the modulus
/// until the run stops. So `p` divides a difference `|x - y|` of the run on `n` at exactly the
/// comparisons where the difference of the run on `p` is 0, and the run on `p` stops at the
/// end of the first batch holding such a comparison (`q` becomes 0 modulo `p`, and stays 0, so
/// `g = p`). In the run on `n`, `q` is then 0 modulo `p` too (each product multiplies by a
/// difference and by the unit `R^-1`, so `p | q` once `p` divides one difference), so its gcd
/// is at least `p > 1` at that batch, and the run on `n` stops there or earlier. Its cost
/// through its last batch is therefore at most the run on `p`'s `batches`, for every prime `p`
/// of `n`, the least one in particular. The search back: before the last batch every gcd was 1,
/// so no prime of `n` divided an earlier difference; a gcd of `n` means some prime of `n`
/// divides a difference of the last batch, which has at most 128 comparisons, and the search
/// back recomputes those differences in order from `ys` with the same `x`, so it stops after
/// at most 128 steps. Tests: `the_rho_cost_below_2_22_is_the_table` (every odd prime below
/// 2^22) and `a_run_stops_no_later_than_on_its_least_prime` (the inequality on composites).
fn rho<W: Word>(mont: &Montgomery<W>) -> RhoRun<W> {
    rho_within(mont, u64::MAX)
}

/// [`rho`], stopped with `g = 1` once a round ends with `max_steps` steps or more taken:
/// `factor_u128` runs it for as many products as one curve of the elliptic curve method
/// costs (the comment at `split_u128`).
pub(crate) fn rho_within<W: Word>(mont: &Montgomery<W>, max_steps: u64) -> RhoRun<W> {
    let n = mont.n;
    let one = mont.one();
    let f = |x: W| mont.add(mont.mul(x, x), one);
    let start = mont.to(W::from(2));
    let (mut x, mut y, mut g, mut r) = (start, start, W::ONE, 1u64);
    // Any unit modulo `n`: the products only need their gcd with `n`.
    let mut q = W::ONE;
    let mut ys = y;
    let mut batches = RhoCost::default();
    while g == W::ONE && batches.steps < max_steps {
        x = y;
        for _ in 0..r {
            y = f(y);
        }
        batches.steps += r;
        let mut k = 0;
        while k < r && g == W::ONE {
            ys = y;
            let m = 128.min(r - k);
            for _ in 0..m {
                y = f(y);
                q = mont.mul(q, abs_diff(x, y));
            }
            g = q.gcd(n);
            batches.steps += m;
            batches.products += m;
            batches.gcds += 1;
            k += 128;
        }
        r *= 2;
    }
    let mut back = 0;
    if g == n {
        loop {
            ys = f(ys);
            g = abs_diff(x, ys).gcd(n);
            back += 1;
            if g > W::ONE {
                break;
            }
        }
    }
    RhoRun { g, batches, back }
}

/// `|a - b|`.
fn abs_diff<W: Word>(a: W, b: W) -> W {
    if a > b { a - b } else { b - a }
}

/// What [`lehman`] cost: trial divisions, and values of `x` tried in the search for a square.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct LehmanCost {
    divisions: u64,
    tries: u64,
}

/// A factor of the odd composite `n` other than 1 and `n`, by R. S. Lehman's method, "Factoring
/// large integers", Math. Comp. 28(126):637-646, 1974, doi:10.1090/S0025-5718-1974-0340163-2
/// (read 2026-11-20 in the AMS scan, fetched by allpapers; the DOI's identity by Crossref). Trial
/// division by every `d <= r = floor(n^(1/3))`, then [`lehman_search`]. Its cost, with `r` as
/// above: at most `r - 1` divisions and at most `2.5 r + 0.75` tries (proof at
/// [`lehman_search`]), each try a 128-bit square, a mask test and at most one `isqrt` and one
/// gcd, and per `k <= r` one 128-bit and one 64-bit `isqrt` and one division.
///
/// Departures from the paper's program (section 5): it takes `r = floor(0.1 n^(1/3))`, tries
/// the `k` in an order of many divisors first, uses the congruences of `x` modulo 2 and 4, and
/// filters squares modulo 729; here `r = floor(n^(1/3))`, `k` runs from 1, every `x` of a
/// range holding the theorem's is tried, and squares are filtered modulo 64. These change only
/// the constant: the theorem below needs none of them.
// Complexity tradeoff: trial division alone is O(sqrt n) divisions, 2^21 at 2^44; this is
// O(n^(1/3)), about 26000 divisions and 65000 tries at 2^44. Shanks' SQUFOF is O(n^(1/4)) but its
// bound is heuristic; Lehman's is a theorem.
fn lehman(n: u64) -> (u64, LehmanCost) {
    let r = crate::cbrt_floor(n);
    let mut cost = LehmanCost::default();
    for d in 2..=r {
        cost.divisions += 1;
        if n.is_multiple_of(d) {
            return (d, cost);
        }
    }
    let g = lehman_search(n, r, &mut cost).expect("Lehman's theorem: an odd n = p q has a pair");
    (g, cost)
}

/// For the odd `n` with no factor in `2..=r`, `r = floor(n^(1/3))`: the first `gcd(x + y, n)`
/// strictly between 1 and `n` over `k = 1..=r` and `x` from `isqrt(4 k n)` to
/// `isqrt(4 k n) + e_k`, `e_k = ceil((isqrt(floor(n / k)) + 1) / (4 (r + 1)))`, where
/// `x^2 - 4 k n = y^2` for an integer `y >= 0`; `None` when there is none, as for a prime `n`.
///
/// Why one is found for every such composite `n` (proof). Lehman's Theorem (section 2): "Suppose
/// that n is a positive odd integer and r is an integer such that 1 <= r < n^(1/2). If n = pq
/// where p and q are primes and (n/(r + 1))^(1/2) < p <= n^(1/2), then there are nonnegative
/// integers x, y and k such that x^2 - y^2 = 4kn, 1 <= k <= r, ... 0 <= x - (4kn)^(1/2) <=
/// (1/(4(r + 1)))(n/k)^(1/2)" (2.1, with congruences of `x` not used here), "and p =
/// min(gcd(x + y, n), gcd(x - y, n))" (2.2).
/// 1. `n` is `p q` with `p <= q` prime: `n` is composite with no prime factor `<= r`, and
///    `r + 1 > n^(1/3)` (as `(r + 1)^3 > n`), so every prime factor exceeds `n^(1/3)`, and three
///    of them would multiply to more than `n`.
/// 2. The hypotheses hold: `n` is odd; `n >= 9`, so `r >= 2 >= 1`, and `r <= n^(1/3) < n^(1/2)`;
///    `p <= n^(1/2)` as `p <= q`; and `p >= r + 1`, so `p^2 (r + 1) >= (r + 1)^3 > n`, which is
///    `p > (n / (r + 1))^(1/2)`.
/// 3. The theorem's `x` lies in the range tried for its `k`: `x >= (4 k n)^(1/2) >=
///    isqrt(4 k n)`; and `(4 k n)^(1/2) < isqrt(4 k n) + 1`, `(n / k)^(1/2) < isqrt(floor(n / k))
///    + 1` (as `n / k < floor(n / k) + 1 <= (isqrt(floor(n / k)) + 1)^2`), so `x < isqrt(4 k n)
///    + 1 + e_k`, and `x <= isqrt(4 k n) + e_k` as both sides are integers.
/// 4. At that `x`, `x^2 - 4 k n = y^2` has the one root `y >= 0`, the theorem's. The paper's
///    proof (section 4, (4.6) and (4.7)) builds it as `x = a q + b p`, `y = |a q - b p|` with
///    `a b = k`, `a, b >= 1`. So `x + y = 2 max(a q, b p)`, and `a, b <= k <= r < p <= q`, so
///    neither `a` nor `b` holds `p` or `q`; with `p` odd, `gcd(2 a q, p q)` is `q` when `p != q`
///    and `p` when `p = q`, and `gcd(2 b p, p q) = p`. So `gcd(x + y, n)` is `p` or `q`, strictly
///    between 1 and `n`, and the search returns at that `(k, x)` or earlier.
///
/// No search returns a wrong factor: every value returned is checked to be a divisor strictly
/// between 1 and `n`.
///
/// The number of tries (proof): `sum_(k=1..r) (e_k + 1)`, with `e_k <= ((n / k)^(1/2) + 1) / (4
/// (r + 1)) + 1`, so it is at most `2 r + r / (4 (r + 1)) + (n^(1/2) / (4 (r + 1))) sum_k
/// k^(-1/2)`. The sum is below `2 r^(1/2)` (each `k^(-1/2) < 2 (k^(1/2) - (k - 1)^(1/2))`), and
/// `n^(1/2) < (r + 1)^(3/2)`, so the last term is below `(r + 1)^(1/2) r^(1/2) / 2 < (r + 1) /
/// 2`: in all below `2 r + 1/4 + (r + 1) / 2 = 2.5 r + 0.75`. `lehman_tries_stay_in_the_bound`
/// checks it on primes, where the search runs to the end.
///
/// Tests: `lehman_splits_every_odd_composite` (every odd composite below 2^16 whose least prime
/// is above its cube root, and products of two primes near 2^22 and 2^32),
/// `lehman_finds_nothing_in_a_prime`. They cannot tell this range from a wider one, which is
/// also correct and only slower; the bound test sees a range too wide by a factor.
fn lehman_search(n: u64, r: u64, cost: &mut LehmanCost) -> Option<u64> {
    let n128 = u128::from(n);
    let width = 4 * (u128::from(r) + 1);
    for k in 1..=r {
        let m = 4 * u128::from(k) * n128;
        let s = m.isqrt();
        let e = (u128::from((n / k).isqrt()) + 1).div_ceil(width);
        for x in s..=s + e {
            cost.tries += 1;
            let Some(v) = (x * x).checked_sub(m) else {
                continue;
            };
            if let Some(y) = crate::sqrt_exact_u128(v) {
                // `x + y < 2 x`, and `x <= isqrt(4 r n) + e < 2^45` for `n < 2^64`: a `u128`.
                let g = gcd_u64(((x + y) % n128) as u64, n);
                if g > 1 && g < n {
                    return Some(g);
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The factors of `n` by trial division.
    fn by_trial(mut n: u64) -> Vec<(u64, u64)> {
        let mut out = Vec::new();
        let mut p = 2;
        while p * p <= n {
            let mut k = 0;
            while n.is_multiple_of(p) {
                n /= p;
                k += 1;
            }
            if k > 0 {
                out.push((p, k));
            }
            p += 1;
        }
        if n > 1 {
            out.push((n, 1));
        }
        out
    }

    /// The table the cost bound of `factor` below `2^44` rests on (comment at `factor`): the
    /// most that the run with `c = 1` costs through its last batch, over every odd prime below
    /// `2^22`, field by field; and the search back, at most 128 steps. A computed bound, not a
    /// sampled one: the loop covers every such prime, and the proof at `rho` carries it to every
    /// composite whose least prime is one of them. A change to the walk, its start, the batch
    /// size or the schedule changes these numbers and fails this test, which is then to be
    /// updated together with the comment at `factor`. 5.4 s under a load of 45 on 32 cores
    /// (2026-11-20).
    #[test]
    fn the_rho_cost_below_2_22_is_the_table() {
        let odd = crate::odd_primes_below(1 << 22);
        let mut most = RhoCost::default();
        let mut back = 0;
        for i in (1..odd.len()).filter(|&i| odd[i]) {
            let p = 2 * i as u64 + 1;
            let run = rho(&Montgomery::new(p));
            assert_eq!(run.g, p, "the run on a prime ends with g = p");
            most.steps = most.steps.max(run.batches.steps);
            most.products = most.products.max(run.batches.products);
            most.gcds = most.gcds.max(run.batches.gcds);
            back = back.max(run.back);
        }
        assert_eq!(
            most,
            RhoCost {
                steps: 25_854,
                products: 9_471,
                gcds: 80
            }
        );
        assert_eq!(back, 128);
    }

    /// The odd composites below `2^16` with no factor up to their cube root: those Lehman's
    /// search, not the trial division before it, must split.
    fn lehman_inputs() -> Vec<u64> {
        (9..1u64 << 16)
            .step_by(2)
            .filter(|&n| {
                let f = by_trial(n);
                f != [(n, 1)] && f[0].0 > crate::cbrt_floor(n)
            })
            .collect()
    }

    /// The inequality the cost bound of `factor` rests on (proof at `rho`): the run on a
    /// composite `n` stops no later than the run on its least prime, step for step, product
    /// for product and gcd for gcd, and searches back at most 128 steps. Random odd composites
    /// below `2^44` (products of two or three random odd numbers) and products of two primes
    /// near `2^32`.
    #[test]
    fn a_run_stops_no_later_than_on_its_least_prime() {
        let (mut rng, _) = crate::seed::Rng::fresh("a_run_stops_no_later_than_on_its_least_prime");
        let mut odd = |bits: u32| (rng.next_u64() >> (64 - bits)) | 1;
        let mut ns: Vec<u64> = (0..2000).map(|_| odd(22) * odd(22)).collect();
        ns.extend((0..2000).map(|_| odd(14) * odd(15) * odd(15)));
        ns.extend([
            4_294_967_291u64 * 4_294_967_279,
            4_294_967_291 * 4_294_967_291,
            25,
        ]);
        for n in ns {
            if n < 9 || is_prime(n) {
                continue;
            }
            let p = factor(n)[0].0;
            let (on_n, on_p) = (rho(&Montgomery::new(n)), rho(&Montgomery::new(p)));
            let (a, b) = (on_n.batches, on_p.batches);
            assert!(
                a.steps <= b.steps && a.products <= b.products && a.gcds <= b.gcds,
                "{n} = {p} * ...: {a:?} on n, {b:?} on p"
            );
            assert!(on_n.back <= 128, "{n}");
            assert!(on_n.g > 1 && n.is_multiple_of(on_n.g), "{n}");
        }
    }

    /// Lehman's search splits every odd composite below `2^16` that trial division to the cube
    /// root leaves, into a proper factor; and `lehman` splits every odd composite below `2^16`,
    /// squares of primes and products of two primes near `2^22` and `2^32`.
    #[test]
    fn lehman_splits_every_odd_composite() {
        let inputs = lehman_inputs();
        assert!(inputs.contains(&25) && inputs.contains(&(251 * 257)));
        for n in inputs {
            let mut cost = LehmanCost::default();
            let g = lehman_search(n, crate::cbrt_floor(n), &mut cost);
            assert!(
                g.is_some_and(|g| g > 1 && g < n && n.is_multiple_of(g)),
                "{n}: {g:?}"
            );
        }
        let mut wide = vec![
            4_194_301u64 * 4_194_287,
            4_194_301 * 4_194_301,
            4_294_967_291 * 4_294_967_279,
            4_294_967_291 * 4_294_967_291,
            // Unbalanced: least prime just above the cube root.
            26_017 * 676_212_791,
        ];
        wide.extend((9..1u64 << 16).step_by(2).filter(|&n| !is_prime(n)));
        for n in wide {
            let (g, _) = lehman(n);
            assert!(g > 1 && g < n && n.is_multiple_of(g), "{n}: {g}");
        }
    }

    /// Lehman's search finds no pair for a prime (the theorem's last sentence): every odd
    /// prime below `2^16`, and the largest primes below `2^44` and `2^64`.
    #[test]
    fn lehman_finds_nothing_in_a_prime() {
        for n in largest_primes()
            .into_iter()
            .chain((3..1u64 << 16).step_by(2).filter(|&n| is_prime(n)))
        {
            let mut cost = LehmanCost::default();
            assert_eq!(
                lehman_search(n, crate::cbrt_floor(n), &mut cost),
                None,
                "{n}"
            );
        }
    }

    /// The largest primes below `2^44` and `2^64`.
    fn largest_primes() -> [u64; 2] {
        let below = |top: u64| (0..).map(|i| top - 2 * i).find(|&c| is_prime(c)).unwrap();
        [below((1 << 44) - 1), below(u64::MAX)]
    }

    /// The number of tries of Lehman's search is at most `2.5 r + 0.75` (proof at
    /// `lehman_search`), checked on primes, where the search runs to its end: every odd prime
    /// below `2^16` and the largest below `2^44` and `2^64`.
    #[test]
    fn lehman_tries_stay_in_the_bound() {
        for n in largest_primes()
            .into_iter()
            .chain((3..1u64 << 16).step_by(2).filter(|&n| is_prime(n)))
        {
            let r = crate::cbrt_floor(n);
            let mut cost = LehmanCost::default();
            lehman_search(n, r, &mut cost);
            // `tries <= 2.5 r + 0.75`, in integers.
            assert!(4 * cost.tries <= 10 * r + 3, "{n}: {cost:?}, r {r}");
        }
    }

    /// `split` on composites where the run with `c = 1` ends with `g = n`, so Lehman's method
    /// gives the factor: 25 (the walk `2, 5, 1, 2, 5, ...` modulo 25 meets itself modulo 5 and 25
    /// at once) and every other such odd composite below `2^16`.
    #[test]
    fn split_falls_back_to_lehman() {
        let failing: Vec<u64> = (9..1u64 << 16)
            .step_by(2)
            .filter(|&n| !is_prime(n) && rho(&Montgomery::new(n)).g == n)
            .collect();
        assert!(failing.contains(&25), "{failing:?}");
        for n in failing {
            let g = split(n);
            assert!(g > 1 && g < n && n.is_multiple_of(g), "{n}: {g}");
        }
    }

    /// Negative control for `lehman_splits_every_odd_composite`: the search with only
    /// `x = isqrt(4 k n)` for each `k` (a range of width 0) misses some of its inputs.
    #[test]
    fn a_lehman_range_of_width_0_is_caught() {
        let narrow = |n: u64| {
            let n128 = u128::from(n);
            (1..=crate::cbrt_floor(n)).find_map(|k| {
                let m = 4 * u128::from(k) * n128;
                let x = m.isqrt();
                let y = crate::sqrt_exact_u128((x * x).checked_sub(m)?)?;
                let g = gcd_u64(((x + y) % n128) as u64, n);
                (g > 1 && g < n).then_some(g)
            })
        };
        assert!(lehman_inputs().into_iter().any(|n| narrow(n).is_none()));
    }

    /// Negative control for `a_run_stops_no_later_than_on_its_least_prime`: the same claim
    /// with a prime that does not divide `n` in place of its least prime is false, and the
    /// comparison the test makes catches it on some input. (The proof at `rho` holds for every
    /// divisor of `n`, so a bound by the largest prime of `n` would be true and is no control.)
    #[test]
    fn a_bound_by_a_prime_not_dividing_n_is_caught() {
        let (mut rng, _) = crate::seed::Rng::fresh("a_bound_by_a_prime_not_dividing_n_is_caught");
        let caught = (0..2000).any(|_| {
            let n = ((rng.next_u64() >> 42) | 1) * ((rng.next_u64() >> 42) | 1);
            let q = (rng.next_u64() >> 44) | 1;
            if n < 9 || is_prime(n) || !is_prime(q) || q < 3 || n.is_multiple_of(q) {
                return false;
            }
            rho(&Montgomery::new(n)).batches.steps > rho(&Montgomery::new(q)).batches.steps
        });
        assert!(caught);
    }

    /// NUM-expect-audit: `split` returns for every composite below `2^16`, and the factors are
    /// the primes trial division finds. 25 and the other composites where the run with `c = 1`
    /// ends without a factor go through Lehman's method (`split_falls_back_to_lehman`).
    #[test]
    fn factors_agree_with_trial_division() {
        for n in 2..1u64 << 16 {
            assert_eq!(factor(n), by_trial(n), "{n}");
            assert_eq!(is_prime(n), by_trial(n) == [(n, 1)], "{n}");
        }
    }

    /// Montgomery products (Montgomery 1985, doi:10.1090/S0025-5718-1985-0777282-X; the full
    /// comment is at struct `Montgomery`), sums, powers and conversions agree with division,
    /// for the odd moduli 3, 5, small primes and composites, ones next to `2^63` and `2^64`
    /// (where the high words of `reduce` are largest and its subtraction borrows most), and
    /// residues at both ends.
    #[test]
    fn montgomery_arithmetic_agrees_with_division() {
        use crate::{mul_mod, pow_mod};
        let (mut rng, _) = crate::seed::Rng::fresh("montgomery_arithmetic_agrees_with_division");
        let mut next = move || rng.next_u64();
        let mut moduli = vec![3, 5, 9, 15, 25, 561, 1_000_003, (1 << 61) - 1];
        moduli.extend([
            (1 << 63) - 1,
            (1 << 63) + 1,
            u64::MAX,
            u64::MAX - 2,
            18_446_744_073_709_551_557,
        ]);
        moduli.extend((0..40).map(|_| next() | 1));
        for n in moduli {
            let m = Montgomery::new(n);
            let back = |h: u64| m.reduce(u128::from(h));
            let mut xs = vec![0, 1, 2, n - 1, n - 2, n / 2, n / 2 + 1];
            xs.extend((0..20).map(|_| next() % n));
            for &a in &xs {
                assert_eq!(back(m.to(a)), a, "{a} mod {n} there and back");
                assert!(m.to(a) < n);
                for &b in &xs {
                    let (ha, hb) = (m.to(a), m.to(b));
                    assert_eq!(back(m.mul(ha, hb)), mul_mod(a, b, n), "{a} * {b} mod {n}");
                    let sum = ((u128::from(a) + u128::from(b)) % u128::from(n)) as u64;
                    assert_eq!(back(m.add(ha, hb)), sum, "{a} + {b} mod {n}");
                }
                for e in [0, 1, 2, n - 1, u64::MAX, next()] {
                    assert_eq!(back(m.pow(m.to(a), e)), pow_mod(a, e, n), "{a}^{e} mod {n}");
                }
            }
            assert_eq!(back(m.one()), 1);
        }
    }

    /// NUM-expect-audit: the 64-bit corner cases: squares and products of the largest primes
    /// below `2^32`, Carmichael numbers and strong pseudoprimes to small bases, prime powers,
    /// `2^64 - 1` and the largest 64-bit prime.
    #[test]
    fn factors_of_wide_numbers_are_their_primes() {
        let (p, q) = (4_294_967_291u64, 4_294_967_279u64);
        let cases: [(u64, &[(u64, u64)]); 9] = [
            (p * p, &[(p, 2)]),
            (p * q, &[(q, 1), (p, 1)]),
            (561, &[(3, 1), (11, 1), (17, 1)]),
            (3_215_031_751, &[(151, 1), (751, 1), (28_351, 1)]),
            (
                3_825_123_056_546_413_051,
                &[(149_491, 1), (747_451, 1), (34_233_211, 1)],
            ),
            (3u64.pow(40), &[(3, 40)]),
            (1_000_003u64.pow(3), &[(1_000_003, 3)]),
            (
                u64::MAX,
                &[
                    (3, 1),
                    (5, 1),
                    (17, 1),
                    (257, 1),
                    (641, 1),
                    (65_537, 1),
                    (6_700_417, 1),
                ],
            ),
            (
                18_446_744_073_709_551_557,
                &[(18_446_744_073_709_551_557, 1)],
            ),
        ];
        for (n, want) in cases {
            assert_eq!(factor(n), want, "{n}");
        }
    }

    /// The Montgomery form needs an odd modulus above 1: an even one has no inverse modulo
    /// `R = 2^64`, and 1 leaves no residue but 0.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "an odd modulus above 1")]
    fn a_montgomery_form_of_an_even_modulus() {
        Montgomery::new(4u64);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "an odd modulus above 1")]
    fn a_montgomery_form_of_one() {
        Montgomery::new(1u64);
    }

    /// Negative control for `montgomery_arithmetic_agrees_with_division`: `reduce` without
    /// adding `n` back on a borrow. For the moduli of that test, small and near `2^64`, it
    /// differs from `reduce` on some products (those that borrow) and agrees on others, so the
    /// test's products see the correction. (For a small `n` every product is below `2^64`,
    /// its high word is 0, and every reduction borrows; near `2^64` some do not.)
    #[test]
    fn a_reduction_without_its_borrow_correction_is_caught() {
        for n in [1_000_003, u64::MAX - 58] {
            let m = Montgomery::new(n);
            let wrong = |t: u128| {
                let q = (t as u64).wrapping_mul(m.n_inv);
                let qn = u128::from(q) * u128::from(m.n);
                ((t >> 64) as u64).wrapping_sub((qn >> 64) as u64)
            };
            let (mut caught, mut agree) = (0, 0);
            // Residues spread over `[0, n)` (Fibonacci hashing), not `1..1000`: near `2^64`,
            // `R mod n` is small (59 for `2^64 - 59`), and so are the held forms of small `a`.
            for i in 1..1000u64 {
                let a = i.wrapping_mul(0x9E37_79B9_7F4A_7C15) % n;
                let t = u128::from(m.to(a)) * u128::from(m.to(a ^ 1));
                if wrong(t) == m.reduce(t) {
                    agree += 1;
                } else {
                    caught += 1;
                }
            }
            assert!(caught > 0, "{n}");
            if n > 1 << 63 {
                assert!(agree > 0, "{n}");
            }
        }
    }

    /// Negative control for `factors_agree_with_trial_division`: the factors grouped in the
    /// order the stack of `factor` leaves them, without the sort, are out of order for some
    /// `n` (the larger cofactor of a split is popped first).
    #[test]
    fn unsorted_factors_are_caught() {
        let unsorted = |n: u64| {
            let mut primes = Vec::new();
            let mut left = vec![n];
            while let Some(m) = left.pop() {
                if m == 1 {
                    continue;
                }
                if m.is_multiple_of(2) {
                    let z = m.trailing_zeros();
                    primes.extend(std::iter::repeat_n(2, z as usize));
                    left.push(m >> z);
                } else if is_prime(m) {
                    primes.push(m);
                } else {
                    let d = split(m);
                    left.push(d);
                    left.push(m / d);
                }
            }
            let mut out: Vec<(u64, u64)> = Vec::new();
            for p in primes {
                match out.last_mut() {
                    Some((q, k)) if *q == p => *k += 1,
                    _ => out.push((p, 1)),
                }
            }
            out
        };
        assert!((2..1u64 << 12).any(|n| unsorted(n) != by_trial(n)));
    }
}
