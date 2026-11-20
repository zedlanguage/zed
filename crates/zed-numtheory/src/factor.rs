//! The prime factors of a 64-bit integer: Miller-Rabin with the bases that decide every
//! 64-bit number, and Pollard's rho in Brent's form to split a composite.
//!
//! Sources: G. L. Miller, "Riemann's hypothesis and tests for primality", J. Comput. Syst. Sci.
//! 13(3):300-317, 1976, doi:10.1016/S0022-0000(76)80043-8, and M. O. Rabin, "Probabilistic
//! algorithm for testing primality", J. Number Theory 12(1):128-138, 1980,
//! doi:10.1016/0022-314X(80)90084-0, for the strong-probable-prime test of [`is_prime`] (the
//! bases are cited there); J. M. Pollard, "A Monte Carlo method for factorization", BIT
//! 15(3):331-334, 1975, doi:10.1007/BF01933667, and R. P. Brent, BIT 20, 1980 (cited at
//! `split`), for the rho walk; P. L. Montgomery, 1985 (cited at `Montgomery`), for the
//! products. Checked 2026-11-20: the four DOIs on Crossref; Miller, Rabin and Pollard not read,
//! from memory; Brent read.

/// The prime factors of `n` with their multiplicities, in increasing order of prime; empty for
/// `n <= 1`.
// Complexity tradeoff: trial division is O(sqrt n) divisions, 2^32 for a 64-bit prime product;
// Pollard's rho finds a factor `p` in O(sqrt p) = O(n^(1/4)) expected products, and
// Miller-Rabin tells a prime in O(log n) products.
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

use crate::{gcd_u64, inverse_mod_2_64};

/// Products modulo an odd `n > 1` in Montgomery form (P. L. Montgomery, "Modular multiplication
/// without trial division", Math. Comp. 44(170):519-521, 1985,
/// doi:10.1090/S0025-5718-1985-0777282-X): a residue `x` is held as `x R mod n`, for
/// `R = 2^64`, and the product of two held residues `a R` and `b R` is `a b R mod n`, found
/// with three multiplications and no division. The paper's reduction, as usually stated, is
/// `m = (T mod R) N' mod R` with `N' = -N^-1 mod R`, then `t = (T + m N) / R`, less `N` once if
/// `t >= N`. Departure: [`Montgomery::reduce`] uses `+N^-1` and subtracts, `(T - m N) / R`,
/// adding `N` back on a borrow, so no sum can pass `2^128` and `n` may be any odd 64-bit
/// number. Checked 2026-11-20: the DOI on Crossref; the paper not read (the publisher's site
/// refused the download), so the statement above is from memory. Nothing here rests on it:
/// `montgomery_arithmetic_agrees_with_division` checks every operation against plain division,
/// on moduli up to `2^64 - 1`.
// Complexity tradeoff: `mul_mod` divides a 128-bit product by `n`, a call of the 128-bit
// division routine; the form here costs one division per modulus (for `R^2 mod n`) and then
// three word multiplications per product. Measured by `examples/timing.rs` (COMPLEXITY.md row
// DRY-number-theory). Its residues are in `[0, n)`, so equal residues are equal words.
struct Montgomery {
    n: u64,
    /// `n^-1 mod R`.
    n_inv: u64,
    /// `R^2 mod n`, which [`Montgomery::to`] multiplies by.
    r2: u64,
}

impl Montgomery {
    fn new(n: u64) -> Montgomery {
        debug_assert!(n % 2 == 1 && n > 1, "an odd modulus above 1");
        // `R^2 mod n = 2^128 mod n = ((2^128 - 1) mod n + 1) mod n`.
        let r2 = (u128::MAX % u128::from(n) + 1) % u128::from(n);
        Montgomery {
            n,
            n_inv: inverse_mod_2_64(n),
            // Exact: `r2 < n`, a `u64`.
            r2: r2 as u64,
        }
    }

    /// `t R^-1 mod n`, in `[0, n)`, for `t < n R`.
    fn reduce(&self, t: u128) -> u64 {
        // `m = t n^-1 mod R` makes `m n = t mod R`, so the low words of `t` and `m n` are equal
        // and `(t - m n) / R = hi(t) - hi(m n)` exactly, `t R^-1` modulo `n`. Both high words
        // are below `n` (`t < n R` and `m n < R n`), so the difference is in `(-n, n)`: a
        // borrow means it is negative, and adding `n` (wrapping back past `2^64`) gives the
        // residue in `[0, n)`. This subtracting form needs no `n < 2^63`, unlike the adding one.
        let m = (t as u64).wrapping_mul(self.n_inv);
        let mn = u128::from(m) * u128::from(self.n);
        let (d, borrow) = ((t >> 64) as u64).overflowing_sub((mn >> 64) as u64);
        if borrow { d.wrapping_add(self.n) } else { d }
    }

    /// The product of two held residues, each below `n` (so `a b < n^2 < n R`).
    fn mul(&self, a: u64, b: u64) -> u64 {
        self.reduce(u128::from(a) * u128::from(b))
    }

    /// The sum of two held residues, each below `n`.
    fn add(&self, a: u64, b: u64) -> u64 {
        let (s, carry) = a.overflowing_add(b);
        if carry || s >= self.n {
            s.wrapping_sub(self.n)
        } else {
            s
        }
    }

    /// `x R mod n`, the held form of `x`.
    fn to(&self, x: u64) -> u64 {
        self.mul(x % self.n, self.r2)
    }

    /// `R mod n`, the held form of 1.
    fn one(&self) -> u64 {
        self.reduce(u128::from(self.r2))
    }

    /// The held form of `a^e`, for `a` held, by squaring: O(log e) products.
    fn pow(&self, mut a: u64, mut e: u64) -> u64 {
        let mut r = self.one();
        while e > 0 {
            if e & 1 == 1 {
                r = self.mul(r, a);
            }
            a = self.mul(a, a);
            e >>= 1;
        }
        r
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
    // doi:10.1090/s0025-5718-1980-0572872-7). Citation checked 2026-11-20: Crossref gives that
    // title, authors, volume and pages for the DOI. The paper's text was not read: it is
    // paywalled, and the values were first written from memory. They do not rest on the paper:
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
    let mont = Montgomery::new(n);
    let (one, minus_one) = (mont.one(), n - mont.one());
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    'bases: for &a in &BASES[..k] {
        let mut x = mont.pow(mont.to(a), d);
        if x == one || x == minus_one {
            continue;
        }
        for _ in 1..s {
            x = mont.mul(x, x);
            if x == minus_one {
                continue 'bases;
            }
        }
        return false;
    }
    true
}

/// A factor of the odd composite `n` other than 1 and `n`.
fn split(n: u64) -> u64 {
    // Brent's cycle search on `x^2 + c` (R. P. Brent, "An improved Monte Carlo factorization
    // algorithm", BIT 20(2):176-184, 1980, doi:10.1007/BF01933190), with a new `c` when a cycle
    // closes without a factor. The loop below is the paper's final algorithm of section 7,
    // with its names: "repeat x := y; for i := 1 to r do y := f(y); k := 0; repeat ys := y; for
    // i := 1 to min(m, r - k) do begin y := f(y); q := q × |x - y| mod N end; G := GCD(q, N);
    // k := k + m until (k > r) or (G > 1); r := 2 × r until G > 1", then, if `G = N`, "repeat
    // ys := f(ys); G := GCD(|x - ys|, N) until G > 1". Departures: the paper's tests took
    // `x0 = 0`, `f(x) = x^2 + 3` and `m = 1`; here `x0 = 2`, `c` from 1 and `m = 128`; the inner
    // loop stops at `k >= r`, which skips only the paper's last batch of `min(m, 0) = 0` steps;
    // and where the paper stops on "failure" (`G = N` again) the next `c` is tried. Checked
    // 2026-11-20: the DOI on Crossref and the algorithm read in the paper (the author's scan).
    // `factors_agree_with_trial_division` and `factors_of_wide_numbers_are_their_primes` check
    // the factors; they cannot tell this walk from a slower correct one. The start `x = 2` and
    // the first `c = 1` are the usual choices; any start works, and the proof below shows that
    // `c` running up from 1 always ends. The differences are multiplied in batches of 128 and
    // one gcd is taken per batch, so the O(log n) gcd costs 1/128 of a product per
    // step; a batch that overshoots (`g = n`) is searched again one step at a time from `ys`.
    // Any batch size is exact; a larger one saves gcds and costs more steps when a batch
    // overshoots.
    //
    // The walk is in Montgomery form: it holds `x R` for each `x` of the walk above, since
    // `(x R)^2 R^-1 + c R = (x^2 + c) R`. A difference of held values is the difference of the
    // values times `R`, and each product into `q` adds a factor `R^-1`; `R` is a unit modulo the
    // odd `n`, so every gcd with `n` below, and so the proof at the end, is as for the plain walk.
    let mont = Montgomery::new(n);
    let start = mont.to(2);
    for c in 1u64.. {
        let held_c = mont.to(c);
        let f = |x: u64| mont.add(mont.mul(x, x), held_c);
        let (mut x, mut y, mut g, mut r) = (start, start, 1u64, 1u64);
        // Any unit modulo `n` below it: the products only need their gcd with `n`.
        let mut q = 1u64;
        let mut ys = y;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                for _ in 0..128.min(r - k) {
                    y = f(y);
                    q = mont.mul(q, x.abs_diff(y));
                }
                g = gcd_u64(q, n);
                k += 128;
            }
            r *= 2;
        }
        if g == n {
            loop {
                ys = f(ys);
                g = gcd_u64(x.abs_diff(ys), n);
                if g > 1 {
                    break;
                }
            }
        }
        if g != n {
            return g;
        }
    }
    // Unreachable: each `c` ends (once `y` is in the cycle and `r` past its length, a
    // difference is 0, so `g = n`; the search back from `ys` then meets the difference of that
    // batch that shares a factor with `n`), and some `c` returns. The first comparison is of
    // `x = 2` with `f(f(2)) = 2 + (c + 2)(c + 7) mod n`, so it gives `g = gcd((c + 2)(c + 7), n)`.
    // For `p` the least prime factor of `n` (odd, so `p >= 3`) and `c = p - 2 >= 1`, that is
    // `gcd(p (p + 5), n)`: a multiple of `p`, and `n` only if the odd `n / p >= p` divides the
    // even `p + 5`, so `n / p <= (p + 5) / 2` and `p <= 5`, which leaves `n = 25` alone. So
    // every odd composite but 25 is split by `c = p - 2` at the latest, and 25 is split by a
    // smaller `c` (`factors_agree_with_trial_division`).
    unreachable!("some c splits a composite")
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

    /// NUM-expect-audit: `split` returns for every composite below `2^16`, 25 among them (the
    /// one odd composite its proof leaves to this test), and the factors are the primes trial
    /// division finds.
    #[test]
    fn factors_agree_with_trial_division() {
        for n in 2..1u64 << 16 {
            assert_eq!(factor(n), by_trial(n), "{n}");
            assert_eq!(is_prime(n), by_trial(n) == [(n, 1)], "{n}");
        }
    }

    /// Montgomery products, sums, powers and conversions agree with division, for the odd
    /// moduli 3, 5, small primes and composites, ones next to `2^63` and `2^64` (where the
    /// high words of `reduce` are largest and its subtraction borrows most), and residues at
    /// both ends.
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
}
