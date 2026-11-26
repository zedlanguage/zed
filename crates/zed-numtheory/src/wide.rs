//! Primality and factoring of `u128` (FACTOR-u128, PRIME-u128), for HULL-conic.
//!
//! Primality, the method the author approved 2026-11-22: below `2^64`,
//! [`is_prime`](crate::is_prime); from `2^64` to [`PSI_13`], the strong probable-prime test to
//! the 13 prime bases 2 to 41, exact there by
//! Sorenson and Webster's search (cited at [`PSI_13`]); from [`PSI_13`] up, a Pratt certificate
//! (cited in `pratt.rs`), built from the factorization of `p - 1` and checked before the answer
//! is given. No step relies on the generalized Riemann hypothesis or any other unproved claim:
//! the unproved running times of the elliptic curve method (Lenstra's hypothesis, cited in
//! `ecm.rs`) and of rho bear on the time only, since every factor found is a gcd with `n`, and
//! every prime reported is proved prime.
//!
//! Factoring: trial division by the primes below 1000, then for each composite part above `2^64`
//! a perfect-power test, Pollard's rho (Brent's form, [`rho_within`]), a short pass of curves of
//! the elliptic curve method, then the self-initializing quadratic sieve (`siqs.rs`); the steps
//! and their measured costs are at `split_u128`. Parts below `2^64` go to
//! [`factor`](crate::factor()).

use crate::bits::BitLen;
use crate::ecm::{self, Primes};
use crate::factor::{Montgomery, rho_within};
use crate::pratt::{PSI_13, PrattCertificate, PrattFactor, is_prime_below_psi_13, passes_13_bases};
use crate::siqs::siqs;
use crate::word::root_exact_u128;
use crate::{factor, odd_primes_below, sqrt_exact_u128};

/// Whether `n` is prime, proved: the method at the top of this file.
// Complexity tradeoff: below `PSI_13`, at most 13 strong tests, O(log n) products each. From
// `PSI_13` up, a prime costs the factoring of `p - 1` (the comment at `split_u128`; worst case a
// product of two primes near `2^64`, measured in COMPLEXITY.md row PRIME-u128) and the
// certificates of its primes at or above `PSI_13`, recursively: `p - 1` has at most one prime at
// or above `PSI_13` (two would multiply past `PSI_13^2 > 2^163`), at most `(p - 1) / 2`, so the
// chain of certificates has at most `128 - 81 = 47` levels; a composite above `PSI_13` that
// passes the 13 bases costs the same factoring and the bases tried before a witness. The naive
// method, trial division to `sqrt(n)`, costs up to `2^64` divisions; the ECPP and APR-CL tests
// are polynomial in `log n` but far more code, while a certificate costs one factoring of
// `p - 1` (under 1.3 ms for the largest primes below `2^b` measured, seconds at worst). Given up:
// a proved time bound (the factoring's bound is heuristic), against a proved answer.
pub fn is_prime_u128(n: u128) -> bool {
    matches!(decide(n), Primality::Prime(_))
}

/// The prime factorization of `n` as `(prime, exponent)` pairs, primes increasing; empty for 0
/// and 1. Every prime is proved prime (the method of [`is_prime_u128`]).
// Complexity tradeoff: the comment at `split_u128`.
pub fn factor_u128(n: u128) -> Vec<(u128, u64)> {
    factor_certified(n)
        .into_iter()
        .map(|(p, e, _)| (p, e))
        .collect()
}

impl PrattCertificate {
    /// A certificate that `p` is prime, or `None` when `p` is not prime. Check it with
    /// [`PrattCertificate::check`]; building it does not check it.
    pub fn build(p: u128) -> Option<PrattCertificate> {
        if p == 2 {
            return Some(PrattCertificate {
                p,
                generator: 1,
                factors: Vec::new(),
            });
        }
        let probable = if p < PSI_13 {
            is_prime_below_psi_13(p)
        } else {
            p % 2 == 1 && passes_13_bases(p)
        };
        if probable { certify(p) } else { None }
    }
}

/// [`decide`]'s answer: a prime at or above `PSI_13` comes with its certificate.
enum Primality {
    Composite,
    Prime(Option<PrattCertificate>),
}

fn decide(n: u128) -> Primality {
    if n < PSI_13 {
        return if is_prime_below_psi_13(n) {
            Primality::Prime(None)
        } else {
            Primality::Composite
        };
    }
    if n % 2 == 0 || !passes_13_bases(n) {
        return Primality::Composite;
    }
    match certify(n) {
        Some(c) => Primality::Prime(Some(c)),
        None => Primality::Composite,
    }
}

/// For an odd `p >= 3`: a checked certificate when `p` is prime, `None` when it is not. The
/// generator is the least `g >= 2` of order `p - 1`; each `g` tried is first a base of the strong
/// test, so a composite stops at its first witness. This ends: a prime has a generator below it
/// (Pratt, "only if"), and a composite `n` has none (`phi(n) < n - 1`) but has a witness below it,
/// at least `3/4` of the bases (Rabin 1980, Theorem 1, cited in `factor.rs`), and both are reached
/// in order. How far it goes is not bounded here without the generalized Riemann hypothesis
/// (Bach's bound `2 log^2 n` assumes it), so no bound is relied on; measured, the least
/// generator of the primes in the tests is below 100.
fn certify(p: u128) -> Option<PrattCertificate> {
    let factors: Vec<PrattFactor> = factor_certified(p - 1)
        .into_iter()
        .map(|(q, e, proof)| PrattFactor {
            q,
            exponent: e as u32,
            proof,
        })
        .collect();
    let m = Montgomery::new(p);
    let one = m.one();
    for g in 2u64.. {
        if !m.strong_probable_prime(&[g]) {
            return None;
        }
        let gm = m.to(u128::from(g));
        if factors.iter().all(|f| m.pow(gm, (p - 1) / f.q) != one) {
            let c = PrattCertificate {
                p,
                generator: u128::from(g),
                factors,
            };
            // Built from proved parts, so a refusal here is a bug of this file.
            debug_assert_eq!(c.check(), Ok(()));
            return Some(c);
        }
    }
    unreachable!("a generator or a witness below 2^64")
}

/// The primes of trial division in [`factor_certified`]: below 1000.
const TRIAL: u64 = 1000;

/// [`factor_u128`], with the certificate of each prime at or above `PSI_13`, so that a
/// certificate of `p` reuses those of the primes of `p - 1` found while factoring it.
fn factor_certified(n: u128) -> Vec<(u128, u64, Option<PrattCertificate>)> {
    let mut found: Vec<(u128, Option<PrattCertificate>)> = Vec::new();
    let push_small = |found: &mut Vec<(u128, Option<PrattCertificate>)>, m: u64| {
        for (p, e) in factor(m) {
            found.extend(std::iter::repeat_n((u128::from(p), None), e as usize));
        }
    };
    if let Ok(small) = u64::try_from(n) {
        push_small(&mut found, small);
    } else {
        let mut m = n;
        let z = m.trailing_zeros();
        found.extend(std::iter::repeat_n((2, None), z as usize));
        m >>= z;
        let sieve = odd_primes_below(TRIAL);
        for p in (3..TRIAL).step_by(2).filter(|&p| sieve[(p / 2) as usize]) {
            let p = u128::from(p);
            while m.is_multiple_of(p) {
                found.push((p, None));
                m /= p;
            }
        }
        let mut left = vec![m];
        while let Some(m) = left.pop() {
            if let Ok(small) = u64::try_from(m) {
                push_small(&mut found, small);
                continue;
            }
            if let Some((_, c)) = found.iter().find(|(q, _)| *q == m) {
                let c = c.clone();
                found.push((m, c));
                continue;
            }
            match decide(m) {
                Primality::Prime(c) => found.push((m, c)),
                Primality::Composite => {
                    let d = split_u128(m);
                    left.push(d);
                    left.push(m / d);
                }
            }
        }
    }
    found.sort_by_key(|(p, _)| *p);
    let mut out: Vec<(u128, u64, Option<PrattCertificate>)> = Vec::new();
    for (p, c) in found {
        match out.last_mut() {
            Some((q, k, _)) if *q == p => *k += 1,
            _ => out.push((p, 1, c)),
        }
    }
    out
}

/// The steps of rho before the elliptic curve method: about the products of six curves of
/// `b1 =` [`SHORT_B1`] (measured 2026-11-22: 1.7 ms for `2^16` steps at 128 bits, 0.27 ms a curve).
const RHO_STEPS: u64 = 1 << 16;

/// The stage-1 bound of the short pass of curves between rho and SIQS, each with `b2 = 100 b1`.
/// Measured 2026-11-22 on products of a prime of `f` bits and primes making 128 bits, 12 each,
/// the curves until the first split at `b1 = 1000`, median and most: 1 and 5 at `f = 32`, 1 and 6
/// at 36, 1 and 2 at 40, 1 and 1 at 44 and 48; at `b1 = 500` the most were 11 and 4 at 32 and 36,
/// at `b1 = 2000` 2 and 2 at twice the cost a curve (0.61 ms against 0.27 ms).
const SHORT_B1: u64 = 1000;

/// The curves of the short pass for `n` of `bits` bits: `(bits - 64)^2 / 200`, 0 at 64 bits, 5
/// at 96, 11 at 112, 20 at 128, so the pass costs at most about a fifth of SIQS's mean at that
/// size (measured 2026-11-22: SIQS means 7.3, 17.5 and 55 ms at 96, 112 and 128 bits, against
/// 0.27 ms a curve). A prime of `n` of 36 to 48 bits is then found by curves in a few tenths of
/// a millisecond each instead of a full SIQS run.
fn short_curves(bits: u32) -> u32 {
    (bits.saturating_sub(64)).pow(2) / 200
}

/// The stage-1 bound of the curves after SIQS gives up, which it does only on a prime power the
/// root tests at [`split_u128`] missed (none, by their proof there). Measured 2026-11-22 on 64
/// products of two primes in `[2^63, 2^64)` (seed 11), the curves until the first split, mean and
/// most: 140 and 820 at `b1 = 3000`, 61 and 235 at 5000, 41 and 152 at 8000, 28 and 135 at 11000.
/// A curve costs about `b1` times a constant (both stages), so the mean costs `b1 * curves` are
/// 421k, 304k, 325k and 309k: flat from 5000 to 11000.
const LAST_B1: u64 = 11000;

/// The odd primes `k` for which [`split_u128`] tests whether `n` is a `k`-th power.
const ROOTS: [u32; 4] = [3, 5, 7, 11];

/// A factor of the odd composite `n >= 2^64` above 1 and below `n`, with no prime below
/// [`TRIAL`].
///
/// The steps: a root when `n` is a perfect power; rho; a short pass of curves of the elliptic
/// curve method ([`short_curves`]); then SIQS (`siqs.rs`), which splits any `n` that is not a
/// prime power. A perfect power `n = m^j`, `j >= 2`, is a square or a `q`-th power for an odd
/// prime `q` dividing `j`, as `n = (m^(j/q))^q`; and `m >= 1009` (no prime below 1000), so
/// `1009^q <= n < 2^128` gives `q <= 128 / log2(1009) < 12.9`, so `q` is one of [`ROOTS`]. So a
/// prime power reaching SIQS is a prime, which the caller excludes.
// Complexity tradeoff: rho costs about `sqrt(p)` steps for the least prime `p` of `n` (Pollard's
// heuristic, unproved), so it is cut off after `RHO_STEPS`, enough for `p` up to about `2^32`;
// the curves cost `L(p)^(sqrt 2 + o(1))` products in expectation by Lenstra's conjecture
// (unproved), cheap for `p` up to about `2^48` (the measurement at `SHORT_B1`). SIQS costs
// `L(n)^(1 + o(1))` (Pomerance's heuristic, unproved), set by the size of `n` alone, so it takes
// the case the curves are worst at: two primes near `2^64`, where the curves alone took a mean
// of 0.6 s and up to 2.3 s on 48 inputs and SIQS takes about 55 ms (COMPLEXITY.md rows
// FACTOR-u128 and FACTOR-u128-tail). Rho alone, the naive method here, would take about `2^32`
// steps on that case. Given up: a proved bound (none of the three methods has one); the answer
// is exact, as every factor is a gcd with `n` or a root checked by powering.
fn split_u128(n: u128) -> u128 {
    if let Some(r) = sqrt_exact_u128(n) {
        return r;
    }
    if let Some(r) = ROOTS.iter().find_map(|&k| root_exact_u128(n, k)) {
        return r;
    }
    let mont = Montgomery::new(n);
    let g = rho_within(&mont, RHO_STEPS).g;
    if g != 1 && g != n {
        return g;
    }
    let primes = Primes::up_to(LAST_B1);
    let short = short_curves(n.bit_len());
    for sigma in 6..6 + u64::from(short) {
        if let Some(d) = ecm::curve(&mont, sigma, SHORT_B1, 100 * SHORT_B1, &primes) {
            return d;
        }
    }
    if let Some(d) = siqs(n) {
        return d;
    }
    for sigma in 6 + u64::from(short).. {
        if let Some(d) = ecm::curve(&mont, sigma, LAST_B1, 100 * LAST_B1, &primes) {
            return d;
        }
    }
    unreachable!("the curves repeat without end")
}

#[cfg(test)]
mod tests;
