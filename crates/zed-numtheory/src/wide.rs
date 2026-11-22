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
//! a perfect-square test, Pollard's rho (Brent's form, [`rho_within`]) for about one curve's
//! worth of products, then curves of the elliptic curve method until one splits it. Parts below
//! `2^64` go to [`factor`](crate::factor()).

use crate::ecm::{self, Primes};
use crate::factor::{Montgomery, rho_within};
use crate::pratt::{PSI_13, PrattCertificate, PrattFactor, is_prime_below_psi_13, passes_13_bases};
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

/// The steps of rho before the elliptic curve method: about the products of one curve at the
/// first bound of [`SCHEDULE`] (measured in COMPLEXITY.md row FACTOR-u128).
const RHO_STEPS: u64 = 1 << 16;

/// The curves of the elliptic curve method: `(b1, curves)`, each with `b2 = 100 b1`, then curves
/// of `b1 =` [`LAST_B1`] until one splits `n`. Measured 2026-11-22 on 64 products of two primes
/// in `[2^63, 2^64)` (seed 11), the curves until the first split, mean and most: 140 and 820 at
/// `b1 = 3000`, 61 and 235 at 5000, 41 and 152 at 8000, 28 and 135 at 11000. A curve costs about
/// `b1` times a constant (both stages), so the mean costs `b1 * curves` are 421k, 304k, 325k and
/// 309k: flat from 5000 to 11000. The schedule rises, so the curves of small `b1` find the
/// smaller primes of 80- to 112-bit inputs first, at a small share of the cost of a 64-bit prime.
const SCHEDULE: [(u64, u32); 2] = [(2000, 25), (5000, 60)];
/// The stage-1 bound of the curves after [`SCHEDULE`].
const LAST_B1: u64 = 11000;

/// A factor of the odd composite `n >= 2^64` above 1 and below `n`, with no prime below
/// [`TRIAL`].
// Complexity tradeoff: rho costs about `sqrt(p)` steps for the least prime `p` of `n` (Pollard's
// heuristic, unproved), so it is cut off after `RHO_STEPS`, enough for `p` up to about `2^32`;
// the elliptic curve method then costs `L(p)^(sqrt 2 + o(1))` products in expectation by
// Lenstra's conjecture (unproved), a mean of about 60 curves of `b1 = 5000` for `p` near `2^64`
// (the measurement at `SCHEDULE`). The
// worst case is a product of two primes near `2^64`; measured in COMPLEXITY.md row FACTOR-u128.
// SIQS (Contini 1997) would cost `L(n)^(1 + o(1))`, the same order at `p ~ sqrt(n)`, with a
// smaller constant at 128 bits in published measurements but several times the code (a factor
// base, sieving, and linear algebra over GF(2)); it is not written, pending a measured need.
// Rho alone, the naive method here, would take about `2^32` steps on the worst case. Given up:
// a proved bound (none of the three methods has one); the answer is exact, as every factor is
// a gcd with `n`.
fn split_u128(n: u128) -> u128 {
    if let Some(r) = sqrt_exact_u128(n) {
        return r;
    }
    let mont = Montgomery::new(n);
    let g = rho_within(&mont, RHO_STEPS).g;
    if g != 1 && g != n {
        return g;
    }
    let primes = Primes::up_to(LAST_B1);
    let rows = SCHEDULE
        .iter()
        .flat_map(|&(b1, k)| std::iter::repeat_n(b1, k as usize));
    for (sigma, b1) in (6..).zip(rows.chain(std::iter::repeat(LAST_B1))) {
        if let Some(d) = ecm::curve(&mont, sigma, b1, 100 * b1, &primes) {
            return d;
        }
    }
    unreachable!("the curves repeat without end")
}

#[cfg(test)]
#[path = "wide_tests.rs"]
mod tests;
