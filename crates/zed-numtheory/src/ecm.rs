//! Lenstra's elliptic curve method of factoring, on Montgomery's curves with `x`-only arithmetic,
//! for odd moduli up to `2^128 - 1` (FACTOR-u128). `factor_u128` runs it after Pollard's rho, for
//! the products of two primes near `2^64`, where rho needs about `2^32` steps.
//!
//! Sources, each read 2026-11-21:
//! - H. W. Lenstra, Jr., "Factoring integers with elliptic curves", Annals of Mathematics
//!   126(3):649-673, 1987, doi:10.2307/1971363. Abstract, p. 649: "It is conjectured that the
//!   algorithm determines a non-trivial divisor of a composite number n in expected time at most
//!   K(p)(log n)^2, where p is the least prime dividing n and K is a function for which log K(x)
//!   = sqrt((2 + o(1)) log x log log x) for x -> oo." The running time rests on an unproved
//!   hypothesis, p. 651: "The unproved assumption on which the analysis of the elliptic curve
//!   method is based only concerns the distribution of integers built up from small prime
//!   factors. In particular, it does not refer to elliptic curves." The hypothesis bears only on
//!   the time: a factor this code returns divides `n` (it is a gcd with `n`), so no answer rests
//!   on it, and none rests on the generalized Riemann hypothesis.
//! - P. L. Montgomery, "Speeding the Pollard and elliptic curve methods of factorization",
//!   Math. Comp. 48(177):243-264, 1987, doi:10.1090/S0025-5718-1987-0866113-7 (the AMS scan, as
//!   OpenAlex caches it). p. 260: the curve "By^2 = x^3 + Ax^2 + x", which "requires no
//!   inversions during Step 1". p. 261, with `(X_n : Z_n)` the `x` of `nP`: "X_{m+n} <-
//!   Z_{m-n}[(X_m - Z_m)(X_n + Z_n) + (X_m + Z_m)(X_n - Z_n)]^2, Z_{m+n} <- X_{m-n}[(X_m -
//!   Z_m)(X_n + Z_n) - (X_m + Z_m)(X_n - Z_n)]^2, and 4 X_n Z_n = (X_n + Z_n)^2 - (X_n - Z_n)^2,
//!   X_{2n} <- (X_n + Z_n)^2 (X_n - Z_n)^2, Z_{2n} <- (4 X_n Z_n)((X_n - Z_n)^2 + ((A + 2)/4)(4
//!   X_n Z_n))"; "The addition formula is valid everywhere if we allow GCD(X_n, Z_n, N) to
//!   exceed 1. Once that condition occurs, it will persist, so we can periodically test GCD(Z_n,
//!   N)."
//!   And: "Using the binary method, we can compute nP from P with 11 log_2 n multiplications",
//!   the ladder of [`Curve::mul`]. Stage 2 is the baby-step giant-step continuation of his sec.
//!   4.1, which p. 250 says applies to the elliptic curve method: "The methods of Subsection 4.1
//!   are applicable if we set f(n) = x_n mod N, where nP' = (x_n, y_n)."
//! - P. Zimmermann and B. Dodson, "20 years of ECM", ANTS VII, LNCS 4076, pp. 525-542, 2006,
//!   doi:10.1007/11792086_37 (read in the INRIA report, inria-00070192v2, p. 4): "Choose a random
//!   integer sigma > 5 [...] Then compute u = sigma^2 - 5, v = 4 sigma, x_0 = u^3 mod n, z_0 =
//!   v^3 mod n, a = (v - u)^3 (3u + v)/(4u^3 v) - 2 mod n." So `(a + 2) / 4 = (v - u)^3 (3u + v)
//!   / (16 u^3 v)`, which [`Curve::suyama`] keeps as a fraction `num / den`: the doubling
//!   multiplies `X` and `Z` through by `den`, which leaves the point `(X : Z)` the same and needs
//!   no inverse.

use crate::factor::{Montgomery, Word};
use crate::odd_primes_below;

/// A point `(X : Z)` of the curve, `x = X / Z`, both in Montgomery form.
#[derive(Clone, Copy)]
struct Point {
    x: u128,
    z: u128,
}

/// The curve `B y^2 = x^3 + A x^2 + x` modulo `n`, with `(A + 2) / 4 = num / den`.
struct Curve<'a> {
    m: &'a Montgomery<u128>,
    num: u128,
    den: u128,
}

impl<'a> Curve<'a> {
    /// Suyama's curve for `sigma > 5` and its point `(u^3 : v^3)`, or a factor of `n` above 1
    /// found on the way (when `n` shares a prime with `u`, `v`, `3u + v` or `v - u`, the
    /// inverse the paper takes does not exist).
    fn suyama(m: &'a Montgomery<u128>, sigma: u64) -> Result<(Curve<'a>, Point), u128> {
        let s = m.to(u128::from(sigma));
        let u = m.sub(m.mul(s, s), m.to(5));
        let v = m.add(m.add(s, s), m.add(s, s));
        let u3 = m.mul(m.mul(u, u), u);
        let v3 = m.mul(m.mul(v, v), v);
        let vu = m.sub(v, u);
        let three_u = m.add(m.add(u, u), u);
        let num = m.mul(m.mul(m.mul(vu, vu), vu), m.add(three_u, v));
        let den = m.mul(m.mul(m.to(16), u3), v);
        // A shared prime of `n` with `den v^3 num` (the `x` of the point times the inverse the
        // paper takes) shows as a gcd above 1; `num = 0` modulo a prime would make the curve
        // singular there.
        // (A held residue is `x R mod n`, and `R` is prime to `n`, so its gcd with `n` is `x`'s.)
        let g = m.mul(m.mul(den, v3), num).gcd(m.n);
        if g != 1 {
            return Err(g);
        }
        Ok((Curve { m, num, den }, Point { x: u3, z: v3 }))
    }

    /// `2 P`: five products, with the `den` scaling one more (p. 261, multiplied through).
    fn double(&self, p: Point) -> Point {
        let m = self.m;
        let s = m.mul(m.add(p.x, p.z), m.add(p.x, p.z));
        let d = m.mul(m.sub(p.x, p.z), m.sub(p.x, p.z));
        let t = m.sub(s, d);
        Point {
            x: m.mul(m.mul(self.den, s), d),
            z: m.mul(t, m.add(m.mul(self.den, d), m.mul(self.num, t))),
        }
    }

    /// `P + Q`, given `P - Q`: six products (p. 261).
    fn add(&self, p: Point, q: Point, diff: Point) -> Point {
        let m = self.m;
        let u = m.mul(m.sub(p.x, p.z), m.add(q.x, q.z));
        let v = m.mul(m.add(p.x, p.z), m.sub(q.x, q.z));
        let (sum, dif) = (m.add(u, v), m.sub(u, v));
        Point {
            x: m.mul(diff.z, m.mul(sum, sum)),
            z: m.mul(diff.x, m.mul(dif, dif)),
        }
    }

    /// `k P`, for `k >= 1`, by the ladder that keeps `(j P, (j + 1) P)` (p. 261): about
    /// `11 log2 k` products.
    fn mul(&self, p: Point, k: u64) -> Point {
        let (mut r0, mut r1) = (p, self.double(p));
        for bit in (0..63 - k.leading_zeros()).rev() {
            if k >> bit & 1 == 1 {
                r0 = self.add(r1, r0, p);
                r1 = self.double(r1);
            } else {
                r1 = self.add(r0, r1, p);
                r0 = self.double(r0);
            }
        }
        r0
    }
}

/// The primes up to the largest stage-1 bound, for stage 1 (stage 2 needs no table: the comment
/// at [`curve`]).
pub(crate) struct Primes {
    /// `is_odd_prime[i]` is whether `2 i + 1` is prime ([`odd_primes_below`]).
    is_odd_prime: Vec<bool>,
}

impl Primes {
    pub(crate) fn up_to(b1: u64) -> Primes {
        Primes {
            is_odd_prime: odd_primes_below(b1 + 1),
        }
    }
}

/// The giant step of stage 2: `2 * 3 * 5 * 7`, so the baby steps are the 24 numbers `j < 105`
/// prime to 210 and every prime above 7 is `k 210 ± j`.
const GIANT: u64 = 210;

/// A factor of `n` above 1 and below `n` from one curve, `sigma` its Suyama parameter, with
/// stage-1 bound `b1` and stage-2 bound `b2` (`b1 < b2`, `primes` covering `b1`), or `None` when
/// the curve finds none (or finds all of `n` at once).
// Complexity tradeoff: stage 1 costs about `11 log2 b1` products per prime power below `b1`,
// about `11 * 1.44 b1` products in all (the ladder, p. 261; the product of the prime powers has
// about `1.44 b1` bits). Stage 2 tests each `k 210 ± j` up to `b2` with two products per pair
// (24 pairs per 210 numbers; the baby points share one denominator), about `0.23 b2` products,
// so `b2 = 100 b1` costs about 1.4 times stage 1 and covers primes 100 times larger. Measured at
// `b1 = 8000`: `b2 = 50 b1` took 50.0 curves in the mean against 40.6 at `100 b1`, at 0.64 the
// time per curve, so 0.79 the time; not yet measured at the bounds of `SCHEDULE` (plan row
// FACTOR-u128-tail). The naive stage 2, one ladder per prime between `b1` and
// `b2`, costs `11 log2 p` products per prime; Montgomery's FFT continuation (thesis, 1992)
// would cost `O(sqrt(b2) log b2)` products, a gain that pays off only at larger `b2` than a
// 64-bit factor needs. Given up: the tests of pairs that are not primes (about two thirds), which
// keep stage 2 free of a table of primes.
pub(crate) fn curve(
    m: &Montgomery<u128>,
    sigma: u64,
    b1: u64,
    b2: u64,
    primes: &Primes,
) -> Option<u128> {
    let (curve, mut q) = match Curve::suyama(m, sigma) {
        Ok(c) => c,
        Err(g) => return (g != m.n).then_some(g),
    };
    let n = m.n;
    // Stage 1: `Q = (prod p^e) P` over the prime powers `p^e <= b1` with `p^(e+1) > b1`.
    let mut pk = 2;
    while pk * 2 <= b1 {
        pk *= 2;
    }
    q = curve.mul(q, pk);
    for p in (3..=b1)
        .step_by(2)
        .filter(|&p| primes.is_odd_prime[(p / 2) as usize])
    {
        let mut pk = p;
        while pk * p <= b1 {
            pk *= p;
        }
        q = curve.mul(q, pk);
    }
    let g = q.z.gcd(n);
    if g != 1 {
        return (g != n).then_some(g);
    }
    // Stage 2: `x(k 210 Q) = x(j Q)`, for `j < 105` prime to 210, means `(k 210 ± j) Q` is the
    // point at infinity modulo some prime `p` of `n`, so `p` divides `X_k Z_j - X_j Z_k`; the
    // product of these over all pairs is taken modulo `n`, with one gcd at the end.
    let baby: Vec<u64> = (1..GIANT / 2)
        .step_by(2)
        .filter(|j| j % 3 != 0 && j % 5 != 0 && j % 7 != 0)
        .collect();
    let mut odd = vec![q, curve.double(q)]; // `1 Q` and, for now, `2 Q`.
    let two_q = odd[1];
    odd[1] = curve.add(two_q, q, q); // `3 Q`.
    for i in 2..(GIANT / 4) as usize + 1 {
        // `(2 i + 1) Q = (2 i - 1) Q + 2 Q`, with difference `(2 i - 3) Q`.
        let next = curve.add(odd[i - 1], two_q, odd[i - 2]);
        odd.push(next);
    }
    let baby_points: Vec<Point> = baby.iter().map(|&j| odd[(j / 2) as usize]).collect();
    // All baby steps over one denominator, `Z_c = prod Z_i`, with `X'_j = X_j prod_(i != j) Z_i`
    // (prefix and suffix products, no inverse), so a pair costs `X_k Z_c - X'_j Z_k`: one product
    // and the product into the accumulator, against three with `X_k Z_j - X_j Z_k`. The pair's
    // value is the old one times `prod_(i != j) Z_i`, prime to `n` once `gcd(Z_c, n) = 1`.
    let mut prefix = Vec::with_capacity(baby_points.len() + 1);
    prefix.push(m.one());
    for b in &baby_points {
        prefix.push(m.mul(prefix[prefix.len() - 1], b.z));
    }
    let zc = prefix[baby_points.len()];
    let g = zc.gcd(n);
    if g != 1 {
        return (g != n).then_some(g);
    }
    let mut xs = vec![0; baby_points.len()];
    let mut suffix = m.one();
    for (j, b) in baby_points.iter().enumerate().rev() {
        xs[j] = m.mul(m.mul(b.x, prefix[j]), suffix);
        suffix = m.mul(suffix, b.z);
    }
    let giant = curve.mul(q, GIANT);
    let k0 = (b1 / GIANT).max(1) + 1;
    let (mut prev, mut cur) = (curve.mul(q, (k0 - 1) * GIANT), curve.mul(q, k0 * GIANT));
    let mut acc = m.one();
    let mut k = k0;
    while (k - 1) * GIANT <= b2 {
        let xz = m.mul(cur.x, zc);
        for &x in &xs {
            acc = m.mul(acc, m.sub(xz, m.mul(x, cur.z)));
        }
        let next = curve.add(cur, giant, prev);
        (prev, cur) = (cur, next);
        k += 1;
    }
    let g = acc.gcd(n);
    (g != 1 && g != n).then_some(g)
}
