//! The self-initializing quadratic sieve (SIQS) for `u128` (FACTOR-u128-tail): a factor of an
//! odd composite `n` in `[2^64, 2^128)` that is not a prime power and has no prime below 1000.
//!
//! The method, as written here:
//! 1. A multiplier `k` (Knuth and Schroeppel's choice, [`multiplier`]) and a factor base: 2, the
//!    odd primes `p` with `kN` a square mod `p`, and the primes of `k`.
//! 2. Polynomials `Q(x) = (a x + b)^2 - kN = a g(x)`, `g(x) = a x^2 + 2 b x + c`, with `a` a
//!    product of `s` primes of the factor base near `sqrt(2 kN) / M`, so that `|g(x)| <= M
//!    sqrt(kN / 2)` on the sieve interval `-M <= x < M`, and `b^2 = kN mod a`, so `c = (b^2 - kN)
//!    / a` is an integer. Each `a` serves `2^(s-1)` values of `b`, switched by a Gray code at the
//!    cost of one addition per prime: the self-initialization.
//! 3. Sieving `log p` at the roots of `g` mod `p` marks the `x` where `g(x)` is likely smooth;
//!    those are divided out exactly. A value left with one prime above the factor base but below
//!    [`Params::large`] times its largest prime is kept as a partial relation, and two partials
//!    with the same large prime multiply into one relation (the large prime variation).
//! 4. Gaussian elimination over GF(2) on the exponent vectors finds products of relations that
//!    are squares: `X = prod (a x + b)`, `Y = sqrt(prod Q(x))`, `X^2 = Y^2 mod n`, and
//!    `gcd(X - Y, n)` splits `n` unless `X = +-Y mod n`.
//!
//! Sources (checked 2026-11-22):
//! - C. Pomerance, "The quadratic sieve factoring algorithm", EUROCRYPT 84, Lecture Notes in
//!   Computer Science 209 (1985), 169-182, DOI 10.1007/3-540-39757-4_17: the method of step 3
//!   and 4 with one polynomial. Checked: Crossref metadata (title, pages); the text was not read
//!   here, and the steps above are written from the standard account, not quoted.
//! - R. D. Silverman, "The multiple polynomial quadratic sieve", Mathematics of Computation 48
//!   (1987), 329-339, DOI 10.1090/S0025-5718-1987-0866119-8: many polynomials `(a x + b)^2 - kN`
//!   with `a` near `sqrt(2 kN) / M`, so that `g` stays below `M sqrt(kN / 2)`. Checked: Crossref
//!   metadata only.
//! - S. Contini, "Factoring integers with the self-initializing quadratic sieve", M.A. thesis,
//!   University of Georgia, 1997: `a = q_1 ... q_s`, `B_l = (a / q_l) gamma_l` with `gamma_l =
//!   t_l (a / q_l)^-1 mod q_l`, `t_l^2 = kN mod q_l`, `b = B_1 + ... + B_s`, and the Gray code
//!   `b_(i+1) = b_i + 2 (-1)^ceil(i / 2^v) B_v` with `2^v || 2 i`, under which every root moves
//!   by `+-2 B_v a^-1 mod p`. From memory: the thesis was not found by the literature search of
//!   this change (`allpapers-search --mode keyword -t "self-initializing quadratic sieve"`,
//!   one unrelated hit), so these formulas are not quoted; each is checked by the code itself
//!   (`debug_assert` that `b^2 = kN mod a` for every `b`) and by the tests in `wide/tests.rs`,
//!   whose relations would fail to divide if a root were wrong.
//! - D. E. Knuth, "The Art of Computer Programming", vol. 2, 3rd ed., section 4.5.4 (the
//!   Knuth-Schroeppel function): choose `k` to maximize `sum f(p, kN) log p - (1/2) log k`. From
//!   memory, not checked; the multiplier bears on the time only, never on the answer.
//!
//! Exactness: every factor returned is `gcd(X - Y, n)` with `1 < gcd < n`, so it divides `n`;
//! the heuristics (smoothness, the multiplier, the parameters) bear on the time only.

use std::collections::HashMap;
use zed_hash::Xorshift64;

use crate::factor::{Montgomery, Word};
use crate::{gcd_u128, mul_mod, odd_primes_below, pow_mod};

/// The parameters of one size of `kN`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Params {
    /// The odd primes of the factor base that are sieved (the primes of `k` and 2 are added).
    pub(crate) primes: usize,
    /// Half the sieve interval: `x` runs over `[-m, m)`.
    pub(crate) m: u32,
    /// A partial relation keeps a large prime below `large` times the largest prime of the base.
    pub(crate) large: u64,
    /// How far below `log2(m sqrt(kN / 2))` a sieve value may be, in units of `log2` of the
    /// largest prime of the base, and still be divided out.
    pub(crate) slack: f64,
}

/// The parameters for `kN` of `bits` bits: [`TABLE`], linear between its rows.
// The rows are tuning, not correctness. Measured 2026-11-22 on 48 products of two 64-bit primes
// (`kN` of 130 to 132 bits), CPU time of the 48 under a machine load of 40 to 60: scaling the
// primes of the row by 0.7, 0.85, 1.2 and 1.4 and the interval by 0.25 to 2 gave 1.5 to 3.9 s
// against 1.8 to 3.1 s for the rows as they are; only the interval doubled (twice the wall time)
// and the primes at 1.4 (3.7 to 4.0 s) were worse past the noise of repeated runs.
pub(crate) fn params(bits: u32) -> Params {
    let bits = f64::from(bits);
    let row = |r: &(f64, f64, f64)| Params {
        primes: r.1 as usize,
        m: r.2 as u32,
        large: LARGE,
        slack: SLACK,
    };
    if bits <= TABLE[0].0 {
        return row(&TABLE[0]);
    }
    for w in TABLE.windows(2) {
        let (lo, hi) = (&w[0], &w[1]);
        if bits <= hi.0 {
            let t = (bits - lo.0) / (hi.0 - lo.0);
            return row(&(bits, lo.1 + t * (hi.1 - lo.1), lo.2 + t * (hi.2 - lo.2)));
        }
    }
    row(&TABLE[TABLE.len() - 1])
}

/// `(bits of kN, odd primes in the factor base, half the sieve interval)`.
const TABLE: [(f64, f64, f64); 4] = [
    (64.0, 80.0, 16384.0),
    (96.0, 180.0, 32768.0),
    (120.0, 360.0, 32768.0),
    (136.0, 600.0, 65536.0),
];
/// [`Params::large`].
const LARGE: u64 = 40;
/// [`Params::slack`].
const SLACK: f64 = 2.0;
/// The odd primes below this are not sieved (their logarithms are small and their strides
/// short); [`SMALL_CREDIT`] stands in for them in the threshold.
const SMALL: u32 = 32;
/// The expected `log2` the unsieved primes 3 to 31 contribute to a value, about `sum 2 log2(p) /
/// (p - 1)` over the primes of the base among them (half the primes), rounded down.
const SMALL_CREDIT: f64 = 3.0;

/// A factor of `n` above 1 and below `n`, for an odd composite `n >= 2^64` that is not a
/// perfect power and has no prime factor below 1000. `None` only when `n` breaks those terms in
/// a way the sieve notices (a prime of the factor base divides `n` is not one: that prime is
/// returned).
// Complexity tradeoff: SIQS costs `L(n)^(1 + o(1))` operations, `L(n) = exp(sqrt(ln n ln ln
// n))`, heuristically (Pomerance 1985; unproved), and the cost depends on the size of `n` only,
// not on its least prime: at 128 bits, measured in COMPLEXITY.md row FACTOR-u128-tail, against
// the elliptic curve method's `L(p)^(sqrt 2 + o(1))`, which is the same order at `p ~ sqrt(n)`
// but has a long tail of unlucky curves (2.3 s at most against a mean of 0.6 s, the row
// FACTOR-u128). The linear algebra is dense Gaussian elimination, O(r^3 / 64) word operations
// for `r` relations (under 700 here, about 5 * 10^6 operations); block Lanczos or Wiedemann
// would be O(r w) for `w` nonzero entries but are worth their code only for far larger bases.
// Given up: a proved time bound (no method of factoring has a practical one).
pub(crate) fn siqs(n: u128) -> Option<u128> {
    debug_assert!(n & 1 == 1 && n >> 64 != 0);
    let k = multiplier(n);
    let kn_f = (k as f64) * (n as f64);
    let bits = kn_f.log2().ceil() as u32;
    let par = params(bits);
    let base = match Base::new(n, k, par.primes) {
        Ok(b) => b,
        Err(p) => return Some(u128::from(p)),
    };
    let mut sieve = Sieve::new(&base, par, kn_f);
    let mont = Montgomery::new(n);
    loop {
        sieve.next_a();
        for i in 0..sieve.polys() {
            sieve.poly(i);
            sieve.sieve();
            sieve.collect();
        }
        if sieve.relations.len() >= base.columns() + EXTRA {
            if let Some(d) = combine(&base, &sieve.relations, &mont) {
                return Some(d);
            }
            // Every dependency gave `X = +-Y`: more relations give new dependencies.
            sieve.wanted += EXTRA;
        }
        if sieve.relations.len() > sieve.wanted + base.columns() * 4 {
            // Far more relations than columns and still no split: `n` is a prime power or
            // prime, which the caller excludes.
            return None;
        }
    }
}

/// Relations beyond the number of columns before the linear algebra: each dependency splits a
/// product of two primes with probability 1/2, so 16 fail together with probability `2^-16`.
const EXTRA: usize = 16;

/// The Knuth-Schroeppel multiplier: the odd squarefree `k < 64` maximizing `f(k) = sum_p
/// g(p, kN) - (1/2) ln k`, where for `p = 2`, `g = 2 ln 2` when `kN = 1 mod 8`, `ln 2` when `kN = 5
/// mod 8`, `(1/2) ln 2` otherwise; for odd `p` dividing `k`, `ln p / p`; for odd `p` with `kN` a
/// nonzero square mod `p`, `2 ln p / (p - 1)`; else 0; over the primes below 1000. `f` is the
/// expected `ln` of the part of a value of `Q` the small primes supply, less the growth of `Q` by
/// `sqrt k` (Knuth, TAOCP vol. 2, 4.5.4; cited at the top of this file, from memory).
fn multiplier(n: u128) -> u64 {
    let odd = odd_primes_below(1000);
    let primes: Vec<u64> = (3..1000u64)
        .step_by(2)
        .filter(|&p| odd[(p / 2) as usize])
        .collect();
    let mut best = (f64::NEG_INFINITY, 1u64);
    for k in (1..64u64).step_by(2) {
        if (3..k).step_by(2).any(|q| k % (q * q) == 0) {
            continue;
        }
        let kn8 = ((n % 8) as u64 * k) % 8;
        let ln2 = std::f64::consts::LN_2;
        let mut f = match kn8 {
            1 => 2.0 * ln2,
            5 => ln2,
            _ => 0.5 * ln2,
        } - 0.5 * (k as f64).ln();
        for &p in &primes {
            let lp = (p as f64).ln();
            let r = mul_mod(k, (n % u128::from(p)) as u64, p);
            if r == 0 {
                f += lp / p as f64;
            } else if pow_mod(r, (p - 1) / 2, p) == 1 {
                f += 2.0 * lp / (p - 1) as f64;
            }
        }
        if f > best.0 {
            best = (f, k);
        }
    }
    best.1
}

/// `sqrt(x) mod p` for an odd prime `p` and a nonzero square `x < p`, by Tonelli and Shanks:
/// write `p - 1 = q 2^e`, `q` odd; with `z` a non-square, `c = z^q` has order `2^e`; `r =
/// x^((q+1)/2)` and `t = x^q` satisfy `r^2 = x t`; while `t != 1`, the least `i` with `t^(2^i) = 1`
/// gives `b = c^(2^(e - i - 1))`, and `r b`, `t b^2` keep `r^2 = x t` while the order of `t`
/// falls. (Standard; e.g. Cohen, "A Course in Computational Algebraic Number Theory",
/// Algorithm 1.5.1, from memory.) Checked by `square_roots_mod_primes_square_back`.
pub(crate) fn sqrt_mod_prime(x: u64, p: u64) -> u64 {
    debug_assert!(x != 0 && x < p && pow_mod(x, (p - 1) / 2, p) == 1);
    let (mut q, mut e) = (p - 1, 0u32);
    while q % 2 == 0 {
        q /= 2;
        e += 1;
    }
    let z = (2..p)
        .find(|&z| pow_mod(z, (p - 1) / 2, p) == p - 1)
        .expect("an odd prime has a non-square below it");
    let mut c = pow_mod(z, q, p);
    let mut r = pow_mod(x, q.div_ceil(2), p);
    let mut t = pow_mod(x, q, p);
    let mut m = e;
    while t != 1 {
        let mut i = 0;
        let mut t2 = t;
        while t2 != 1 {
            t2 = mul_mod(t2, t2, p);
            i += 1;
        }
        let b = pow_mod(c, 1 << (m - i - 1), p);
        r = mul_mod(r, b, p);
        c = mul_mod(b, b, p);
        t = mul_mod(t, c, p);
        m = i;
    }
    r
}

/// `x^-1 mod p` for a prime `p` not dividing `x`: Fermat, `x^(p-2)`.
fn inv_mod_prime(x: u64, p: u64) -> u64 {
    pow_mod(x, p - 2, p)
}

/// The factor base. Column 0 is the sign; column `1 + i` is `primes[i]`: `primes[0] = 2`, then the
/// sieved odd primes (`1..=sieved`), then the primes of `k`, which divide `Q(x)` only where they
/// divide `a x + b` and are not sieved.
struct Base {
    n: u128,
    k: u64,
    /// `kN mod 2^128`: [`Sieve::poly`] needs `kN` only modulo `2^128` (the comment there).
    kn: u128,
    primes: Vec<u32>,
    /// The last index of a sieved prime in `primes`.
    sieved: usize,
    /// `sqrt(kN) mod p` for the sieved primes, indexed as `primes` (0 for the others).
    root: Vec<u32>,
    /// `round(log2 p)` for the sieved primes.
    log: Vec<u8>,
}

impl Base {
    /// The base of `count` sieved odd primes, or `Err(p)` for a prime of the base that divides
    /// `n`.
    fn new(n: u128, k: u64, count: usize) -> Result<Base, u64> {
        let mut primes = vec![2u32];
        let mut root = vec![0u32];
        let mut log = vec![1u8];
        let mut top = 4096u64;
        'grow: loop {
            let odd = odd_primes_below(top);
            primes.truncate(1);
            root.truncate(1);
            log.truncate(1);
            for p in (3..top).step_by(2).filter(|&p| odd[(p / 2) as usize]) {
                let np = (n % u128::from(p)) as u64;
                if np == 0 {
                    return Err(p);
                }
                if k.is_multiple_of(p) {
                    continue;
                }
                let r = mul_mod(k, np, p);
                if pow_mod(r, (p - 1) / 2, p) != 1 {
                    continue;
                }
                primes.push(p as u32);
                root.push(sqrt_mod_prime(r, p) as u32);
                log.push((p as f64).log2().round() as u8);
                if primes.len() > count {
                    break 'grow;
                }
            }
            top *= 2;
        }
        let sieved = primes.len() - 1;
        for q in (3..64u32).step_by(2) {
            if k.is_multiple_of(u64::from(q)) && (2..q).all(|d| q % d != 0) {
                primes.push(q);
                root.push(0);
                log.push(0);
            }
        }
        Ok(Base {
            n,
            k,
            kn: u128::from(k).wrapping_mul(n),
            primes,
            sieved,
            root,
            log,
        })
    }

    fn columns(&self) -> usize {
        1 + self.primes.len()
    }

    fn largest(&self) -> u64 {
        u64::from(self.primes[self.sieved])
    }
}

/// One relation: `prod u^2 = prod Q = large^2 prod_(col) p_col^e mod n`, with the columns in
/// `factors` repeated by their exponents (column 0, the sign, once per negative value).
struct Relation {
    /// The values `a x + b`: one, or two for two partials joined by their large prime.
    u: Vec<i128>,
    factors: Vec<u32>,
    /// The large prime of two joined partials, or 1.
    large: u64,
}

/// The sieve and its state between polynomials.
struct Sieve<'b> {
    base: &'b Base,
    par: Params,
    /// `sqrt(2 kN) / m`, the target size of `a`.
    target: f64,
    /// `log2(m sqrt(kN / 2))` less the slack: values at or above it are divided out.
    threshold: u8,
    /// xorshift64 (zed-hash's, where its source is), fixed seed: the choice of `a` is
    /// reproducible.
    rng: Xorshift64,
    /// The indices in `base.primes` of the primes of the current `a`, and `a` itself.
    a_idx: Vec<usize>,
    a: u128,
    /// `B_l` of the current `a`, and the current `b`.
    big_b: Vec<i128>,
    b: i128,
    /// `2 B_l a^-1 mod p` per `l`, per prime (0 for the primes of `a` and the unsieved ones).
    bainv: Vec<Vec<u32>>,
    /// The two sieve offsets of the roots of `g` mod `p`, in `[0, p)`, per prime.
    soln1: Vec<u32>,
    soln2: Vec<u32>,
    /// `a^-1 mod 2^128`, for `c`.
    a_inv: u128,
    c: i128,
    used_a: std::collections::HashSet<u128>,
    bytes: Vec<u8>,
    relations: Vec<Relation>,
    partials: HashMap<u64, Relation>,
    /// The relations wanted beyond the columns before [`combine`] runs again.
    wanted: usize,
}

impl<'b> Sieve<'b> {
    fn new(base: &'b Base, par: Params, kn_f: f64) -> Sieve<'b> {
        let m = f64::from(par.m);
        let top = (m * (kn_f / 2.0).sqrt()).log2();
        let lp = (base.largest() as f64).log2();
        let threshold = (top - par.slack * lp - SMALL_CREDIT).max(1.0) as u8;
        let p = base.primes.len();
        Sieve {
            base,
            par,
            target: (2.0 * kn_f).sqrt() / m,
            threshold,
            rng: Xorshift64::new(0x9E37_79B9_7F4A_7C15),
            a_idx: Vec::new(),
            a: 1,
            big_b: Vec::new(),
            b: 0,
            bainv: Vec::new(),
            soln1: vec![0; p],
            soln2: vec![0; p],
            a_inv: 1,
            c: 0,
            used_a: std::collections::HashSet::new(),
            bytes: vec![0; 2 * par.m as usize],
            relations: Vec::new(),
            partials: HashMap::new(),
            wanted: EXTRA,
        }
    }

    fn polys(&self) -> usize {
        1 << (self.a_idx.len() - 1)
    }

    /// A new `a` near `target`: `s - 1` random primes of the base near `target^(1/s)`, and the
    /// last the prime of the base nearest `target` over their product; never an `a` used before.
    /// `s` is the least with `target^(1/s) <= ` [`A_PRIME`] or a third of the largest prime.
    fn next_a(&mut self) {
        let base = self.base;
        let ln_t = self.target.ln();
        let cap = (A_PRIME as f64).min(base.largest() as f64 / 3.0).ln();
        let s = ((ln_t / cap).ceil() as usize).max(1);
        let q0 = (ln_t / s as f64).exp();
        // The sieved primes in `[q0 / 2, 2 q0]`, above `SMALL`.
        let lo = base.primes[1..=base.sieved]
            .partition_point(|&p| f64::from(p) < q0 / 2.0)
            .max(base.primes[1..=base.sieved].partition_point(|&p| p < SMALL))
            + 1;
        let hi = base.primes[1..=base.sieved].partition_point(|&p| f64::from(p) <= 2.0 * q0) + 1;
        let (lo, hi) = (
            lo.min(base.sieved),
            hi.clamp(lo.min(base.sieved) + 1, base.sieved + 1),
        );
        loop {
            let mut idx: Vec<usize> = Vec::with_capacity(s);
            let mut prod = 1f64;
            let mut tries = 0;
            while idx.len() + 1 < s && tries < 1000 {
                tries += 1;
                let i = lo + self.rng.below((hi - lo) as u64) as usize;
                if !idx.contains(&i) {
                    idx.push(i);
                    prod *= f64::from(base.primes[i]);
                }
            }
            let want = self.target / prod;
            // The sieved prime nearest `want`, not taken, above `SMALL`.
            let at = base.primes[1..=base.sieved].partition_point(|&p| f64::from(p) < want) + 1;
            let near = [
                at.saturating_sub(1),
                at,
                at + 1,
                at.saturating_sub(2),
                at + 2,
            ]
            .into_iter()
            .filter(|&i| i >= 1 && i <= base.sieved && base.primes[i] >= SMALL && !idx.contains(&i))
            .min_by(|&i, &j| {
                let d = |i: usize| (f64::from(base.primes[i]) / want).ln().abs();
                d(i).total_cmp(&d(j))
            });
            let Some(last) = near else { continue };
            idx.push(last);
            idx.sort_unstable();
            let a: u128 = idx.iter().map(|&i| u128::from(base.primes[i])).product();
            if self.used_a.insert(a) {
                self.a_idx = idx;
                self.a = a;
                break;
            }
        }
        self.init_a();
    }

    /// `B_l`, `b`, `a^-1` mod each prime and mod `2^128`, the roots of the first `b`.
    fn init_a(&mut self) {
        let base = self.base;
        let a = self.a;
        self.big_b.clear();
        for &i in &self.a_idx {
            let q = u64::from(base.primes[i]);
            let aq = a / u128::from(q);
            // `gamma = t (a / q)^-1 mod q`, taken as the smaller of `gamma` and `q - gamma`.
            let mut gamma = mul_mod(
                u64::from(base.root[i]),
                inv_mod_prime((aq % u128::from(q)) as u64, q),
                q,
            );
            if gamma > q / 2 {
                gamma = q - gamma;
            }
            self.big_b.push((aq * u128::from(gamma)) as i128);
        }
        self.b = self.big_b.iter().sum();
        self.a_inv = a.inverse_mod_r();
        let p_count = base.primes.len();
        self.bainv = vec![vec![0u32; p_count]; self.a_idx.len()];
        let m = u64::from(self.par.m);
        for j in 1..=base.sieved {
            if self.a_idx.contains(&j) {
                continue;
            }
            let p = u64::from(base.primes[j]);
            let ainv = inv_mod_prime((a % u128::from(p)) as u64, p);
            for (l, bl) in self.big_b.iter().enumerate() {
                let blp = (*bl as u128 % u128::from(p)) as u64;
                self.bainv[l][j] = mul_mod(2 * blp, ainv, p) as u32;
            }
            let t = u64::from(base.root[j]);
            let bp = (self.b.rem_euclid(i128::from(p))) as u64;
            let r1 = mul_mod(ainv, (t + p - bp) % p, p);
            let r2 = mul_mod(ainv, (2 * p - t - bp) % p, p);
            self.soln1[j] = ((r1 + m) % p) as u32;
            self.soln2[j] = ((r2 + m) % p) as u32;
        }
        self.set_c();
    }

    /// `c = (b^2 - kN) / a`, computed modulo `2^128`. Exact: `a` divides `b^2 - kN` (as `b^2 = kN
    /// mod a`), `a` is odd, so `c = (b^2 - kN) a^-1 mod 2^128`; and `|c| < 2^127`, as `|c| <= kN /
    /// a + b^2 / a`, `kN < 2^134`, `a > 2^(bits/2 - 17)` and `b^2 / a < s a`, so the `i128` read
    /// of that residue is `c`. `kN` itself may pass `2^128`, which is why only its residue is
    /// used.
    fn set_c(&mut self) {
        let b2 = (self.b * self.b) as u128;
        debug_assert_eq!(
            (self.b.rem_euclid(self.a as i128) as u128).pow(2) % self.a,
            (self.base.k as u128 % self.a) * (self.base.n % self.a) % self.a,
            "b^2 = kN mod a"
        );
        self.c = b2.wrapping_sub(self.base.kn).wrapping_mul(self.a_inv) as i128;
    }

    /// Switch to polynomial `i` of the current `a` (0 is set by [`Sieve::init_a`]): Contini's
    /// Gray code, cited at the top of this file. For `i >= 1`, with `l` the trailing zeros of `i`
    /// (`2^(l+1) || 2 i`), `b` moves by `-2 B_l` when `ceil(i / 2^(l+1))` is odd and `+2 B_l`
    /// otherwise, and each root `a^-1 (+-t - b)` moves by minus `a^-1` times that.
    fn poly(&mut self, i: usize) {
        if i == 0 {
            return;
        }
        let l = i.trailing_zeros() as usize;
        let down = i.div_ceil(1 << (l + 1)) % 2 == 1;
        let base = self.base;
        if down {
            self.b -= 2 * self.big_b[l];
        } else {
            self.b += 2 * self.big_b[l];
        }
        let bainv = &self.bainv[l];
        for j in 1..=base.sieved {
            let p = base.primes[j];
            let d = bainv[j];
            let (s1, s2) = (self.soln1[j], self.soln2[j]);
            if down {
                self.soln1[j] = if s1 + d >= p { s1 + d - p } else { s1 + d };
                self.soln2[j] = if s2 + d >= p { s2 + d - p } else { s2 + d };
            } else {
                self.soln1[j] = if s1 >= d { s1 - d } else { s1 + p - d };
                self.soln2[j] = if s2 >= d { s2 - d } else { s2 + p - d };
            }
        }
        self.set_c();
    }

    /// Add `log2 p` at every offset of each root of `g` mod `p`, for the sieved primes from
    /// [`SMALL`] up, except those of `a`.
    fn sieve(&mut self) {
        self.bytes.fill(0);
        let len = self.bytes.len();
        let base = self.base;
        let start = base.primes[1..=base.sieved].partition_point(|&p| p < SMALL) + 1;
        for j in start..=base.sieved {
            if self.a_idx.contains(&j) {
                continue;
            }
            let p = base.primes[j] as usize;
            let lg = base.log[j];
            for s in [self.soln1[j] as usize, self.soln2[j] as usize] {
                let mut o = s;
                while o < len {
                    self.bytes[o] = self.bytes[o].wrapping_add(lg);
                    o += p;
                }
            }
        }
    }

    /// Divide out each `g(x)` the sieve marked; keep the full relations, and the partials, which
    /// join in pairs by their large prime.
    fn collect(&mut self) {
        let base = self.base;
        let m = i64::from(self.par.m);
        let large = base.largest() * self.par.large;
        let thr = self.threshold;
        for o in 0..self.bytes.len() {
            if self.bytes[o] < thr {
                continue;
            }
            let x = o as i64 - m;
            let x128 = i128::from(x);
            let a = self.a as i128;
            // `|g| <= m sqrt(kN / 2)` is below `2^84`; `a x^2 < 2^53 2^34`: no overflow.
            let g = a * x128 * x128 + 2 * self.b * x128 + self.c;
            if g == 0 {
                continue;
            }
            let mut factors: Vec<u32> = Vec::new();
            if g < 0 {
                factors.push(0);
            }
            let mut v = g.unsigned_abs();
            let z = v.trailing_zeros();
            factors.extend(std::iter::repeat_n(1, z as usize));
            v >>= z;
            for j in 1..base.primes.len() {
                let p = base.primes[j];
                let hit = if j <= base.sieved && !self.a_idx.contains(&j) {
                    let r = (o % p as usize) as u32;
                    r == self.soln1[j] || r == self.soln2[j]
                } else {
                    true
                };
                if hit {
                    let p = u128::from(p);
                    while v.is_multiple_of(p) {
                        v /= p;
                        factors.push(j as u32 + 1);
                    }
                }
            }
            // `Q = a g`: the primes of `a`, once each.
            factors.extend(self.a_idx.iter().map(|&j| j as u32 + 1));
            let u = a * x128 + self.b;
            if v == 1 {
                self.relations.push(Relation {
                    u: vec![u],
                    factors,
                    large: 1,
                });
            } else if v < u128::from(large) {
                // Every prime below the largest of the base that can divide `Q` is in the base
                // (a prime `p` dividing `Q` and not `kN` has `kN` a square mod `p`), so `v`,
                // below the square of the largest, is prime.
                let v = v as u64;
                match self.partials.get(&v) {
                    Some(r) => {
                        let mut f = r.factors.clone();
                        f.extend(factors);
                        self.relations.push(Relation {
                            u: vec![r.u[0], u],
                            factors: f,
                            large: v,
                        });
                    }
                    None => {
                        self.partials.insert(
                            v,
                            Relation {
                                u: vec![u],
                                factors,
                                large: 1,
                            },
                        );
                    }
                }
            }
        }
    }
}

/// The primes of `a` are at most this, when the base reaches it: small enough that one `a`
/// gives several polynomials, large enough that they are not in the short strides.
const A_PRIME: u64 = 2000;

/// Gaussian elimination over GF(2) on the exponent vectors, then for each dependency
/// `gcd(X - Y, n)`: the first that lies strictly between 1 and `n`.
fn combine(base: &Base, rels: &[Relation], mont: &Montgomery<u128>) -> Option<u128> {
    let cols = base.columns();
    let r = rels.len();
    let cw = cols.div_ceil(64);
    let width = cw + r.div_ceil(64);
    let mut rows: Vec<Vec<u64>> = rels
        .iter()
        .enumerate()
        .map(|(i, rel)| {
            let mut row = vec![0u64; width];
            for &c in &rel.factors {
                row[c as usize / 64] ^= 1 << (c % 64);
            }
            row[cw + i / 64] |= 1 << (i % 64);
            row
        })
        .collect();
    let mut rank = 0;
    for c in 0..cols {
        let Some(p) = (rank..r).find(|&i| rows[i][c / 64] >> (c % 64) & 1 == 1) else {
            continue;
        };
        rows.swap(rank, p);
        let pivot = rows[rank].clone();
        for (i, row) in rows.iter_mut().enumerate() {
            if i != rank && row[c / 64] >> (c % 64) & 1 == 1 {
                for (w, pw) in row.iter_mut().zip(&pivot) {
                    *w ^= pw;
                }
            }
        }
        rank += 1;
    }
    let n = base.n;
    let to_mont = |u: i128| {
        let v = mont.to(u.unsigned_abs() % n);
        if u < 0 { mont.sub(0, v) } else { v }
    };
    for row in &rows[rank..] {
        let mut x = mont.one();
        let mut y = mont.one();
        let mut exp = vec![0u32; cols];
        for i in 0..r {
            if row[cw + i / 64] >> (i % 64) & 1 == 0 {
                continue;
            }
            let rel = &rels[i];
            for &u in &rel.u {
                x = mont.mul(x, to_mont(u));
            }
            for &c in &rel.factors {
                exp[c as usize] += 1;
            }
            y = mont.mul(y, mont.to(u128::from(rel.large)));
        }
        debug_assert!(exp.iter().all(|e| e % 2 == 0), "a dependency is a square");
        for (c, &e) in exp.iter().enumerate().skip(1) {
            if e > 0 {
                let p = mont.to(u128::from(base.primes[c - 1]));
                y = mont.mul(y, mont.pow(p, u128::from(e / 2)));
            }
        }
        // Both are in Montgomery form, `X R` and `Y R` with `R = 2^128` prime to `n`, so the
        // gcd of their difference with `n` is that of `X - Y`.
        let d = gcd_u128(mont.sub(x, y), n);
        if d != 1 && d != n {
            return Some(d);
        }
    }
    None
}
