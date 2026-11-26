//! Rigorous bounds on a product of prime powers, for ordering exact numbers and rounding them
//! to floats without building their digits.
//!
//! A bound is `m * 2^e` with `m` kept to `k` bits and `e` unbounded, rounded down for a lower
//! bound and up for an upper one at every step, so it bounds the product whatever `k` is; a
//! larger `k` only makes it tighter. A power `p^e` is bounded by squaring, `2 log e` products
//! of `k`-bit numbers, so `10^(10^9)` costs about 60 products and not its billion digits.

use std::borrow::Cow;
use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};

use super::fast;
use super::room::{LiteralRounding, TooLarge, built, room};
use zed_numtheory::BitLen;

/// `coef * prod p^e * prod q^f`, every exponent positive, `q` the wide atoms of a `Rat` (each
/// wider than 64 bits); the coefficient and the atoms are borrowed from the number it bounds
/// where they can be, so a wide one is not copied.
pub(super) struct Product<'a> {
    pub(super) coef: Cow<'a, BigUint>,
    pub(super) pows: Vec<(u64, BigUint)>,
    pub(super) wide: Vec<(Cow<'a, BigUint>, BigUint)>,
}

/// The positive number `m * 2^e`.
struct Bound {
    m: BigUint,
    e: BigInt,
}

impl Bound {
    fn exact(m: BigUint) -> Bound {
        Bound {
            m,
            e: BigInt::zero(),
        }
    }

    /// `m` kept to `k` bits, rounded toward zero or away from it, reading only the bits kept
    /// and the lowest nonzero one: a wide coefficient is not copied in full at each precision.
    fn of(m: &BigUint, k: u64, up: bool) -> Bound {
        let bits = m.bits();
        if bits <= k {
            return Bound::exact(m.clone());
        }
        let drop = bits - k;
        // Unreachable: `bits > k >= 0` here, so `m` is not zero and has a lowest set bit.
        let inexact = m.trailing_zeros().expect("a bound is positive") < drop;
        let mut kept = m >> drop;
        if up && inexact {
            kept += 1u32;
        }
        Bound {
            m: kept,
            e: BigInt::from(drop),
        }
    }

    /// Kept to `k` bits, rounded toward zero, or away from it when `up`.
    fn round(mut self, k: u64, up: bool) -> Bound {
        let bits = self.m.bits();
        if bits <= k {
            return self;
        }
        let drop = bits - k;
        // Unreachable: `bits > k >= 0` here, so `self.m` is not zero.
        let inexact = self.m.trailing_zeros().expect("a bound is positive") < drop;
        self.m >>= drop;
        if up && inexact {
            self.m += 1u32;
        }
        self.e += drop;
        self
    }

    fn mul(&self, other: &Bound, k: u64, up: bool) -> Bound {
        Bound {
            m: fast::mul(&self.m, &other.m),
            e: &self.e + &other.e,
        }
        .round(k, up)
    }

    /// `self / other`, to `k` bits, rounded toward zero or away from it.
    fn div(&self, other: &Bound, k: u64, up: bool) -> Bound {
        let shift = k + other.m.bits();
        let (q, r) = (&self.m << shift).div_rem(&other.m);
        let m = if up && !r.is_zero() { q + 1u32 } else { q };
        Bound {
            m,
            e: &self.e - &other.e - shift,
        }
        .round(k, up)
    }

    /// `floor(log2(self))`.
    fn log2(&self) -> BigInt {
        &self.e + (self.m.bits() - 1)
    }

    fn cmp(&self, other: &Bound) -> Ordering {
        self.log2().cmp(&other.log2()).then_with(|| {
            // With the leading bit in one place, the exponents differ by the difference of the
            // mantissas' widths. Unreachable: equal `log2` gives `e1 + bits1 = e2 + bits2`, so
            // `d = bits2 - bits1`, and no mantissa in memory has `2^63` bits.
            let d = (&self.e - &other.e)
                .to_i64()
                .expect("bounds with one leading place have exponents a mantissa apart");
            if d >= 0 {
                (&self.m << d as u64).cmp(&other.m)
            } else {
                self.m.cmp(&(&other.m << d.unsigned_abs()))
            }
        })
    }

    /// `floor(self * 2^s)`, and whether that is `self * 2^s` exactly.
    fn floor_scaled(&self, s: &BigInt) -> (BigUint, bool) {
        let x = &self.e + s;
        match x.to_u64() {
            // Unreachable: the one caller, `round_with`, takes `s = prec - t` with `t` the top of
            // `log2 q` clamped to the format and lowered only while the scaled value keeps at most
            // `prec` bits, so the scaled bound has at most a few bits more than `prec` and `up`,
            // below it, fits in a `usize`.
            Some(up) => (
                &self.m << usize::try_from(up).expect("a scaled bound near a float's mantissa"),
                true,
            ),
            None => {
                let down = (-x).to_u64().unwrap_or(u64::MAX);
                if down >= self.m.bits() {
                    return (BigUint::zero(), false);
                }
                // Unreachable: `down < self.m.bits()`, so `self.m` is not zero.
                let exact = self.m.trailing_zeros().expect("a bound is positive") >= down;
                (&self.m >> down, exact)
            }
        }
    }
}

impl Product<'_> {
    /// More than the number of bits of the product: what building it costs.
    fn bits(&self) -> BigUint {
        let mut b = BigUint::from(self.coef.bits());
        for (p, e) in &self.pows {
            b += e * p.bit_len();
        }
        for (q, f) in &self.wide {
            b += f * q.bits();
        }
        b
    }

    /// The product itself, built by [`built`], [`fast::pow`] and [`fast::mul`], O(n log n) in
    /// its width; [`TooLarge`] as for [`built`], and for an atom's exponent beyond a word.
    fn materialize(&self) -> Result<BigUint, TooLarge> {
        let mut x = fast::mul(&self.coef, &built(&self.pows)?.into_parts().1);
        for (q, f) in &self.wide {
            let Some(k) = f.to_u64() else {
                return Err(TooLarge {
                    size: self.bits(),
                    ask: self.bits(),
                });
            };
            x = fast::mul(&x, &fast::pow(q, k));
        }
        Ok(x)
    }

    /// The widest exponent, in bits.
    fn exp_bits(&self) -> u64 {
        let pows = self.pows.iter().map(|(_, e)| e.bits());
        pows.chain(self.wide.iter().map(|(_, f)| f.bits()))
            .max()
            .unwrap_or(0)
    }

    /// A lower bound, or an upper one when `up`, kept to `k` bits.
    fn bound(&self, k: u64, up: bool) -> Bound {
        /// `base^e` by squaring from 1, each product rounded to `k` bits.
        fn power(base: &Bound, e: &BigUint, k: u64, up: bool) -> Bound {
            let mut power = Bound::exact(BigUint::one());
            for i in (0..e.bits()).rev() {
                power = power.mul(&power, k, up);
                if e.bit(i) {
                    power = power.mul(base, k, up);
                }
            }
            power
        }
        let mut b = Bound::of(&self.coef, k, up);
        for (p, e) in &self.pows {
            if *p == 2 {
                // `2^e` is a bound exactly: the exponent moves and nothing is rounded or squared.
                b.e += BigInt::from(e.clone());
                continue;
            }
            b = b.mul(&power(&Bound::exact(BigUint::from(*p)), e, k, up), k, up);
        }
        // A wide atom's base is itself rounded to `k` bits first, in the bound's direction, so
        // the power bounds `q^f` the same way ([`cap`] counts this rounding).
        for (q, f) in &self.wide {
            b = b.mul(&power(&Bound::of(q, k, up), f, k, up), k, up);
        }
        b
    }
}

/// The order of two positive products read from their bit lengths alone, when those tell it:
/// `2^(b - 1) <= c < 2^b` for a coefficient of `b` bits and `2^((b - 1) e) <= p^e < 2^(b e)` for
/// a prime of `b` bits, so a product whose least bit length is at least the other's greatest is
/// the larger. Exact integer arithmetic on the exponents, O(terms) word operations for exponents
/// of a word: `1 < 3^200000` is `2^0 <= 1 < 2^1` against `3^200000 >= 2^200000`.
fn by_bit_length(n: &Product<'_>, d: &Product<'_>) -> Option<Ordering> {
    let range = |x: &Product<'_>| {
        let b = x.coef.bits();
        let (mut low, mut high) = (BigUint::from(b - 1), BigUint::from(b));
        for (p, e) in &x.pows {
            let bits = u64::from(p.bit_len());
            low += e * (bits - 1);
            high += e * bits;
        }
        for (q, f) in &x.wide {
            low += f * (q.bits() - 1);
            high += f * q.bits();
        }
        (low, high)
    };
    let ((nl, nh), (dl, dh)) = (range(n), range(d));
    if nl >= dh {
        return Some(Ordering::Greater);
    }
    if dl >= nh {
        return Some(Ordering::Less);
    }
    None
}

/// The error of the system's `log2` on an `f64`, in units in the last place, that
/// [`by_logs`] allows for. Rust documents the precision of `f64::log2` as unspecified ("non-
/// deterministic": it calls the platform's libm). On the one platform of the first release,
/// Linux x86_64 with glibc (2.43 on the build machine, 2026-11-20), the bound is glibc's own:
/// sysdeps/ieee754/dbl-64/e_log2.c (glibc master, read 2026-11-20 on the bminor/glibc mirror;
/// the code of ARM's optimized-routines, in glibc since 2.28) states "Worst-case error is less
/// than 0.54 ULP (0.55 ULP without fma)" for inputs near 1, and "Worst-case error if |y| >
/// 0x1p-4: 0.547 ULP (0.550 ULP without fma)" for the rest, each with its rounding steps
/// listed beside the code. The double format's measured errors, sysdeps/ieee754/dbl-64/
/// libm-test-ulps (last changed acaad9ab0, 2025-10-27), list no `log2` entry: the test suite
/// found none above the correctly rounded result. glibc's manual (section "Errors in Math
/// Functions", read 2026-11-20) promises only "within a few ulp" and flags errors above 9 ulp.
/// So 16 is more than 29 times glibc's stated bound; a larger allowance only moves a few more
/// pairs on to the exact bounds, at no measurable cost.
/// Not proved: the 0.55 ulp figure is the implementer's error analysis in a code comment, not
/// a published proof, and another libm (musl, a later port, PORTABLE-rt) has its own; a libm
/// more than 16 ulps off would let `by_logs` answer wrongly. Tested only on the products of
/// `bit_lengths_and_the_f64_check_decide_products_far_apart`,
/// `products_close_in_log2_go_on_to_the_exact_bounds` and `the_f64_check_needs_its_margin`,
/// whose answers are known exactly.
const LOG2_ULPS: f64 = 16.0;

/// `x` as `m * 2^s` with `m` its leading 64 bits, rounded to an `f64`, and `s` the bits dropped:
/// `m * 2^s` is within a relative `2^-63 + 2^-53 <= 2^-52` of `x` (truncation, then rounding).
fn leading(x: &BigUint) -> (f64, u64) {
    let s = x.bits().saturating_sub(64);
    // Unreachable: `x >> s` has at most 64 bits.
    let m = (x >> s).to_u64().expect("the leading 64 bits");
    (m as f64, s)
}

/// An approximation `S'` of `log2 x` for a product `x`, and the number of its terms; `None`
/// when an exponent is beyond what an `f64` holds with room for the product.
fn log2_sum(x: &Product<'_>) -> Option<(f64, usize)> {
    let mut sum = 0.0f64;
    let mut terms = 0;
    if !x.coef.is_one() {
        let (m, s) = leading(&x.coef);
        sum += s as f64 + m.log2();
        terms += 1;
    }
    for (p, e) in &x.pows {
        let (m, s) = leading(e);
        if s > 900 {
            return None;
        }
        let e = m * 2f64.powi(s as i32);
        sum += e * (*p as f64).log2();
        terms += 1;
    }
    // A wide atom's term `f log2 q`, with `log2 q = s + log2 m` from its leading 64 bits, as
    // the coefficient's: within a relative `(2.04c + 5)u` of `log2 q` (`q > 2^64`, so `s > 0`
    // and `log2 q >= 64`), then times `fl(f)` within `2u` and the product rounded by `u`, inside
    // the `r` of the analysis at [`by_logs`].
    for (q, f) in &x.wide {
        let (m, s) = leading(f);
        if s > 900 {
            return None;
        }
        let (mq, sq) = leading(q);
        sum += m * 2f64.powi(s as i32) * (sq as f64 + mq.log2());
        terms += 1;
    }
    Some((sum, terms))
}

/// The order of two positive products from `log2` of each in `f64`, when the two differ by
/// more than a proved bound on the error; `None` when they do not, or an exponent is beyond an
/// `f64`. `slack` scales the margin: 1 for the proved bound, which every caller passes; a test
/// passes 0 to show that the bound is needed.
///
/// Error analysis, with `u = 2^-53` and `c` = [`LOG2_ULPS`]. Each side is `S = log2 coef +
/// sum e log2 p`, every term at least 0 (`coef >= 1`, `p >= 2`), so relative errors of the
/// terms add without cancellation. A prime's term `fl(fl(e) * L)`, with `L = log2(fl(p))` from
/// the libm: `fl(p)` is within a relative `u` of `p`, which moves `log2 p` by at most
/// `u / ln 2 < 1.45u`, relative `1.45u` since `log2 p >= 1`; the libm adds
/// `c ulp(L) <= 2cu |L|`; `fl(e)` from the leading 64 bits is within `2u` ([`leading`]); the
/// product rounds by `u`. So a term is within a relative `(2c + 5)u` of its value, to first
/// order. The coefficient's term `s + log2(m)`: `m` within `2u`, so `log2 m` within `2.9u`
/// absolute, plus the libm's `c ulp(log2 m) <= c 2^-46` for `m < 2^64`, and the sum rounds by
/// `u`; with `log2 coef >= 63` once `s > 0`, that is within a relative `(2.04c + 5)u`
/// (`c 2^-46 / 63 < 2.04cu`), and below 64 bits it is the prime's case. So every term is
/// within a relative `r = (3c + 6)u`. Recursive summation of `N` terms at least 0 adds a
/// relative `gamma(N - 1) = (N - 1)u / (1 - (N - 1)u)`: N. J. Higham, "Accuracy and Stability
/// of Numerical Algorithms", 2nd ed., SIAM, 2002, doi:10.1137/1.9780898718027 (DOI, title
/// and year checked on Crossref 2026-11-20). Read 2026-11-20 in a scanned copy from LibGen,
/// kept out of the repository and used only to check this comment: section 3.1, Lemma 3.1,
/// p. 63, defines `gamma(n) = nu / (1 - nu)` under `nu < 1`; section 4.2, pp. 81-82, analyses
/// Algorithm 4.1 (any order of the `n - 1` additions, recursive summation among them) and
/// gives the first-order bound (4.4), `|E_n| <= (n - 1)u sum |x_i| + O(u^2)`, then the
/// backward result that the computed sum is the exact sum of the terms `x_i (1 + e_i)` with
/// `|e_i| <= gamma(n - 1)`, since no term takes part in more than `n - 1` additions. With
/// terms at least 0 that gives `|E_n| <= gamma(n - 1) sum x_i`, the bound used here.
/// The bound is also the plain one: each of the `N - 1` additions rounds by at most `u` on a
/// partial sum at most `S`. `the_f64_check_needs_its_margin` shows a margin is needed (with
/// none, some verdicts are wrong); no test shows this margin is enough, which rests on the
/// argument here. So `|S' - S| <= B S` with
/// `B = (3c + 6 + N)u (1 + 2^-20)` for `N` and `c` far below `2^30`, the second-order terms
/// inside the factor. Then `Sn > Sd` holds when `Sn' (1 - B) > Sd' (1 + B)`, that is
/// `Sn' - Sd' > B (Sn' + Sd')`; the test below computes both sides in `f64` and asks for twice
/// that, which covers the rounding of the test itself (three roundings, `(1 - u)^3 / (1 + u) >
/// 1/2`). Since `log2` is increasing, `Sn > Sd` is `n > d`.
pub(super) fn by_logs(n: &Product<'_>, d: &Product<'_>, slack: f64) -> Option<Ordering> {
    let (sn, tn) = log2_sum(n)?;
    let (sd, td) = log2_sum(d)?;
    let terms = tn.max(td) as f64;
    let b = (3.0 * LOG2_ULPS + 6.0 + terms) * 2f64.powi(-53) * (1.0 + 2f64.powi(-20));
    let margin = slack * 2.0 * b * (sn + sd);
    let diff = sn - sd;
    if diff > margin {
        Some(Ordering::Greater)
    } else if -diff > margin {
        Some(Ordering::Less)
    } else {
        None
    }
}

/// The first precision tried: a power `p^e` loses about `log2 e` bits to rounding, so this
/// leaves 64 good bits.
fn start(n: &Product<'_>, d: &Product<'_>) -> u64 {
    64 + n.exp_bits().max(d.exp_bits())
}

/// `x + |x| 2^-40 + 2^-40`: above `x` by more than the rounding of the one `f64` operation that
/// gave `x`, when that operation's inputs were bounds of the same direction, so a chain of
/// operations each followed by `up` stays an upper bound. A relative error of `2^-53` and an
/// absolute one of a few ulps are far inside `2^-40`.
fn up(x: f64) -> f64 {
    x + x.abs() * 2f64.powi(-40) + 2f64.powi(-40)
}

/// An upper bound on `ln x` for `x >= 1`: `x < (m + 1) 2^s` for its leading 64 bits `m`
/// ([`leading`]), and `ln(m + 1) - ln m <= 1/m <= 2^-63` when `s > 0`, where `m >= 2^63`;
/// `x = m` when `s = 0`.
fn ln_up(x: &BigUint) -> f64 {
    let (m, s) = leading(x);
    up(up(m.ln()) + up(s as f64 * std::f64::consts::LN_2))
}

/// A precision `P` in bits with `|ln n - ln d| >= 2^-P`, from Laurent's lower bound on a
/// linear form in two logarithms, when each of `n` and `d` is one power `a^b` with `a > 1` and
/// one of the two `a` is a listed atom; `None` otherwise, or when `P` passes `2^62`.
///
/// The bound (M. Laurent, "Linear forms in two logarithms and interpolation determinants II",
/// Acta Arith. 133(4) (2008) 325-348, doi:10.4064/aa133-4-3; DESIGN.md sec:domains, "Kept
/// powers"). p. 327: "Consider the linear form Λ = b2 log α2 − b1 log α1 , where b1 and b2 are
/// positive integers", with `D = [Q(α1, α2) : Q]/[R(α1, α2) : R]`; p. 328: "b0 = b1/(D log A2) +
/// b2/(D log A1), where A1 and A2 are real numbers > 1 such that log Ai ≥ max{h(αi),
/// |log αi|/D, 1/D}", and "Corollary 2. Suppose moreover that the numbers α1, α2, log α1, log α2
/// are real and positive. Then log |Λ| ≥ −C2 D4 (max{log b0 + 0.38, m/D, 1})2 log A1 log A2
/// for each pair (m, C2(m)) from Table 1", whose last column is `m = 30`, `C2 = 17.9`; Corollary
/// 1, which Corollary 2 extends, asks that "α1 and α2 are multiplicatively independent".
///
/// Proof that it applies. Take `α1 = a_d`, `b1 = b_d`, `α2 = a_n`, `b2 = b_n`, so `Λ = ln n -
/// ln d` with `b1, b2` positive integers. The `α` are integers above 1, so real and positive
/// with positive logarithms, and `D = 1 / 1 = 1`. Independence: the caller (`Rat`'s
/// `magnitude_order`) passes coefficients coprime to every listed atom and listed atoms that
/// are pairwise coprime, a wide atom of a `Rat` (`Product::wide`) among them, since a `Rat`'s
/// wide atoms are coprime to each other, to its listed primes and to its coefficients, and a
/// pair with one goes through the quotient of the two, one `Rat`; so with one `a` listed the
/// two `a` are coprime; then `a_1^x = a_2^y` with `x, y` not both 0 is impossible, since
/// `x, y > 0` puts a prime of `a_1` into `a_2`, and one of them 0 makes a number above 1
/// equal 1. The other caller, [`cmp_without_base`], passes distinct atoms that may share
/// primes, independent by the proof there. The height of an integer `a > 1` is `ln a`, so any
/// `ln A_i >= max(ln a_i, 1)` meets the condition, and the bound holds for every such choice;
/// this takes `ln A_i` as the upper bound [`ln_up`] of `ln a_i`, at least 1. A larger
/// `b0` only weakens the bound (it is increasing in `log b0`), so `ln b0` is bounded above by
/// `ln 2 + max(ln b1 - ln ln A2, ln b2 - ln ln A1)`, since `x + y <= 2 max(x, y)`, which stays
/// in `f64` range for exponents of any width. Then `|Λ| >= e^-C = 2^-(C / ln 2)` with `C =
/// 17.9 max(ln b0 + 0.38, 30)^2 ln A1 ln A2`, and `P` is `C / ln 2` rounded up, every step of
/// it rounded up by [`up`] (17.9 itself is below its `f64`, which `up` covers).
///
/// For `3^(2^40)` against `2^e`, `e < 2^41`: `ln b0 + 0.38` is about 29.4, under 30, and `C /
/// ln 2 = 17.9 * 900 * ln 3 / ln 2 = 25533.8`, so `P = 25534`, the 25,534 bits of DESIGN.md.
pub(super) fn laurent_bits(n: &Product<'_>, d: &Product<'_>) -> Option<u64> {
    // `(ln_up a, b, listed)` for a product that is one power `a^b`, `a > 1`.
    fn single(x: &Product<'_>) -> Option<(f64, BigUint, bool)> {
        match (x.coef.is_one(), &x.pows[..], &x.wide[..]) {
            (true, [(p, e)], []) => Some((ln_up(&BigUint::from(*p)), e.clone(), true)),
            (true, [], [(q, f)]) => Some((ln_up(q), f.clone(), true)),
            (false, [], []) => Some((ln_up(&x.coef), BigUint::one(), false)),
            _ => None,
        }
    }
    let (ln_a2, b2, listed2) = single(n)?;
    let (ln_a1, b1, listed1) = single(d)?;
    if !(listed1 || listed2) {
        return None;
    }
    let (ln_big_a1, ln_big_a2) = (ln_a1.max(1.0), ln_a2.max(1.0));
    // Lower bounds on `ln ln A_i`, which is at least 0.
    let ln_ln_down = |x: f64| (x.ln() * (1.0 - 2f64.powi(-40)) - 2f64.powi(-40)).max(0.0);
    let ln_b0 = up(std::f64::consts::LN_2
        + up(up(ln_up(&b1) - ln_ln_down(ln_big_a2)).max(up(ln_up(&b2) - ln_ln_down(ln_big_a1)))));
    let s = up(ln_b0 + 0.38).max(30.0);
    let c = up(up(up(up(17.9) * up(s * s)) * ln_big_a1) * ln_big_a2);
    let p = up(c / std::f64::consts::LN_2).ceil();
    (p < 2f64.powi(62)).then_some(p as u64)
}

/// A precision `k` at which the rounds of [`cmp`] must tell `n` and `d` apart, when
/// [`laurent_bits`] gives `P`: `P + eb + 9`, `eb` the widest exponent in bits, at least 1.
///
/// Proof. A rounding to `k` bits ([`Bound::of`], [`Bound::round`]) keeps `m >= 2^(k - 1)` units
/// of `2^drop` and moves the value `v` by less than one unit, so by less than `δ v` with `δ =
/// 2^(1 - k)`; in logarithms by at most `ln(1 + δ) <= δ` up and `-ln(1 - δ) <= 2δ` down, so
/// `2^(2 - k)` either way. A power `p^e` by squaring from 1 rounds twice a step at most, so its
/// error in logarithms after step `j` is `E_j <= 2 E_(j-1) + 2^(3 - k)`, `E_0 = 0`, hence
/// `E_t <= 2^(3 - k) (2^t - 1) < 2^(4 - k) e` for `t` the bits of `e`. A wide atom's base is
/// rounded once first, by at most `2^(2 - k)` in logarithms, which its power multiplies by `e`:
/// `2^(2 - k) e` more, so a power is within `2^(4 - k) e + 2^(2 - k) e < 2^(5 - k) e`. The
/// coefficient adds one rounding and the product of the two one more. So each side's bound is
/// within `2^(3 - k) + 2^(5 - k) e <= 2^(6 + eb - k)` of the side in logarithms, up and down
/// alike, and its interval `[low, high]` has `ln(high / low) <= 2^(7 + eb - k)`. When neither
/// `low_n > high_d` nor `high_n < low_d`, the two intervals meet, so `|ln n - ln d| <=
/// ln(high_n / low_n) + ln(high_d / low_d) <= 2^(8 + eb - k)`, which at `k >= P + eb + 9` is
/// below `2^-P <= |ln n - ln d|`, a contradiction. A power of 2 is bounded exactly and only
/// tightens this.
fn cap(n: &Product<'_>, d: &Product<'_>) -> Option<u64> {
    let eb = n.exp_bits().max(d.exp_bits()).max(1);
    laurent_bits(n, d).map(|p| p + eb + 9)
}

/// `n` and `d` with every exponent divided by `g`, the greatest common divisor of all the
/// exponents of both, when `g > 1` and both coefficients are 1; `None` otherwise.
///
/// Proof that the order is kept: with coefficient 1 each side is `prod x^(g k_x)`, so it is
/// `r^g` for `r = prod x^(k_x)`, the side returned, and `r > 0`. For an integer `g >= 1`,
/// `t -> t^g` is strictly increasing on the positive reals, so `r_n^g` and `r_d^g` order as
/// `r_n` and `r_d`. A side with no exponent at all is 1 and stays 1.
///
/// Complexity tradeoff: the rounds of [`cmp_at`] raise `k`-bit bounds to each exponent by
/// squaring, `O(log e M(k))` a round, and two sides that agree in their first `m` bits take `k`
/// near `m`. Two products of wide powers with one exponent `e`, `(a b)^e` against `(b c)^e`, agree
/// in as many bits as `a / c` is near 1, about the bits of the atoms when they are close, so the
/// rounds cost `O(log e M(m))` against the `O(M(m))` of comparing the roots `a` and `c` (or with
/// small exponents, built in full). Measured on `(a b)^(2^64)` against `(b c)^(2^64)`, `a`, `b`,
/// `c` within 64 of `2^(m - 1)`: 175 ms at `m = 2^16` and 2.93 s at `2^19` without this, 16.7
/// times for 8 times the bits (2026-11-24, Colab). The gcd costs `O(terms)` gcds of exponents,
/// a word or two each, beside the rounds' products of `k`-bit numbers.
fn common_root<'a>(n: &Product<'a>, d: &Product<'a>) -> Option<(Product<'a>, Product<'a>)> {
    if !n.coef.is_one() || !d.coef.is_one() {
        return None;
    }
    let mut g = BigUint::zero();
    for x in [n, d] {
        for e in x
            .pows
            .iter()
            .map(|(_, e)| e)
            .chain(x.wide.iter().map(|(_, f)| f))
        {
            g = g.gcd(e);
            if g.is_one() {
                return None;
            }
        }
    }
    // `g = 0`: both sides are 1, which the bit lengths already ordered.
    if g.is_zero() {
        return None;
    }
    let root = |x: &Product<'a>| Product {
        coef: x.coef.clone(),
        pows: x.pows.iter().map(|(p, e)| (*p, e / &g)).collect(),
        wide: x.wide.iter().map(|(q, f)| (q.clone(), f / &g)).collect(),
    };
    Some((root(n), root(d)))
}

/// The order of two positive products. The system is asked for the memory of each precision
/// before it is tried, `8k` bits for what a round holds at once (four `k`-bit bounds and the
/// `2k`-bit product of two, with room to spare), and for the two products in full before they
/// are built; [`TooLarge`] when it refuses. This holds for every caller, the [`Ord`] of `Rat`
/// with no `Watch` and `Rat::integer_text` among them: a pair close enough to reach a
/// precision, or a build, past the free memory is refused and not built, where the build with
/// no ask aborted the process (NUM-huge-div).
pub(super) fn cmp(n: &Product<'_>, d: &Product<'_>) -> Result<Ordering, TooLarge> {
    cmp_at(n, d).map(|(o, _)| o)
}

/// The order of two positive products with coefficient 1 whose atoms (listed primes and wide
/// atoms) are distinct but may share primes across the two sides, when it is cheap to tell
/// without a coprime base: from the bit lengths or the logarithms ([`by_bit_length`],
/// [`by_logs`]), or when the exponents have a common factor `g > 1` ([`common_root`]) and the
/// two roots cost at most `h ceil(log2 h)` bits to build, `h` the bits of the distinct atoms
/// of both sides; then [`cmp`] of the roots. `None` otherwise: the caller takes the quotient in
/// normal form (`Rat::magnitude_order`). Plan row FAIL-wide-product-order-ratio.
///
/// Proof that the order is the order of `n` and `d`: the first two read sound bounds (their
/// proofs are at each); [`common_root`] keeps the order (proof there); [`cmp`] of the roots is
/// exact, as its rounds read sound bounds and it builds the two when its precision reaches
/// their cost, which the test below holds to `h ceil(log2 h)`. [`cap`] of two atoms is sound
/// here too: it asks only that the two be multiplicatively independent (Laurent's Corollary
/// 1, quoted at [`laurent_bits`]), and two distinct atoms are: each is a prime or a wide atom
/// of a `Rat`, which is not a perfect power (its least root, `Rat::wide`), and `a^x = b^y`
/// with `x, y > 0` makes `a` and `b` powers of one `r` (`r = a^(1/s)` for `s = y / gcd(x,
/// y)`), so both are `r` and equal; one exponent 0 makes a number above 1 equal 1.
///
/// Complexity tradeoff: the quotient builds the coprime base of all the atoms,
/// O(M(h) log^2 h) at most (`num::coprime`), before [`cmp`]; this path costs O(terms) for the
/// first two tests and the gcd of the exponents, and the roots' rounds and build at most
/// O(M(b)) for `b <= h log2 h` built bits, so it is never of a higher order than the quotient,
/// and on `(a b)^e` against `(b c)^e` it costs the `O(M(m))` of comparing `a b` and `b c`
/// where the base cost three gcds and the splits of `a`, `b` and `c`.
pub(super) fn cmp_without_base(
    n: &Product<'_>,
    d: &Product<'_>,
) -> Option<Result<Ordering, TooLarge>> {
    if let Some(o) = by_bit_length(n, d).or_else(|| by_logs(n, d, 1.0)) {
        return Some(Ok(o));
    }
    let (rn, rd) = common_root(n, d)?;
    let h: u64 = [n, d]
        .iter()
        .flat_map(|x| {
            let pows = x.pows.iter().map(|(p, _)| u64::from(p.bit_len()));
            pows.chain(x.wide.iter().map(|(q, _)| q.bits()))
        })
        .sum();
    let limit = BigUint::from(h) * (u64::from(h.max(2).next_power_of_two().ilog2()));
    if rn.bits() + rd.bits() > limit {
        return None;
    }
    Some(cmp(&rn, &rd))
}

/// [`cmp`], with the last precision a round of bounds tried, 0 when none ran.
fn cmp_at(n: &Product<'_>, d: &Product<'_>) -> Result<(Ordering, u64), TooLarge> {
    // Complexity tradeoff (LIT-power-values): the order is tried first from the bit lengths in
    // exact integer arithmetic ([`by_bit_length`]), then from `log2` of each side in `f64` with
    // a proved error bound ([`by_logs`]), each O(terms) word operations for exponents of a
    // word, and only then from the `k`-bit bounds below, whose first round costs `2 log e`
    // products of about `64 + log2 e` bits. So `1 < 3^200000` and `2^200000 < 3^200000` cost a
    // few word operations, and only two sides within a relative `2^-45` or so in `log2` reach
    // the bounds. The f64 check was the author's addition (2026-11-13); the alternative of the
    // bounds alone was already free of the digits, at O(log^2 e) word operations.
    if let Some(o) = by_bit_length(n, d).or_else(|| by_logs(n, d, 1.0)) {
        return Ok((o, 0));
    }
    if let Some((n, d)) = common_root(n, d) {
        return cmp_at(&n, &d);
    }
    let cost = n.bits() + d.bits();
    let mut k = start(n, d);
    let cap = cap(n, d);
    loop {
        // Complexity tradeoff: two products that agree in their first `k` bits are told apart
        // by doubling `k`, and once `k` reaches the size of the products themselves they are
        // built and compared, at a cost proportional to their size, the cost of the
        // materializing comparison this replaces; no input is refused. Bounds stop separating
        // only when the two numbers agree in about `k` leading bits, as `2^a 5^b` and
        // `3^c 7^d` with `a log 2 + b log 5` close to `c log 3 + d log 7`. Tested by
        // `close_products_compare_exactly` (COMPLEXITY.md K30). For two atoms the build
        // is reached only when it costs less than twice [`cap`]: Laurent's bound on a linear
        // form in two logarithms names a precision,
        // [`cap`], at which the bounds must part, polynomial in the bits of the exponents
        // (25,534 bits plus the exponents' width for `3^(2^40)` against any `2^e`, `e < 2^41`).
        // For three or more, Matveev's bound was not read and is not relied on (DESIGN.md
        // sec:domains, "Kept powers").
        // Complexity tradeoff: each ask is one allocation of the size asked, given and freed
        // at once (`room`), O(1) beside the round or the build it comes before, which costs
        // at least its size; the alternative of asking only under a `Watch` left an unwatched
        // comparison to abort the process on a precision or a build the system cannot give.
        if BigUint::from(k) >= cost {
            room(cost.clone(), cost)?;
            return Ok((n.materialize()?.cmp(&d.materialize()?), k));
        }
        // Two atoms: a round past the cap was reached from one below it, which by [`cap`]
        // told the two apart, so no round runs at twice the cap or more.
        debug_assert!(cap.is_none_or(|c| k == start(n, d) || k < 2 * c));
        room(BigUint::from(k) << 1u32, BigUint::from(k) << 3u32)?;
        let (nl, nu) = (n.bound(k, false), n.bound(k, true));
        let (dl, du) = (d.bound(k, false), d.bound(k, true));
        if nl.cmp(&du) == Ordering::Greater {
            return Ok((Ordering::Greater, k));
        }
        if nu.cmp(&dl) == Ordering::Less {
            return Ok((Ordering::Less, k));
        }
        k *= 2;
    }
}

/// The binary floating-point format a projection rounds to.
pub(super) struct Format {
    /// Bits of the significand, with its leading one.
    pub(super) prec: u64,
    /// The exponent of the least normal number.
    pub(super) emin: i64,
    /// The exponent of the largest finite number.
    pub(super) emax: i64,
}

/// What the rounding reads of `q = n / d`.
enum Quotient {
    /// Bounds on `q`.
    Bounds { low: Bound, high: Bound },
    /// `n` and `d` themselves.
    Exact { n: BigUint, d: BigUint },
}

impl Quotient {
    /// Bounds on `floor(log2 q)`.
    fn log2(&self) -> (BigInt, BigInt) {
        match self {
            Quotient::Bounds { low, high } => (low.log2(), high.log2()),
            Quotient::Exact { n, d } => {
                let t = BigInt::from(n.bits()) - BigInt::from(d.bits());
                (&t - 1, t)
            }
        }
    }

    /// `floor(q * 2^s)` and whether that is `q * 2^s` exactly; `None` when the bounds do not
    /// tell. `is` is the exact test that `q * 2^s` is a given integer.
    fn floor_scaled(
        &self,
        s: &BigInt,
        is: &dyn Fn(&BigInt, &BigUint) -> bool,
    ) -> Option<(BigUint, bool)> {
        match self {
            Quotient::Bounds { low, high } => {
                let (wl, at_wl) = low.floor_scaled(s);
                let (wh, _) = high.floor_scaled(s);
                if wl == wh {
                    // `q * 2^s >= low * 2^s`, past `wl` unless the bound is on it.
                    let whole = at_wl && is(s, &wl);
                    Some((wl, whole))
                } else if wh == &wl + 1u32 && is(s, &wh) {
                    Some((wh, true))
                } else {
                    None
                }
            }
            Quotient::Exact { n, d } => {
                // Unreachable: `|s| = |prec - t|` with `t` clamped to the format's exponents, at
                // most `prec - emin`, 1,075 for `f64`.
                let shift = |x: &BigUint, by: &BigInt| {
                    x << by.to_usize().expect("a float's scale fits in memory")
                };
                let (w, r) = if s.sign() == num_bigint::Sign::Minus {
                    n.div_rem(&shift(d, &-s))
                } else {
                    shift(n, s).div_rem(d)
                };
                Some((w, r.is_zero()))
            }
        }
    }
}

/// `n / d` rounded to `f`, to nearest with ties to even, as a significand `m` and the exponent
/// `t` of its leading place, so the float is `m * 2^(t - prec + 1)`. `is` tests exactly whether
/// `n / d * 2^s` is the integer `w`, which only a near-tie needs. The system is asked for the
/// memory of each precision before it is tried, `32k` bits for what a round holds at once (four
/// `k`-bit bounds, a dividend of up to `3k` bits, and num-bigint's division of it), and for `n`
/// and `d` in full before they are built; [`LiteralRounding::TooLarge`] when it refuses.
pub(super) fn round(
    n: &Product<'_>,
    d: &Product<'_>,
    f: &Format,
    is: &dyn Fn(&BigInt, &BigUint) -> bool,
) -> Result<(u64, i64), LiteralRounding> {
    let cost = n.bits() + d.bits();
    let mut k = start(n, d);
    loop {
        // Complexity tradeoff: the precision doubles until the bounds fix the rounding, and
        // once it reaches the size of `n` and `d` they are built, as in `cmp`: a quotient within
        // `2^-k` of a rounding boundary that is not on it costs the size of its parts. Tested
        // by `projection_matches_the_standard_reading` (COMPLEXITY.md K30). A complete solution
        // would stop at a precision from a lower bound on the distance to the boundary.
        let q = if BigUint::from(k) >= cost {
            room(cost.clone(), cost.clone()).map_err(LiteralRounding::TooLarge)?;
            Quotient::Exact {
                n: n.materialize().map_err(LiteralRounding::TooLarge)?,
                d: d.materialize().map_err(LiteralRounding::TooLarge)?,
            }
        } else {
            // Complexity tradeoff: a round asks for `32k` bits, a measured bound, not a proved
            // one: the peak heap of the rounds of a number just below a rounding boundary was
            // 1.30 to 1.39 times `16k` for parts of 2^12 to 2^18 words, the rise from num-bigint's
            // Burnikel-Ziegler division (`Bound::div`), which a sum of the parts, `12k`, missed;
            // asking `16k` let a round start and abort the compiler on a literal of 2^24 digits
            // under a limit 128 MiB above its holdings. So a round needing less is refused when
            // the free memory lies between the two. Tested by
            // `a_literal_near_a_rounding_boundary_is_a_compile_error_when_memory_is_short`
            // (COMPLEXITY.md K30). A complete solution would be a division whose scratch is
            // allocated once, its size known by construction.
            room(BigUint::from(k) << 1u32, BigUint::from(k) << 5u32)
                .map_err(LiteralRounding::TooLarge)?;
            let (nl, nu) = (n.bound(k, false), n.bound(k, true));
            let (dl, du) = (d.bound(k, false), d.bound(k, true));
            Quotient::Bounds {
                low: nl.div(&du, k, false),
                high: nu.div(&dl, k, true),
            }
        };
        if let Some(r) = round_with(&q, f, is) {
            return r;
        }
        k *= 2;
    }
}

/// The rounding, when `q` tells it.
fn round_with(
    q: &Quotient,
    f: &Format,
    is: &dyn Fn(&BigInt, &BigUint) -> bool,
) -> Option<Result<(u64, i64), LiteralRounding>> {
    let (low, high) = q.log2();
    if low > BigInt::from(f.emax) {
        return Some(Err(LiteralRounding::Infinite));
    }
    // Unreachable: a value clamped to `[emin, emax]` fits in an `i64`.
    let mut t = high
        .clamp(BigInt::from(f.emin), BigInt::from(f.emax))
        .to_i64()
        .expect("clamped to the format's exponents");
    loop {
        // `v = q * 2^(prec - t)` is twice the significand, so its last bit is the half.
        let (w, whole) = q.floor_scaled(&BigInt::from(f.prec as i64 - t), is)?;
        if w.bits() > f.prec + 1 {
            return Some(Err(LiteralRounding::Infinite));
        }
        if w.bits() <= f.prec && t > f.emin {
            t -= 1;
            continue;
        }
        let half = &w >> 1u32;
        let m = if !w.bit(0) || (whole && !half.bit(0)) {
            half
        } else {
            half + 1u32
        };
        // Unreachable: `w` has at most `prec + 1` bits here, so `half + 1 <= 2^prec`, at most
        // `2^53`.
        let mut m = m.to_u64().expect("a significand fits in 64 bits");
        if m == 1 << f.prec {
            m >>= 1;
            t += 1;
        }
        if t > f.emax {
            return Some(Err(LiteralRounding::Infinite));
        }
        if m == 0 {
            return Some(Err(LiteralRounding::Zero));
        }
        return Some(Ok((m, t)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Pow;

    fn product(coef: BigUint, pows: &[(u64, u64)]) -> Product<'static> {
        Product {
            coef: Cow::Owned(coef),
            pows: pows.iter().map(|&(p, e)| (p, BigUint::from(e))).collect(),
            wide: Vec::new(),
        }
    }

    fn power(p: u64, e: u64) -> Product<'static> {
        product(BigUint::one(), &[(p, e)])
    }

    /// `1 < 3^200000` by the bit lengths alone; `2^84 < 3^53`, whose bit lengths overlap (85
    /// against 53 to 106) and whose `log2` differ by 0.0028, far past the bound of about
    /// `10^-11`, by the f64 check.
    #[test]
    fn bit_lengths_and_the_f64_check_decide_products_far_apart() {
        let one = product(BigUint::one(), &[]);
        assert_eq!(
            by_bit_length(&one, &power(3, 200_000)),
            Some(Ordering::Less)
        );
        assert_eq!(
            by_bit_length(&power(3, 200_000), &one),
            Some(Ordering::Greater)
        );
        let (a, b) = (power(2, 84), power(3, 53));
        assert_eq!(by_bit_length(&a, &b), None);
        assert_eq!(by_logs(&a, &b, 1.0), Some(Ordering::Less));
        assert_eq!(by_logs(&b, &a, 1.0), Some(Ordering::Greater));
        assert_eq!(cmp(&a, &b), Ok(Ordering::Less));
    }

    /// `2^16785921` and `3^10590737`, from a convergent of `log2 3`: their `log2` differ by
    /// about `5 * 10^-8`, inside the bound of about `4 * 10^-7`, so the f64 check leaves them to
    /// the `k`-bit bounds. The order is checked against `log2 3` to 40 digits, in integers.
    #[test]
    fn products_close_in_log2_go_on_to_the_exact_bounds() {
        let (p, q) = (16_785_921u64, 10_590_737u64);
        let (a, b) = (power(2, p), power(3, q));
        assert_eq!(by_bit_length(&a, &b), None);
        assert_eq!(by_logs(&a, &b, 1.0), None);
        let log2_3 =
            BigUint::parse_bytes(b"15849625007211561814537389439478165087598", 10).expect("digits");
        let expected =
            (BigUint::from(p) * BigUint::from(10u32).pow(40u32)).cmp(&(BigUint::from(q) * log2_3));
        assert_eq!(cmp(&a, &b), Ok(expected));
        assert_eq!(cmp(&b, &a), Ok(expected.reverse()));
    }

    /// [`laurent_bits`] at the example of DESIGN.md: `3^(2^40)` against `2^e`, `e < 2^41`, is
    /// `17.9 * 900 * ln 3 / ln 2 = 25533.8` rounded up. The plateau of `max(ln b0 + 0.38, 30)`
    /// ends between `e = 2^41` (`ln b0 + 0.38` about 29.4, rounded up) and `e = 2^43` (about
    /// 30.6), where the bound grows. A side that is not one power, or two sides neither of which
    /// is a listed atom, have no bound.
    #[test]
    fn the_laurent_bound_of_two_atoms() {
        let three = power(3, 1 << 40);
        for e in [1u64, 1 << 20, (1 << 41) - 1] {
            assert_eq!(laurent_bits(&three, &power(2, e)), Some(25534), "e = {e}");
            assert_eq!(laurent_bits(&power(2, e), &three), Some(25534), "e = {e}");
        }
        let far = laurent_bits(&three, &power(2, 1 << 43)).expect("two atoms");
        assert!(far > 25534, "{far}");
        // `5` as a coefficient, against the listed atom 3.
        let five = product(BigUint::from(5u32), &[]);
        assert!(laurent_bits(&five, &three).is_some());
        assert_eq!(
            laurent_bits(&five, &product(BigUint::from(7u32), &[])),
            None
        );
        assert_eq!(
            laurent_bits(&product(BigUint::from(5u32), &[(3, 2)]), &three),
            None
        );
        assert_eq!(
            laurent_bits(&product(BigUint::one(), &[(2, 1), (5, 1)]), &three),
            None
        );
    }

    /// The pair nearest in `log2` among `2^p` and `3^q` with `q < 2^40`, from the last
    /// convergent `p/q` with `q < 2^40` of the continued fraction of `log2 3` to 40 digits, the
    /// hardest such pair for the bounds: `|q log2 3 - p| < 1/q`, so the ratio of the two is
    /// within about `2^-39` of 1. The order is checked against the 40 digits in integers, whose
    /// error, below `q` units of `10^-40`, the test checks is under the distance itself; the last
    /// precision tried is below twice [`cap`], which the debug assertion in [`cmp_at`] also
    /// checks at every round.
    #[test]
    fn the_nearest_pair_below_2_to_the_40_parts_under_the_cap() {
        let ten40 = BigUint::from(10u32).pow(40u32);
        let log2_3 =
            BigUint::parse_bytes(b"15849625007211561814537389439478165087598", 10).expect("digits");
        // Convergents `h/k` of `log2_3 / 10^40` by Euclid's algorithm.
        let (mut x, mut y) = (log2_3.clone(), ten40.clone());
        let (mut h0, mut h1) = (BigUint::zero(), BigUint::one());
        let (mut k0, mut k1) = (BigUint::one(), BigUint::zero());
        let (mut p, mut q) = (0u64, 0u64);
        while !y.is_zero() {
            let (a, r) = x.div_rem(&y);
            let h = &a * &h1 + &h0;
            let k = &a * &k1 + &k0;
            if k >= BigUint::from(1u64 << 40) {
                break;
            }
            (p, q) = (h.to_u64().expect("a word"), k.to_u64().expect("a word"));
            (h0, h1, k0, k1, x, y) = (h1, h, k1, k, y, r);
        }
        assert_eq!((p, q), (1_193_652_440_098, 753_110_839_881));
        let (a, b) = (power(2, p), power(3, q));
        let gap = (BigInt::from(BigUint::from(p) * &ten40)
            - BigInt::from(BigUint::from(q) * &log2_3))
        .magnitude()
        .clone();
        assert!(gap > BigUint::from(q), "the 40 digits decide the order");
        let expected = (BigUint::from(p) * &ten40).cmp(&(BigUint::from(q) * &log2_3));
        let (order, k) = cmp_at(&a, &b).expect("bounds of a few hundred bits");
        assert_eq!(order, expected);
        assert_eq!(cmp_at(&b, &a).map(|(o, _)| o), Ok(expected.reverse()));
        let cap = cap(&a, &b).expect("two atoms");
        assert!(k > 0 && k < 2 * cap, "precision {k}, cap {cap}");
    }

    /// DESIGN.md step L1.17b: for each convergent `p/q` of the continued fraction of `log2 3`
    /// with `p` below 2^24, `2^p` against `3^q` gives the order of the built numbers, at a
    /// precision no larger than Laurent's bound for the pair ([`laurent_bits`]). The convergents
    /// come from `log2 3` to 40 digits by Euclid's algorithm, as in the test above; the largest
    /// with `p < 2^24` is `301994/190537`, the next `16785921/10590737`, so each built number has
    /// at most 301,994 bits. A precision of 0 is an order the bit lengths or the f64 check gave.
    #[test]
    fn each_convergent_of_log2_3_below_2_to_the_24_orders_as_the_built_numbers() {
        let ten40 = BigUint::from(10u32).pow(40u32);
        let log2_3 =
            BigUint::parse_bytes(b"15849625007211561814537389439478165087598", 10).expect("digits");
        let (mut x, mut y) = (log2_3, ten40);
        let (mut h0, mut h1) = (BigUint::zero(), BigUint::one());
        let (mut k0, mut k1) = (BigUint::one(), BigUint::zero());
        let mut pairs = Vec::new();
        while !y.is_zero() {
            let (a, r) = x.div_rem(&y);
            let h = &a * &h1 + &h0;
            let k = &a * &k1 + &k0;
            if h >= BigUint::from(1u64 << 24) {
                break;
            }
            pairs.push((h.to_u64().expect("a word"), k.to_u64().expect("a word")));
            (h0, h1, k0, k1, x, y) = (h1, h, k1, k, y, r);
        }
        assert_eq!(pairs.last(), Some(&(301_994, 190_537)));
        assert!(pairs.len() >= 12, "{pairs:?}");
        for &(p, q) in &pairs {
            let (a, b) = (power(2, p), power(3, q));
            let built = (BigUint::one() << p).cmp(&BigUint::from(3u32).pow(q));
            let (order, k) = cmp_at(&a, &b).expect("numbers of at most 301,994 bits");
            assert_eq!(order, built, "2^{p} against 3^{q}");
            assert_eq!(cmp(&b, &a), Ok(built.reverse()), "3^{q} against 2^{p}");
            let laurent = laurent_bits(&a, &b).expect("two atoms");
            assert!(
                k <= laurent,
                "2^{p} against 3^{q}: precision {k}, Laurent {laurent}"
            );
        }
    }

    /// `3^1000 + 1` and `3^1000 - 1` against `3^1000`: the f64 check leaves both, which agree
    /// with `3^1000` in about 1585 bits, and the bounds reach the products' size and build them.
    /// The negative control: with no margin (`slack` 0) the f64 check gives one verdict for
    /// both pairs, for some exponents, and so a wrong one; a margin too small is not sound.
    #[test]
    fn the_f64_check_needs_its_margin() {
        let mut wrong = 0;
        for k in 1000u32..1064 {
            let x = BigUint::from(3u32).pow(k);
            let pow = power(3, u64::from(k));
            let above = product(&x + 1u32, &[]);
            let below = product(&x - 1u32, &[]);
            for (side, truth) in [(&above, Ordering::Greater), (&below, Ordering::Less)] {
                assert_eq!(by_logs(side, &pow, 1.0), None);
                assert_eq!(cmp(side, &pow), Ok(truth));
                if by_logs(side, &pow, 0.0).is_some_and(|o| o != truth) {
                    wrong += 1;
                }
            }
        }
        assert!(wrong > 0, "no exponent gave a wrong verdict with no margin");
    }

    /// [`common_root`] divides every exponent by their gcd, leaves a coefficient other than 1
    /// and coprime exponents alone, and the order of two close wide powers with one exponent
    /// `2^64` is that of their atoms.
    #[test]
    fn a_common_root_of_both_sides_keeps_their_order() {
        let m = 1u64 << 12;
        let odd = |k: u32| (BigUint::one() << (m - 1)) + BigUint::from(2 * k + 1);
        let (a, c) = (odd(7), odd(28));
        let e = BigUint::one() << 64u32;
        let wide = |q: &BigUint, f: &BigUint, p: &[(u64, u64)]| Product {
            coef: Cow::Owned(BigUint::one()),
            pows: p.iter().map(|&(p, k)| (p, BigUint::from(k) * f)).collect(),
            wide: vec![(Cow::Owned(q.clone()), f.clone())],
        };
        let (n, d) = (wide(&a, &e, &[(3, 2)]), wide(&c, &e, &[(3, 2)]));
        let (rn, rd) = common_root(&n, &d).expect("a common root");
        assert_eq!(rn.pows, vec![(3, BigUint::from(2u32))]);
        assert_eq!(rn.wide[0].1, BigUint::one());
        assert_eq!(rd.wide[0].1, BigUint::one());
        assert_eq!(cmp(&n, &d), Ok(Ordering::Less));
        assert_eq!(cmp(&d, &n), Ok(Ordering::Greater));
        // Exponents 2^64 and 2^64 + 1 are coprime; a coefficient of 2 is not a power.
        let f = &e + BigUint::one();
        assert!(common_root(&n, &wide(&c, &f, &[])).is_none());
        let mut two = wide(&c, &e, &[]);
        two.coef = Cow::Owned(BigUint::from(2u32));
        assert!(common_root(&n, &two).is_none());
    }
}
