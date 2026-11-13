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

use super::fast::{self, built};
use super::room::{LiteralRounding, TooLarge, room};

/// `coef * prod p^e`, every exponent positive; the coefficient is borrowed from the number it
/// bounds where it can be, so a wide one is not copied.
pub(super) struct Product<'a> {
    pub(super) coef: Cow<'a, BigUint>,
    pub(super) pows: Vec<(u64, BigUint)>,
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
            b += e * (64 - p.leading_zeros());
        }
        b
    }

    /// The product itself, built by [`built`] and [`fast::mul`], O(n log n) in its width;
    /// [`TooLarge`] as for [`built`].
    fn materialize(&self) -> Result<BigUint, TooLarge> {
        let pows = built(&self.pows)?.into_parts().1;
        Ok(fast::mul(&self.coef, &pows))
    }

    /// The widest exponent, in bits.
    fn exp_bits(&self) -> u64 {
        self.pows.iter().map(|(_, e)| e.bits()).max().unwrap_or(0)
    }

    /// A lower bound, or an upper one when `up`, kept to `k` bits.
    fn bound(&self, k: u64, up: bool) -> Bound {
        let mut b = Bound::of(&self.coef, k, up);
        for (p, e) in &self.pows {
            if *p == 2 {
                // `2^e` is a bound exactly: the exponent moves and nothing is rounded or squared.
                b.e += BigInt::from(e.clone());
                continue;
            }
            let base = Bound::exact(BigUint::from(*p));
            let mut power = Bound::exact(BigUint::one());
            for i in (0..e.bits()).rev() {
                power = power.mul(&power, k, up);
                if e.bit(i) {
                    power = power.mul(&base, k, up);
                }
            }
            b = b.mul(&power, k, up);
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
            let bits = u64::from(64 - p.leading_zeros());
            low += e * (bits - 1);
            high += e * bits;
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
/// deterministic": it calls the platform's libm), and no bound of glibc's was at hand (its
/// manual's table of known errors could not be fetched, 2026-11-13), so this is the "few ulps"
/// of the brief, taken large: correctly rounded and the usual libms are within 1 ulp, and a
/// larger allowance only moves a few more pairs on to the exact bounds, at no measurable cost.
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
/// relative `gamma(N - 1) = (N - 1)u / (1 - (N - 1)u)` (Higham, "Accuracy and Stability of
/// Numerical Algorithms", SIAM, 2nd ed. 2002, sec. 4.2). So `|S' - S| <= B S` with
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

/// The order of two positive products. The system is asked for the memory of each precision
/// before it is tried, `8k` bits for what a round holds at once (four `k`-bit bounds and the
/// `2k`-bit product of two, with room to spare), and for the two products in full before they
/// are built; [`TooLarge`] when it refuses. This holds for every caller, the [`Ord`] of `Rat`
/// with no `Watch` and `Rat::integer_text` among them: a pair close enough to reach a
/// precision, or a build, past the free memory is refused and not built, where the build with
/// no ask aborted the process (NUM-huge-div).
pub(super) fn cmp(n: &Product<'_>, d: &Product<'_>) -> Result<Ordering, TooLarge> {
    // Complexity tradeoff (LIT-power-values): the order is tried first from the bit lengths in
    // exact integer arithmetic ([`by_bit_length`]), then from `log2` of each side in `f64` with
    // a proved error bound ([`by_logs`]), each O(terms) word operations for exponents of a
    // word, and only then from the `k`-bit bounds below, whose first round costs `2 log e`
    // products of about `64 + log2 e` bits. So `1 < 3^200000` and `2^200000 < 3^200000` cost a
    // few word operations, and only two sides within a relative `2^-45` or so in `log2` reach
    // the bounds. The f64 check was the author's addition (2026-11-13); the alternative of the
    // bounds alone was already free of the digits, at O(log^2 e) word operations.
    if let Some(o) = by_bit_length(n, d).or_else(|| by_logs(n, d, 1.0)) {
        return Ok(o);
    }
    let cost = n.bits() + d.bits();
    let mut k = start(n, d);
    loop {
        // Complexity tradeoff: two products that agree in their first `k` bits are told apart
        // by doubling `k`, and once `k` reaches the size of the products themselves they are
        // built and compared, at a cost proportional to their size, the cost of the
        // materializing comparison this replaces; no input is refused. Bounds stop separating
        // only when the two numbers agree in about `k` leading bits, as `2^a 5^b` and
        // `3^c 7^d` with `a log 2 + b log 5` close to `c log 3 + d log 7`. Tested by
        // `close_products_compare_exactly` (COMPLEXITY.md K30). A complete solution would bound
        // `|log N - log D|` from below by Baker's theorem on linear forms in logarithms and
        // stop at the precision it names, which is polynomial in the exponents' bits.
        // Complexity tradeoff: each ask is one allocation of the size asked, given and freed
        // at once (`room`), O(1) beside the round or the build it comes before, which costs
        // at least its size; the alternative of asking only under a `Watch` left an unwatched
        // comparison to abort the process on a precision or a build the system cannot give.
        if BigUint::from(k) >= cost {
            room(cost.clone(), cost)?;
            return Ok(n.materialize()?.cmp(&d.materialize()?));
        }
        room(BigUint::from(k) << 1u32, BigUint::from(k) << 3u32)?;
        let (nl, nu) = (n.bound(k, false), n.bound(k, true));
        let (dl, du) = (d.bound(k, false), d.bound(k, true));
        if nl.cmp(&du) == Ordering::Greater {
            return Ok(Ordering::Greater);
        }
        if nu.cmp(&dl) == Ordering::Less {
            return Ok(Ordering::Less);
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
}
