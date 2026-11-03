//! Rigorous bounds on a product of prime powers, for ordering exact numbers and rounding them
//! to floats without building their digits.
//!
//! A bound is `m * 2^e` with `m` kept to `k` bits and `e` unbounded, rounded down for a lower
//! bound and up for an upper one at every step, so it bounds the product whatever `k` is; a
//! larger `k` only makes it tighter. A power `p^e` is bounded by squaring, `2 log e` products
//! of `k`-bit numbers, so `10^(10^9)` costs about 60 products and not its billion digits.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Pow, ToPrimitive, Zero};

use super::LiteralRounding;

/// `coef * prod p^e`, every exponent positive.
pub(super) struct Product {
    pub(super) coef: BigUint,
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

    /// Kept to `k` bits, rounded toward zero, or away from it when `up`.
    fn round(mut self, k: u64, up: bool) -> Bound {
        let bits = self.m.bits();
        if bits <= k {
            return self;
        }
        let drop = bits - k;
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
            m: &self.m * &other.m,
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
            // mantissas' widths.
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
            Some(up) => (
                &self.m << usize::try_from(up).expect("a scaled bound near a float's mantissa"),
                true,
            ),
            None => {
                let down = (-x).to_u64().unwrap_or(u64::MAX);
                if down >= self.m.bits() {
                    return (BigUint::zero(), false);
                }
                let exact = self.m.trailing_zeros().expect("a bound is positive") >= down;
                (&self.m >> down, exact)
            }
        }
    }
}

impl Product {
    /// More than the number of bits of the product: what building it costs.
    fn bits(&self) -> BigUint {
        let mut b = BigUint::from(self.coef.bits());
        for (p, e) in &self.pows {
            b += e * (64 - p.leading_zeros());
        }
        b
    }

    /// The product itself.
    fn materialize(&self) -> BigUint {
        let mut out = self.coef.clone();
        for (p, e) in &self.pows {
            out *= Pow::pow(BigUint::from(*p), e);
        }
        out
    }

    /// The widest exponent, in bits.
    fn exp_bits(&self) -> u64 {
        self.pows.iter().map(|(_, e)| e.bits()).max().unwrap_or(0)
    }

    /// A lower bound, or an upper one when `up`, kept to `k` bits.
    fn bound(&self, k: u64, up: bool) -> Bound {
        let mut b = Bound::exact(self.coef.clone()).round(k, up);
        for (p, e) in &self.pows {
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

/// The first precision tried: a power `p^e` loses about `log2 e` bits to rounding, so this
/// leaves 64 good bits.
fn start(n: &Product, d: &Product) -> u64 {
    64 + n.exp_bits().max(d.exp_bits())
}

/// The order of two positive products.
pub(super) fn cmp(n: &Product, d: &Product) -> Ordering {
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
        if BigUint::from(k) >= cost {
            return n.materialize().cmp(&d.materialize());
        }
        let (nl, nu) = (n.bound(k, false), n.bound(k, true));
        let (dl, du) = (d.bound(k, false), d.bound(k, true));
        if nl.cmp(&du) == Ordering::Greater {
            return Ordering::Greater;
        }
        if nu.cmp(&dl) == Ordering::Less {
            return Ordering::Less;
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
/// `n / d * 2^s` is the integer `w`, which only a near-tie needs.
pub(super) fn round(
    n: &Product,
    d: &Product,
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
            Quotient::Exact {
                n: n.materialize(),
                d: d.materialize(),
            }
        } else {
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
