//! `Approx`: a number to a fixed number of significant bits, as an interval
//! `lo * 2^shift ..= hi * 2^shift` whose ends are rounded outward at every step, so that
//! products of huge powers and their sums can be ordered and rounded without writing them out.
//!
//! DRY-bignum-bound-type (numeric.md group 7): this is zedc-int's `Approx`, moved down, and
//! zed-kernel `num/bound.rs`'s `Bound` (one end, positive, a run for each end) is now its
//! positive use. `Approx` was kept as the more general (signs and sums), and for its power,
//! which keeps the shift out of the squaring loop (PERF-fold-power-of-huge-exponent); `Bound`'s
//! power added a `BigInt` exponent at every squaring. The kernel's memory policy (`room`)
//! stays at the kernel's callers: nothing here asks the system for memory.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::fast::mul_int;

/// The sign of `x`, as a `bool` that holds for values below zero.
pub fn below_zero(x: &BigInt) -> bool {
    x.sign() == Sign::Minus
}

/// `x * 2^sx` against `y * 2^sy`, for magnitudes.
pub fn mag_scaled_cmp(x: &BigUint, sx: &BigInt, y: &BigUint, sy: &BigInt) -> Ordering {
    match (x.bits(), y.bits()) {
        (0, 0) => return Ordering::Equal,
        (0, _) => return Ordering::Less,
        (_, 0) => return Ordering::Greater,
        _ => {}
    }
    let (tx, ty) = (sx + x.bits(), sy + y.bits());
    if tx != ty {
        return tx.cmp(&ty);
    }
    // The totals are equal, so the difference of the shifts is at most the bits of x or y.
    if sx >= sy {
        let d = u64::try_from(&(sx - sy)).expect("at most the bits of y");
        (x << d).cmp(y)
    } else {
        let d = u64::try_from(&(sy - sx)).expect("at most the bits of x");
        x.cmp(&(y << d))
    }
}

/// `x * 2^sx` against `y * 2^sy`.
pub fn scaled_cmp(x: &BigInt, sx: &BigInt, y: &BigInt, sy: &BigInt) -> Ordering {
    match x.sign().cmp(&y.sign()) {
        Ordering::Equal => {}
        o => return o,
    }
    let o = mag_scaled_cmp(x.magnitude(), sx, y.magnitude(), sy);
    if below_zero(x) { o.reverse() } else { o }
}

/// `floor(x / 2^s)` for `s >= 0`. A shift past the bits of `x` gives -1 or 0 without
/// shifting, so `s` may be far larger than `x`.
pub fn floor_shr(x: &BigInt, s: &BigInt) -> BigInt {
    match u64::try_from(s) {
        Ok(s) if s <= x.bits() => x >> s,
        _ => BigInt::from(-i32::from(below_zero(x))),
    }
}

/// `ceil(x / 2^s)` for `s >= 0`.
pub fn ceil_shr(x: &BigInt, s: &BigInt) -> BigInt {
    -floor_shr(&-x, s)
}

/// A value to `bits` bits: it lies in `lo * 2^shift ..= hi * 2^shift`. It is exact when
/// `lo == hi`.
#[derive(Clone, Debug)]
pub struct Approx {
    /// The lower end, scaled by `2^shift`.
    pub lo: BigInt,
    /// The upper end, scaled by `2^shift`.
    pub hi: BigInt,
    /// The power of 2 both ends are scaled by.
    pub shift: BigInt,
}

impl Approx {
    /// `v` itself.
    pub fn exact(v: BigInt) -> Approx {
        Approx {
            lo: v.clone(),
            hi: v,
            shift: BigInt::ZERO,
        }
    }

    /// `v` to `bits` bits: exact when `v` has at most `bits` bits. It reads only the bits it
    /// keeps, so its cost does not grow with the bits of `v`.
    pub fn of(v: &BigInt, bits: u64) -> Approx {
        let have = v.bits();
        if have <= bits {
            return Approx::exact(v.clone());
        }
        let t = have - bits;
        let lo = v >> t;
        let hi = if v.trailing_zeros().is_some_and(|z| z < t) {
            &lo + 1u32
        } else {
            lo.clone()
        };
        Approx {
            lo,
            hi,
            shift: BigInt::from(t),
        }
    }

    /// [`Approx::of`] of a magnitude: it shifts `m` itself and builds a `BigInt` of the kept
    /// bits only, so a wide `m` is not copied in full to make it signed (zed-kernel
    /// `num/bound.rs` bounds each wide coefficient and atom this way at every precision).
    pub fn of_uint(m: &BigUint, bits: u64) -> Approx {
        let have = m.bits();
        if have <= bits {
            return Approx::exact(BigInt::from(m.clone()));
        }
        let t = have - bits;
        let lo = BigInt::from(m >> t);
        // `have > bits >= 0`, so `m` is not zero and has a lowest set bit.
        let hi = if m.trailing_zeros().is_some_and(|z| z < t) {
            &lo + 1u32
        } else {
            lo.clone()
        };
        Approx {
            lo,
            hi,
            shift: BigInt::from(t),
        }
    }

    /// `self / o` for `self >= 0` and `o > 0` (every value of `o` above zero), to `bits` bits.
    /// Proof that it holds the quotient: for `x` in `self` and `y` in `o`, both ends of `o`
    /// positive, `x / y >= self.lo / o.hi` and `x / y <= self.hi / o.lo`; with
    /// `t = bits + bits(o.hi)`, `floor(self.lo 2^t / o.hi)` and `ceil(self.hi 2^t / o.lo)` scaled
    /// by `2^(self.shift - o.shift - t)` round these outward, and [`Approx::truncate`] keeps them
    /// outward. The `t` extra bits keep at least `bits` bits in the quotient of the ends.
    pub fn div_positive(&self, o: &Approx, bits: u64) -> Approx {
        debug_assert!(!below_zero(&self.lo) && o.lo.sign() == Sign::Plus);
        let t = bits + o.hi.bits();
        Approx {
            lo: Integer::div_floor(&(&self.lo << t), &o.hi),
            hi: Integer::div_ceil(&(&self.hi << t), &o.lo),
            shift: &self.shift - &o.shift - t,
        }
        .truncate(bits)
    }

    /// `floor(log2)` of the lower end and of the upper end, for `self > 0`.
    pub fn log2_ends(&self) -> (BigInt, BigInt) {
        debug_assert!(self.lo.sign() == Sign::Plus);
        (
            &self.shift + (self.lo.bits() - 1),
            &self.shift + (self.hi.bits() - 1),
        )
    }

    /// Whether the interval is one value.
    pub fn is_exact(&self) -> bool {
        self.lo == self.hi
    }

    /// Drops the low bits past `bits`, rounding `lo` down and `hi` up.
    pub fn truncate(mut self, bits: u64) -> Approx {
        let have = self.lo.bits().max(self.hi.bits());
        if have <= bits {
            return self;
        }
        let t = have - bits;
        let up = self.hi.trailing_zeros().is_some_and(|z| z < t);
        self.lo >>= t;
        self.hi >>= t;
        if up {
            self.hi += 1u32;
        }
        self.shift += t;
        self
    }

    /// The product, to `bits` bits.
    pub fn mul(&self, o: &Approx, bits: u64) -> Approx {
        let (lo, hi) = if !below_zero(&self.lo) && !below_zero(&o.lo) {
            (mul_int(&self.lo, &o.lo), mul_int(&self.hi, &o.hi))
        } else {
            let mut ps = [
                mul_int(&self.lo, &o.lo),
                mul_int(&self.lo, &o.hi),
                mul_int(&self.hi, &o.lo),
                mul_int(&self.hi, &o.hi),
            ];
            ps.sort();
            let [lo, _, _, hi] = ps;
            (lo, hi)
        };
        Approx {
            lo,
            hi,
            shift: &self.shift + &o.shift,
        }
        .truncate(bits)
    }

    /// The sum, to `bits` bits. When the shifts differ by at most `bits`, the operand with the
    /// larger shift is moved down to the other exactly; otherwise the one with the smaller
    /// shift is rounded outward to the larger, so a small term beside a huge one costs no
    /// more than the huge one's `bits`.
    pub fn add(&self, o: &Approx, bits: u64) -> Approx {
        let (a, b) = if self.shift >= o.shift {
            (self, o)
        } else {
            (o, self)
        };
        let diff = &a.shift - &b.shift;
        match u64::try_from(&diff) {
            Ok(d) if d <= bits => Approx {
                lo: (&a.lo << d) + &b.lo,
                hi: (&a.hi << d) + &b.hi,
                shift: b.shift.clone(),
            },
            _ => Approx {
                lo: &a.lo + floor_shr(&b.lo, &diff),
                hi: &a.hi + ceil_shr(&b.hi, &diff),
                shift: a.shift.clone(),
            },
        }
        .truncate(bits)
    }

    /// The quotient by `den >= 1`, to `bits` bits; exact when `self` is an exact multiple of
    /// `den`.
    pub fn div(self, den: &BigUint, bits: u64) -> Approx {
        if den.is_one() {
            return self;
        }
        let den = BigInt::from(den.clone());
        if self.is_exact() && self.shift.is_zero() && self.lo.is_multiple_of(&den) {
            return Approx::exact(self.lo / den);
        }
        let t = bits + den.bits();
        Approx {
            lo: Integer::div_floor(&(self.lo << t), &den),
            hi: Integer::div_ceil(&(self.hi << t), &den),
            shift: self.shift - t,
        }
        .truncate(bits)
    }

    /// `self ^ exp`, for `self >= 0`, by squaring: `O(bits of exp)` products. Each product
    /// adds a relative error of at most `2^-bits`, and a power multiplies the relative error
    /// by its exponent (to first order; this says only how precise the result is). The result
    /// holds the true power whatever the error: `r` starts exact at 1, and each step is a
    /// [`Approx::mul`] of two intervals of values at least 0, whose ends are the products of
    /// the ends (both `lo` at least 0, so `lo * lo'` is the least product and `hi * hi'` the
    /// greatest), and whose [`Approx::truncate`] rounds `lo` down and `hi` up. So by induction
    /// on the steps, `r.lo * 2^r.shift <= self^e <= r.hi * 2^r.shift` for the exponent `e`
    /// read so far.
    ///
    /// The shift is kept out of the loop (item PERF-fold-power-of-huge-exponent). Squaring an
    /// `Approx` that carried its shift doubled a BigInt of about `b` bits, for the `b` bits of
    /// `exp`, at each of the `b` steps: O(b^2) bit operations for shifts alone, where the ends
    /// stay at `bits` bits. `2 ^ (2^(2^20))` took 11 s in a dev build to fold, all of it in
    /// those additions. Now the ends are computed with shifts of zero, and the shift once at
    /// the end. Proof that the result is the same `Approx`, end for end and shift for shift:
    ///
    /// 1. [`Approx::mul`] and [`Approx::truncate`] read only `lo` and `hi` to compute the new
    ///    `lo`, `hi` and the bits `t` dropped; the shift of the product is the sum of the
    ///    shifts plus `t`. So the ends at every step are those of the loop above whatever the
    ///    shifts, and starting from shifts of zero, each step's product has the shift `t` of
    ///    that step alone, a `u64` since it is at most the bits of the product's ends.
    /// 2. In the loop above, write `s` for `self.shift`, `S_i` for `r.shift` after the step of
    ///    bit `i`, and `c_i` for the bits dropped in that step's square and product together.
    ///    Then `S_i = 2 S_{i+1} + c_i + s * bit_i(exp)`, with `S = 0` above the top bit.
    /// 3. Unrolled from the top bit down to bit 0, each term entered at bit `i` is doubled by
    ///    the `i` squarings below it: `S_0 = sum_i (c_i + s * bit_i(exp)) * 2^i
    ///    = s * exp + sum_i c_i 2^i`.
    /// 4. The sum `sum_i c_i 2^i`, with each `c_i` below `2^64`, is written in one pass from
    ///    bit 0 up with a carry: after position `i` the carry is below `2^65` (by induction:
    ///    `(carry + c_i) / 2 < (2^65 + 2^64) / 2 < 2^65`), so a `u128` holds it.
    ///
    /// Cost: the `b` steps of products of `bits`-bit ends, O(b) words to keep the `c_i`, one
    /// O(b) pass for their sum, and one product `s * exp`: linear in `b` for a fixed `bits`.
    /// Tested by `tests::a_power_keeps_its_shift_out_of_the_loop` (against the loop above,
    /// shifts of zero and not, exact and not, exponents of 0 to 300 bits) and timed by
    /// l01_29 `bench::too_large::folding_a_power_of_a_huge_exponent_scales`. What the test
    /// cannot catch: a `bits` so large that the dropped bits of one step pass `2^64`, which
    /// would need ends of `2^63` bits.
    pub fn pow(&self, exp: &BigUint, bits: u64) -> Approx {
        // Fast path: an exponent of 1, as in the order of two powers with a common root
        // (zed-kernel `bound::common_root`). The loop below takes one squaring of the exact 1,
        // which is 1, and one product of 1 by the base, whose ends are the base's ends (by
        // either branch of `mul`), truncated; steps 3 and 4 then give the shift `s * 1 + t`
        // with `t` the bits that truncation dropped. That is `self.truncate(bits)`, with no
        // product, `dropped` vector or shift multiplication.
        if exp.is_one() {
            return self.clone().truncate(bits);
        }
        let base = Approx {
            lo: self.lo.clone(),
            hi: self.hi.clone(),
            shift: BigInt::ZERO,
        };
        let mut r = Approx::exact(BigInt::from(1u32));
        // Step 1: `dropped[i]` is `c_i`, the bits dropped at bit `i` of `exp`.
        let mut dropped = vec![0u64; usize::try_from(exp.bits()).expect("an exponent in memory")];
        let take = |r: Approx| -> (Approx, u64) {
            let t = u64::try_from(&r.shift).expect("step 1: the bits one product drops");
            (
                Approx {
                    shift: BigInt::ZERO,
                    ..r
                },
                t,
            )
        };
        for i in (0..exp.bits()).rev() {
            let (sq, t) = take(r.mul(&r, bits));
            r = sq;
            let mut c = t;
            if exp.bit(i) {
                let (p, t) = take(r.mul(&base, bits));
                r = p;
                c += t;
            }
            dropped[i as usize] = c;
        }
        // Step 4: `sum_i c_i 2^i`, in 32-bit digits for `BigUint::new`.
        let mut digits = Vec::with_capacity(dropped.len() / 32 + 5);
        let (mut carry, mut digit) = (0u128, 0u32);
        for (i, c) in dropped.iter().enumerate() {
            carry += u128::from(*c);
            digit |= ((carry & 1) as u32) << (i % 32);
            carry >>= 1;
            if i % 32 == 31 {
                digits.push(digit);
                digit = 0;
            }
        }
        if dropped.len() % 32 != 0 {
            digits.push(digit);
        }
        let low = BigUint::new(digits);
        let high = BigUint::from(carry) << dropped.len();
        // Step 3: `s * exp + sum_i c_i 2^i`.
        r.shift = &self.shift * BigInt::from(exp.clone()) + BigInt::from(low + high);
        r
    }

    /// Whether every value in `self` is below every value in `o`.
    pub fn below(&self, o: &Approx) -> bool {
        scaled_cmp(&self.hi, &self.shift, &o.lo, &o.shift) == Ordering::Less
    }

    /// Whether every value in `self` is at most `y * 2^sy`.
    pub fn hi_at_most(&self, y: &BigInt, sy: &BigInt) -> bool {
        scaled_cmp(&self.hi, &self.shift, y, sy) != Ordering::Greater
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A random value `n * 2^s`: `n` of up to `max_bits` bits, of either sign unless `positive`
    /// (then at least 1), and `s` in `-100..=100`.
    fn value(rng: &mut crate::seed::Rng, max_bits: u64, positive: bool) -> (BigInt, BigInt) {
        let bits = 1 + rng.below_u64(max_bits);
        let words: Vec<u32> = (0..bits.div_ceil(32))
            .map(|_| rng.next_u64() as u32)
            .collect();
        let mut n = BigInt::from(BigUint::new(words) >> (bits.div_ceil(32) * 32 - bits));
        if positive {
            n += 1u32;
        } else if rng.next_u64() % 2 == 0 {
            n = -n;
        }
        (n, BigInt::from(rng.below_u64(201) as i64 - 100))
    }

    /// Whether `a` holds `num * 2^s / den` for `den > 0`: `lo * den <= num 2^(s - shift) <=
    /// hi * den`, compared exactly by [`scaled_cmp`].
    fn holds(a: &Approx, num: &BigInt, s: &BigInt, den: &BigInt) -> bool {
        scaled_cmp(&(&a.lo * den), &a.shift, num, s) != Ordering::Greater
            && scaled_cmp(&(&a.hi * den), &a.shift, num, s) != Ordering::Less
    }

    /// Every operation, on random values of both signs (positive for the division and the
    /// logarithms), to 1 to 130 bits, holds the exact result, which is computed in integers:
    /// a value `n * 2^s` against an end `e * 2^shift` by [`scaled_cmp`], and a quotient by
    /// multiplying the end by the divisor. Each result keeps at most `bits + 1` bits; the
    /// quotient of exact operands is at most 2 units of its last place wide.
    #[test]
    fn every_operation_holds_the_exact_result() {
        let (mut rng, seed) = crate::seed::Rng::fresh("every_operation_holds_the_exact_result");
        let one = BigInt::one();
        let narrow = |a: &Approx, bits: u64| a.lo.bits().max(a.hi.bits()) <= bits + 1;
        for case in 0..3000 {
            let bits = 1 + rng.below_u64(130);
            let ((x, sx), (y, sy)) = (value(&mut rng, 300, false), value(&mut rng, 300, false));
            let (a, b) = (Approx::of(&x, bits), Approx::of(&y, bits));
            let (a, b) = (
                Approx {
                    shift: &a.shift + &sx,
                    ..a
                },
                Approx {
                    shift: &b.shift + &sy,
                    ..b
                },
            );
            let at = format!("case {case}, seed {seed}: {x} 2^{sx}, {y} 2^{sy}, {bits} bits");
            assert!(
                holds(&a, &x, &sx, &one) && holds(&b, &y, &sy, &one),
                "of, {at}"
            );
            let p = a.mul(&b, bits);
            assert!(holds(&p, &(&x * &y), &(&sx + &sy), &one), "mul, {at}");
            assert!(narrow(&p, bits), "mul width, {at}");
            let (lo_s, hi_s) = if sx <= sy { (&sx, &sy) } else { (&sy, &sx) };
            let (wide, other) = if sx <= sy { (&y, &x) } else { (&x, &y) };
            let d = u32::try_from(hi_s - lo_s).expect("shifts within 200");
            let sum = (wide << d) + other;
            let q = a.add(&b, bits);
            assert!(holds(&q, &sum, lo_s, &one), "add, {at}");
            assert!(narrow(&q, bits), "add width, {at}");
            if a.below(&b) {
                assert!(
                    scaled_cmp(&x, &sx, &y, &sy) == Ordering::Less,
                    "below, {at}"
                );
            }
            let den = BigUint::from(1 + rng.below_u64(1 << 40));
            let dv = a.clone().div(&den, bits);
            assert!(holds(&dv, &x, &sx, &BigInt::from(den)), "div, {at}");
            let ((m, sm), (n, sn)) = (value(&mut rng, 300, true), value(&mut rng, 300, true));
            let at = format!("case {case}, seed {seed}: {m} 2^{sm} / {n} 2^{sn}, {bits} bits");
            let shifted = |v: &BigInt, s: &BigInt, exact: bool| {
                let a = if exact {
                    Approx::exact(v.clone())
                } else {
                    Approx::of_uint(v.magnitude(), bits)
                };
                Approx {
                    shift: &a.shift + s,
                    ..a
                }
            };
            for exact in [true, false] {
                let (u, v) = (shifted(&m, &sm, exact), shifted(&n, &sn, exact));
                // `m 2^sm / (n 2^sn)` is `m 2^(sm - sn) / n`.
                let r = u.div_positive(&v, bits);
                assert!(holds(&r, &m, &(&sm - &sn), &n), "div_positive, {at}");
                assert!(narrow(&r, bits), "div_positive width, {at}");
                if exact {
                    assert!(
                        &r.hi - &r.lo <= BigInt::from(2u32),
                        "div_positive tight, {at}"
                    );
                }
                let (l0, l1) = u.log2_ends();
                assert_eq!(l0, &u.shift + (u.lo.bits() - 1), "log2_ends, {at}");
                assert!(l0 <= l1, "log2_ends order, {at}");
                if exact {
                    assert_eq!(l0, &sm + (m.bits() - 1), "log2 of an exact value, {at}");
                }
            }
            let o = Approx::of_uint(m.magnitude(), bits);
            let w = Approx::of(&m, bits);
            assert_eq!(
                (&o.lo, &o.hi, &o.shift),
                (&w.lo, &w.hi, &w.shift),
                "of_uint, {at}"
            );
            let e = rng.below_u64(12) as u32;
            let base = Approx::of(&(&m >> (m.bits().saturating_sub(40))), bits);
            let base_v = &m >> (m.bits().saturating_sub(40));
            let pw = base.pow(&BigUint::from(e), bits);
            assert!(
                holds(
                    &pw,
                    &num_traits::pow(base_v.clone(), e as usize),
                    &BigInt::ZERO,
                    &one
                ),
                "pow {e}, {at}"
            );
        }
    }

    /// `x ^ exp` by the loop `Approx::pow` ran before PERF-fold-power-of-huge-exponent, the
    /// shift carried through every step.
    fn pow_carrying_the_shift(x: &Approx, exp: &BigUint, bits: u64) -> Approx {
        let mut r = Approx::exact(BigInt::from(1u32));
        for i in (0..exp.bits()).rev() {
            r = r.mul(&r, bits);
            if exp.bit(i) {
                r = r.mul(x, bits);
            }
        }
        r
    }

    /// `Approx::pow` gives the ends and shift of the loop that carried the shift through every
    /// step: bases exact and not, of shifts zero, positive and negative, to 8, 64 and 200 bits,
    /// and exponents 0 to 40, `2^k`, `2^k - 1` and random ones of up to 300 bits, so that the
    /// dropped bits carry across 32-bit digits and past the top bit of the exponent.
    #[test]
    fn a_power_keeps_its_shift_out_of_the_loop() {
        let (mut rng, _) = crate::seed::Rng::fresh("a_power_keeps_its_shift_out_of_the_loop");
        let mut exps: Vec<BigUint> = (0u32..=40).map(BigUint::from).collect();
        for k in [31u32, 32, 33, 63, 64, 65, 200] {
            exps.push(BigUint::one() << k);
            exps.push((BigUint::one() << k) - 1u32);
        }
        for _ in 0..20 {
            let words: Vec<u32> = (0..10).map(|_| rng.next_u64() as u32).collect();
            exps.push(BigUint::new(words) >> (rng.next_u64() % 320));
        }
        let lo = BigInt::from(3u64 << 61) * 5u32 + 7u32;
        let bases = [
            Approx::exact(BigInt::from(2u32)),
            Approx::exact(BigInt::from(3u32)),
            Approx::exact(lo.clone()),
            Approx {
                lo: lo.clone(),
                hi: &lo + 1u32,
                shift: BigInt::from(17u32),
            },
            Approx {
                lo: lo.clone(),
                hi: &lo + 2u32,
                shift: BigInt::from(-90),
            },
            Approx {
                lo: BigInt::from(1u32),
                hi: BigInt::from(1u32),
                shift: BigInt::one() << 100u32,
            },
        ];
        for x in &bases {
            for bits in [8u64, 64, 200] {
                for e in &exps {
                    let (got, want) = (x.pow(e, bits), pow_carrying_the_shift(x, e, bits));
                    assert_eq!(
                        (&got.lo, &got.hi, &got.shift),
                        (&want.lo, &want.hi, &want.shift),
                        "{x:?} ^ {e} to {bits} bits"
                    );
                }
            }
        }
    }
}
