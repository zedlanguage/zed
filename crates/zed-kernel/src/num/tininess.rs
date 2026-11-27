//! Underflow with tininess detected before rounding (DESIGN.md sec:failure, the `underflow()`
//! fact and the `@checked` float atom `#underflow`; plan row FLOAT-underflow-tininess, study
//! STUDY-ieee754-2019): the one test that the `underflow()` transfer of FPWARN and the run-time
//! `#underflow` of CHECKED-float share, for every operation and every format.
//!
//! IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, 7.5 "Underflow" (read in the 2019 text
//! of study STUDY-ieee754-2019, as quoted in DESIGN.md sec:failure, checked 2026-11-26): "The
//! implementer shall choose how tininess is detected, but shall detect tininess in the same way
//! for all operations in radix two". The rest is written here from memory of 7.5 in the 2008
//! text and was not checked against the 2019 text: tininess before rounding is a nonzero
//! result, computed as though both the exponent range and the precision were unbounded, lying
//! strictly between `±b^emin`; under default exception handling underflow is signaled when the
//! result is tiny and also inexact. DESIGN.md sec:failure says the same in its own words ("a
//! nonzero exact result whose magnitude is below the smallest normal of the format and which
//! rounds"), so the code follows DESIGN.md. DESIGN.md chose before rounding, since it depends on
//! the exact result alone. So the test is
//!
//! `underflow(v)  <=>  v != 0  and  |v| < 2^emin  and  v is not a float of the format`,
//!
//! `emin = 1 - emax` (IEEE 3.3, "emin shall be 1 − emax for all formats"). No rounding mode
//! enters it, and neither does the rounded result: it is decided by the exact result, which the
//! callers have from the operands (an exact product of two floats, [`product_underflows`]; an
//! exact rational, [`exact_underflows`]). The row's text says "from an operation's operands and
//! rounded result"; the rounded result is not needed, since the operands decide the exact
//! result, and reading it would only add a way to be wrong.
//!
//! Why "not a float" is "not a multiple of `2^tiny`", `tiny = emin - p + 1` the exponent of the
//! least subnormal's bit ([`FloatFormat::tiny`]), for a tiny `v`. (1) Every float `f` with
//! `0 < |f| < 2^emin` is a subnormal, `k * 2^tiny` with `0 < k < 2^(p - 1)` (the encoding with
//! exponent field 0, IEEE 3.4, from memory; `float_text.rs` `decode` reads it so), so a
//! tiny float is a multiple of `2^tiny`. (2) Conversely, a multiple `k * 2^tiny` with
//! `0 < |k * 2^tiny| < 2^emin` has `0 < |k| < 2^(emin - tiny) = 2^(p - 1)`, which is the
//! subnormal of significand `|k|`. So a tiny `v` is exact iff `v * 2^-tiny` is an integer. This
//! is also why a sum or difference never underflows [Hauser96] (DESIGN.md sec:failure): both
//! operands are multiples of `2^tiny`, so their exact sum is one too.
//!
//! Tests: `tininess::tests`, below. `every_f16_product_pair` decides every pair of finite `f16`
//! operands and compares it with the exact product read in `f64` (exact: 22 significand bits
//! and exponents far inside `f64`'s); `rat_agrees_on_drawn_f16_pairs` compares
//! [`product_underflows`] with [`exact_underflows`] on the exact `rat` product of drawn pairs
//! near the least normal; the boundary cases of DESIGN.md and CHECKED-float are named one by
//! one. They catch a wrong boundary (`<` for `<=`, the least normal taken as tiny), a wrong
//! grid (the least normal's bit in place of the least subnormal's), and a test after rounding
//! (`(1 - 2^-53) * 2^-1022`). They cannot catch a caller that passes the rounded result in
//! place of the exact one.

use super::float_text::decode;
use super::{FloatFormat, Rat, TooLarge};
use num_bigint::BigInt;
use num_traits::One;
use std::cmp::Ordering;

/// Whether the exact value `m * 2^e` underflows in `format`, tininess before rounding: it is
/// not zero, below `2^emin` in magnitude, and not a multiple of `2^tiny` (proof in the module
/// comment). `m.bit_len() + e <= emin` says `m * 2^e < 2^emin`, since
/// `2^(bit_len - 1) <= m < 2^bit_len`; `trailing_zeros(m) + e < tiny` says it is not a multiple
/// of `2^tiny`, since the largest power of two dividing `m * 2^e` is `2^(tz + e)`.
pub fn dyadic_underflows(format: FloatFormat, m: u128, e: i64) -> bool {
    if m == 0 {
        return false;
    }
    let emin = 1 - format.emax();
    let bit_len = i64::from(u128::BITS - m.leading_zeros());
    bit_len + e <= emin && i64::from(m.trailing_zeros()) + e < format.tiny()
}

/// The encoding `bits` of `format` (sign bit included, in the low `width` bits) as
/// `(m, e)` with `|x| = m * 2^e`; `None` for an infinity or a NaN.
fn finite(bits: u64, format: FloatFormat) -> Option<(u64, i64)> {
    let sign = 1u64 << (format.width() - 1);
    let magnitude = bits & (sign - 1);
    // The exponent field all ones is an infinity or a NaN (IEEE 754-2019 3.4, from memory of
    // the encoding, which `value.rs` `F64::NAN_BITS` and Rust's `f64::to_bits` also follow).
    // `(sign - 1) >> fraction_bits` is the exponent field with every bit set.
    let fraction_bits = format.precision() - 1;
    match magnitude >> fraction_bits == (sign - 1) >> fraction_bits {
        true => None,
        false => Some(decode(magnitude, format)),
    }
}

/// Whether the product of the floats `x` and `y`, given as encodings of `format`, underflows
/// in `format` ([`dyadic_underflows`] of the exact product). The exact product of two
/// significands of at most 53 bits fits a `u128`, and its exponent is the sum of the two, so
/// nothing is rounded on the way. An infinite or NaN operand gives `false`: the product is an
/// infinity or a NaN, never tiny.
///
/// Examples, `f64` (DESIGN.md sec:failure; plan rows FLOAT-underflow-tininess, CHECKED-float):
/// `(1 - 2^-53) * 2^-1022` underflows though it rounds to `2^-1022`; `1.0 * 2^-1022` and
/// `0.5 * 2^-1022` (an exact subnormal) do not; `1e-200 * 1e-200`, `5e-324 * 0.5` and
/// `1e-310 * 0.7` do.
pub fn product_underflows(format: FloatFormat, x: u64, y: u64) -> bool {
    match (finite(x, format), finite(y, format)) {
        (Some((mx, ex)), Some((my, ey))) => {
            dyadic_underflows(format, u128::from(mx) * u128::from(my), ex + ey)
        }
        _ => false,
    }
}

/// Whether the exact rational `v` underflows in `format`: the result of any operation whose
/// exact value is a `rat` (a quotient, a cast of an `int` or a `rat` to a float, `f32(1e-50)`
/// among them). [`TooLarge`] when the system refuses the memory to compare `v`.
///
/// Complexity tradeoff: none. One comparison with `2^emin` and one product by `2^-tiny`, each
/// on a kept power of two ([`Rat::try_cmp`], [`Rat::mul`]), so a value with a huge kept power
/// is not built.
pub fn exact_underflows(format: FloatFormat, v: &Rat) -> Result<bool, TooLarge> {
    if v.is_zero() {
        return Ok(false);
    }
    let two_to = |k: i64| Rat::extract(BigInt::one(), BigInt::one(), vec![(2, BigInt::from(k))]);
    if v.abs().try_cmp(&two_to(1 - format.emax()))? != Ordering::Less {
        return Ok(false);
    }
    Ok(!v.mul(&two_to(-format.tiny()))?.is_integer())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::seed::Rng;
    use num_traits::Zero;

    /// `x` and `y` as `f64` bits.
    fn f64s(x: f64, y: f64) -> bool {
        product_underflows(FloatFormat::F64, x.to_bits(), y.to_bits())
    }

    /// The exact value `m * 2^e` as a `rat`.
    fn rat(m: u128, e: i64) -> Rat {
        Rat::extract(BigInt::from(m), BigInt::one(), vec![(2, BigInt::from(e))])
    }

    #[test]
    fn the_boundary_cases_of_design() {
        let least_normal = f64::MIN_POSITIVE;
        assert_eq!(least_normal, 2.2250738585072014e-308);
        let below_one = 1.0 - 2f64.powi(-53);
        // Rounds to the least normal, and is still tiny before rounding, and inexact.
        assert_eq!(below_one * least_normal, least_normal);
        assert!(f64s(below_one, least_normal));
        assert!(f64s(least_normal, below_one));
        assert!(f64s(-below_one, least_normal));
        assert!(!f64s(1.0, least_normal));
        assert!(!f64s(0.5, least_normal));
        assert!(!f64s(0.0, least_normal));
        assert!(!f64s(f64::INFINITY, least_normal));
        assert!(!f64s(f64::NAN, 0.5));
        // CHECKED-float's `#underflow` cases, and its two that give none.
        assert!(f64s(1e-200, 1e-200));
        assert!(f64s(5e-324, 0.5));
        assert!(f64s(1e-310, 0.7));
        assert!(!f64s(0.5, 2.2250738585072014e-308));
        // A product in the subnormal range that is exact: 3 * 2^-1074 * 2.
        assert!(!f64s(3.0 * 5e-324, 2.0));
        assert!(f64s(3.0 * 5e-324, 0.5));
    }

    #[test]
    fn a_cast_reads_the_exact_rational() {
        // `f32(1e-50)` is `0.0` with `underflow()` (DESIGN.md sec:failure).
        let tiny = Rat::decimal("1e-50").expect("memory").expect("a decimal");
        assert!(exact_underflows(FloatFormat::F32, &tiny).expect("memory"));
        assert!(!exact_underflows(FloatFormat::F64, &tiny).expect("memory"));
        // The least subnormal of `f32`, exact; a third of the least normal, not dyadic.
        assert!(!exact_underflows(FloatFormat::F32, &rat(1, -149)).expect("memory"));
        let third = rat(1, -126)
            .div(&Rat::int(BigInt::from(3)))
            .expect("memory");
        assert!(exact_underflows(FloatFormat::F32, &third.expect("nonzero")).expect("memory"));
        assert!(!exact_underflows(FloatFormat::F32, &rat(1, -126)).expect("memory"));
        assert!(!exact_underflows(FloatFormat::F32, &Rat::int(BigInt::zero())).expect("memory"));
        // A huge kept power of two, below every format's least normal and off its grid.
        let far = rat(3, -(1i64 << 40));
        for format in [
            FloatFormat::F64,
            FloatFormat::F32,
            FloatFormat::F16,
            FloatFormat::BF16,
        ] {
            assert!(exact_underflows(format, &far).expect("memory"));
            assert!(exact_underflows(format, &far.neg()).expect("memory"));
            // Three least subnormals: tiny and exact.
            assert!(!exact_underflows(format, &rat(3, format.tiny())).expect("memory"));
        }
    }

    /// Every pair of finite `f16` operands, both signs of the result by symmetry (the test
    /// reads magnitudes only) and both orders by the commutativity of the product of
    /// significands, compared with the exact product read in `f64`: tiny when below `2^-14`,
    /// exact when `p * 2^24` is whole. The `f64` product is exact, 22 bits of significand at
    /// most and exponents within `-48..=32`.
    #[test]
    fn every_f16_product_pair() {
        let values: Vec<(u64, f64)> = (0..0x7c00u64)
            .map(|bits| {
                let (m, e) = decode(bits, FloatFormat::F16);
                (bits, m as f64 * 2f64.powi(e as i32))
            })
            .collect();
        let least_normal = 2f64.powi(-14);
        let grid = 2f64.powi(24);
        let mut tiny = 0u64;
        for (i, &(x, fx)) in values.iter().enumerate() {
            for &(y, fy) in &values[i..] {
                let p = fx * fy;
                let want = p != 0.0 && p < least_normal && (p * grid).fract() != 0.0;
                let got = product_underflows(FloatFormat::F16, x, y);
                assert_eq!(got, want, "f16 bits {x:#06x} * {y:#06x}");
                tiny += u64::from(got);
            }
        }
        // Not vacuous: a fifth of the pairs or so lie in the band.
        assert!(tiny > 1_000_000, "{tiny}");
        // The sign bit is ignored.
        assert!(product_underflows(FloatFormat::F16, 0x8001, 0x3800));
        assert!(!product_underflows(FloatFormat::F16, 0x8002, 0x3800));
        assert!(!product_underflows(FloatFormat::F16, 0x7c00, 0x0001));
    }

    /// The exact `rat` product of drawn `f16` pairs whose product lies near the least normal
    /// agrees with [`product_underflows`]: the two paths share no arithmetic.
    #[test]
    fn rat_agrees_on_drawn_f16_pairs() {
        let (mut mix, seed) = Rng::fresh("rat_agrees_on_drawn_f16_pairs");
        let mut both = [0u32; 2];
        for _ in 0..20_000 {
            let x = mix.below(0x7c00) as u64;
            let (mx, ex) = decode(x, FloatFormat::F16);
            if mx == 0 {
                continue;
            }
            // `y` with `x * y` within a few binades of `2^-14`.
            let top = ex + i64::from(64 - mx.leading_zeros()) - 1;
            let want_top = -14 - top + mix.below(9) as i64 - 6;
            let field = (want_top + 15).clamp(0, 30) as u64;
            let y = (field << 10) | mix.below(1 << 10) as u64;
            let (my, ey) = decode(y, FloatFormat::F16);
            let exact = rat(u128::from(mx), ex)
                .mul(&rat(u128::from(my), ey))
                .expect("memory");
            let by_rat = exact_underflows(FloatFormat::F16, &exact).expect("memory");
            assert_eq!(
                product_underflows(FloatFormat::F16, x, y),
                by_rat,
                "seed {seed}: f16 bits {x:#06x} * {y:#06x}"
            );
            both[usize::from(by_rat)] += 1;
        }
        assert!(both[0] > 1000 && both[1] > 1000, "seed {seed}: {both:?}");
    }

    /// `bf16` and `f32` share `f32`'s exponents; the least normal times `1 - 2^-p` is tiny and
    /// inexact in each, and the least normal times one half is exact.
    #[test]
    fn each_format_has_its_own_grid() {
        for (format, least_normal, below_one) in [
            (FloatFormat::F32, 0x0080_0000u64, 0x3f7f_ffffu64),
            (FloatFormat::BF16, 0x0080, 0x3f7f),
            (FloatFormat::F16, 0x0400, 0x3bff),
        ] {
            let half = match format {
                FloatFormat::F32 => 0x3f00_0000,
                FloatFormat::BF16 => 0x3f00,
                _ => 0x3800,
            };
            assert!(
                product_underflows(format, below_one, least_normal),
                "{format:?}"
            );
            assert!(
                !product_underflows(format, half, least_normal),
                "{format:?}"
            );
            // The least normal squared is far below the least subnormal: tiny and inexact.
            assert!(
                product_underflows(format, least_normal, least_normal),
                "{format:?}"
            );
        }
    }
}
