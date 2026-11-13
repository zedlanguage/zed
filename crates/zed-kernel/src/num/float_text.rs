//! Float text: reading a decimal literal straight to a binary format, correctly rounded, with no
//! rational built (DESIGN.md sec:domains, step L1.26b), and writing an `f64` as the shortest
//! decimal that reads back to it (sec:reduction).
//!
//! Reading follows Mushtak and Lemire (DESIGN.md \[MushtakLemire23\]). A significand `w` of at
//! most 19 digits times `10^q` is one 64 x 128-bit product with the truncated power of five
//! `POW5[q]`. The paper proves, by the continued-fraction convergents of `POW5[q] / 2^137`, that
//! for `q` outside `-27..=55` the error of the truncation never reaches bit 73 of the product's
//! high 128 bits, so those bits, the 55 that `f64` rounding reads and the fewer that `f32`,
//! `f16` and `bf16` read, are exact and no fallback is needed; `the_truncated_powers_never_carry`
//! repeats that check on this table. Inside that range the product is exact (`q` in `0..=55`),
//! or the value is not a dyadic rational (`q < 0` and `5^-q` does not divide `w`), or it is read
//! exactly in 128 bits. A value read through the product with `q` outside `0..=27` is never a
//! float nor halfway between two: its odd part has a factor `5^q > 2^64`, or it is not dyadic.
//! So rounding it reads the round bit alone; ties occur only in the exact reading, where they
//! go to even.
//!
//! A significand of more than 19 digits is cut to its first 19, `w'`, and `w'` and `w' + 1` are
//! read. When the two round alike, that is the literal's float; otherwise the literal's digits
//! are compared with the decimal digits of the halfway point between the two floats.
//!
//! Writing is Giulietti's Schubfach ("The Schubfach way to render doubles", 2020, as in Java's
//! `DoubleToDecimal`), with its powers of ten taken from the same table, changed for the rule
//! of sec:reduction: the shortest digits, and of two equally near the larger magnitude, where
//! Schubfach takes the even one; and one significant digit where Java asks for two.

use super::LiteralRounding;
use num_bigint::BigUint;
use std::cmp::Ordering;

mod pow5;
use pow5::POW5;

/// A binary floating-point format of IEEE 754 that a literal is read to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatFormat {
    /// binary64: 53 bits of precision, exponents `-1022..=1023`.
    F64,
    /// binary32: 24 bits of precision, exponents `-126..=127`.
    F32,
    /// binary16: 11 bits of precision, exponents `-14..=15`.
    F16,
    /// bfloat16: 8 bits of precision, the exponents of `f32`.
    BF16,
}

impl FloatFormat {
    /// The bits of precision, the leading bit included.
    const fn precision(self) -> i64 {
        match self {
            FloatFormat::F64 => 53,
            FloatFormat::F32 => 24,
            FloatFormat::F16 => 11,
            FloatFormat::BF16 => 8,
        }
    }

    /// The largest exponent of a finite value, which is also the exponent bias.
    const fn emax(self) -> i64 {
        match self {
            FloatFormat::F64 => 1023,
            FloatFormat::F32 | FloatFormat::BF16 => 127,
            FloatFormat::F16 => 15,
        }
    }

    /// Its name, as a type and a literal suffix write it: `f64`, `bf16`.
    pub const fn name(self) -> &'static str {
        match self {
            FloatFormat::F64 => "f64",
            FloatFormat::F32 => "f32",
            FloatFormat::F16 => "f16",
            FloatFormat::BF16 => "bf16",
        }
    }

    /// The width of an encoding in bits.
    pub const fn width(self) -> u32 {
        match self {
            FloatFormat::F64 => 64,
            FloatFormat::F32 => 32,
            FloatFormat::F16 | FloatFormat::BF16 => 16,
        }
    }

    /// The exponent of the last bit of a subnormal.
    const fn tiny(self) -> i64 {
        2 - self.emax() - self.precision()
    }
}

/// The significant digits of a 64-bit significand: `10^19 < 2^64 < 10^20`.
const SIGNIFICAND_DIGITS: i64 = 19;

/// The decimal literal `text`, the parts of it that reading needs.
struct Decimal<'t> {
    negative: bool,
    /// The first `SIGNIFICAND_DIGITS` significant digits; 0 when every digit is 0.
    w: u64,
    /// The literal is about `w * 10^q`, exactly when not `truncated`.
    q: i64,
    /// A nonzero digit follows the digits of `w`.
    truncated: bool,
    /// The digits and point, without the sign and exponent.
    mantissa: &'t [u8],
    /// The literal is `0.d1 d2 d3 ... * 10^point`, the `d` its significant digits.
    point: i64,
}

/// The largest exponent kept as written; any larger rounds every nonzero significand of an
/// accepted text to infinity or zero, whatever the format.
const EXPONENT_LIMIT: i64 = 1 << 40;

/// The parts of `text`, decimal digits with an optional sign, fraction and exponent, the
/// exponent with an optional sign, as [`super::Rat::decimal`] reads them (`1.`, `.5`, `-2e+3`);
/// `None` for any other text. One pass over the text.
fn decimal(text: &str) -> Option<Decimal<'_>> {
    let bytes = text.as_bytes();
    let (negative, start) = match bytes.first() {
        Some(b'-') => (true, 1),
        Some(b'+') => (false, 1),
        _ => (false, 0),
    };
    let digit = |i: usize| {
        bytes
            .get(i)
            .map(|b| b.wrapping_sub(b'0'))
            .filter(|&d| d < 10)
    };
    // Every digit after the leading zeros goes into `w`, wrapping past 19 of them; a longer
    // significand is read again below. `first` is the index of the first significant digit.
    let mut i = start;
    while bytes.get(i) == Some(&b'0') {
        i += 1;
    }
    let mut first = i;
    let mut w = 0u64;
    while let Some(d) = digit(i) {
        w = w.wrapping_mul(10).wrapping_add(u64::from(d));
        i += 1;
    }
    let whole = i - start;
    let mut fraction = 0;
    if bytes.get(i) == Some(&b'.') {
        i += 1;
        let from = i;
        if first == i - 1 {
            while bytes.get(i) == Some(&b'0') {
                i += 1;
            }
            first = i;
        }
        while let Some(d) = digit(i) {
            w = w.wrapping_mul(10).wrapping_add(u64::from(d));
            i += 1;
        }
        fraction = i - from;
    }
    if whole + fraction == 0 {
        return None;
    }
    let end = i;
    // The point lies between `first` and `end` exactly when it was written after a
    // significant digit of the whole part.
    let point_inside = fraction > 0 || bytes.get(end - 1) == Some(&b'.');
    let significant = (end - first - usize::from(point_inside && first < start + whole)) as i64;
    let mut exponent = 0i64;
    if let Some(b'e' | b'E') = bytes.get(i) {
        i += 1;
        let minus = match bytes.get(i) {
            Some(b'-') => {
                i += 1;
                true
            }
            Some(b'+') => {
                i += 1;
                false
            }
            _ => false,
        };
        let from = i;
        while let Some(d) = digit(i) {
            exponent = (exponent * 10 + i64::from(d)).min(EXPONENT_LIMIT);
            i += 1;
        }
        if i == from {
            return None;
        }
        if minus {
            exponent = -exponent;
        }
    }
    if i != bytes.len() {
        return None;
    }
    // The literal is the `significant` digits from `first` times `10^q`. `fraction` and
    // `significant` are at most the text's length, far below `2^62 - EXPONENT_LIMIT`.
    let mut q = exponent - fraction as i64;
    let point = q + significant;
    let mut truncated = false;
    if significant > SIGNIFICAND_DIGITS {
        // Keep the first 19 significant digits; `truncated` when a nonzero one follows.
        w = 0;
        let mut taken = 0;
        for &b in &bytes[first..end] {
            if b == b'.' {
                continue;
            }
            if taken < SIGNIFICAND_DIGITS {
                w = w * 10 + u64::from(b - b'0');
                taken += 1;
            } else if b != b'0' {
                truncated = true;
                break;
            }
        }
        q += significant - SIGNIFICAND_DIGITS;
    }
    Some(Decimal {
        negative,
        w,
        q,
        truncated,
        mantissa: &bytes[start..end],
        point,
    })
}

/// The encoding in `format` of the decimal literal `text` (as `decimal` reads it), correctly
/// rounded to nearest with ties to even; `None` when `text` is not a decimal literal.
/// [`LiteralRounding::Infinite`] when it rounds to infinity and [`LiteralRounding::Zero`] when
/// it rounds to zero while not zero; a zero literal is zero at any exponent (`0e999`).
///
/// Complexity tradeoff: reading the literal's exact rational and rounding it, as before, cost
/// O(n log^2 n) for `n` digits and about 42,000 instructions for a 17-digit literal (std's
/// parser: 404); this is one pass over the text, O(n), and one 64 x 128-bit product, about 530
/// instructions for a 17-digit literal, with a halfway comparison of at most 800 digits of the
/// halfway point (the bound of `f64`) when a literal of more than 19 digits lies between two
/// floats.
pub fn read_float(text: &str, format: FloatFormat) -> Option<Result<u64, LiteralRounding>> {
    let d = decimal(text)?;
    let sign = u64::from(d.negative) << (format.width() - 1);
    Some(match magnitude(&d, format) {
        Ok(bits) => Ok(bits | sign),
        Err(Edge::Infinite) => Err(LiteralRounding::Infinite),
        Err(Edge::Zero) => Err(LiteralRounding::Zero),
    })
}

/// The `f64` written `text`, as IEEE 754 reads it: as [`read_float`] does, but a text that
/// rounds to infinity is infinity and one that rounds to zero is zero, each with the text's
/// sign; `None` when `text` is not a decimal literal.
pub fn read_f64_ieee(text: &str) -> Option<f64> {
    let d = decimal(text)?;
    let x = match magnitude(&d, FloatFormat::F64) {
        Ok(bits) => f64::from_bits(bits),
        Err(Edge::Infinite) => f64::INFINITY,
        Err(Edge::Zero) => 0.0,
    };
    Some(if d.negative { -x } else { x })
}

/// The `f32` written `text`, as IEEE 754 reads it: as [`read_f64_ieee`] does, at `f32`.
pub fn read_f32_ieee(text: &str) -> Option<f32> {
    let d = decimal(text)?;
    let x = match magnitude(&d, FloatFormat::F32) {
        Ok(bits) => f32::from_bits(bits as u32),
        Err(Edge::Infinite) => f32::INFINITY,
        Err(Edge::Zero) => 0.0,
    };
    Some(if d.negative { -x } else { x })
}

/// Why a nonzero literal has no finite encoding: [`LiteralRounding`] without its memory
/// refusal, small enough to come back in registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Edge {
    Infinite,
    Zero,
}

/// The encoding of `|d|` in `format`.
#[inline]
fn magnitude(d: &Decimal<'_>, format: FloatFormat) -> Result<u64, Edge> {
    if d.w == 0 {
        return Ok(0);
    }
    let low = scaled(d.w, d.q, format);
    if !d.truncated {
        return low;
    }
    // The literal lies strictly between `w * 10^q` and `(w + 1) * 10^q`, so it rounds as
    // both do when they round alike. `w + 1 <= 10^19 < 2^64`.
    let high = scaled(d.w + 1, d.q, format);
    if low == high {
        return low;
    }
    // Otherwise the two are adjacent, as the interval is narrower than 10^-18 of its ends and
    // any two floats are further apart: `low` is a finite float or zero and `high` the next.
    let (m, e) = match low {
        Ok(bits) => decode(bits, format),
        Err(_) => (0, format.tiny()),
    };
    match compare_halfway(d, 2 * m + 1, e - 1) {
        Ordering::Less => low,
        Ordering::Greater => high,
        Ordering::Equal if m % 2 == 0 => low,
        Ordering::Equal => high,
    }
}

/// `5^k` for `k` in `0..=27`, the powers below `2^64`.
const POW5_SMALL: [u64; 28] = {
    let mut p = [1u64; 28];
    let mut k = 1;
    while k < 28 {
        p[k] = p[k - 1] * 5;
        k += 1;
    }
    p
};

/// The encoding in `format` of `w * 10^q`, `w` not zero.
#[inline]
fn scaled(w: u64, q: i64, format: FloatFormat) -> Result<u64, Edge> {
    // `w < 2^64` and `10^-343 * 2^64 < 2^-1075`, half the least subnormal; `10^309 > 2^1024`.
    if q < -342 {
        return Err(Edge::Zero);
    }
    if q > 308 {
        return Err(Edge::Infinite);
    }
    let k = q.unsigned_abs() as usize;
    if q >= 0 && k < POW5_SMALL.len() {
        // Exact: `w * 5^q < 2^128`; the bits past the top 64, `s` of them, only tell whether
        // the value lies above `n * 2^(q + s)`.
        let n = u128::from(w) * u128::from(POW5_SMALL[k]);
        let s = 64u32.saturating_sub(n.leading_zeros());
        let inexact = n & ((1u128 << s) - 1) != 0;
        return round((n >> s) as u64, q + i64::from(s), inexact, format);
    }
    if q < 0 && k < POW5_SMALL.len() && w.is_multiple_of(POW5_SMALL[k]) {
        return round(w / POW5_SMALL[k], q, false, format);
    }
    let shift = w.leading_zeros();
    let z = high_product(POW5[(q + 342) as usize], w << shift);
    // `floor(q * log2 10)`, that is `q + floor(log2 5^q)`, for `q` in `-342..=324`
    // (`exponent_of_a_power_of_ten`). `POW5[q]` is `5^q * 2^(127 - floor(log2 5^q))`, cut.
    let log2_pow10 = (q * 217_706) >> 16;
    // `w * 10^q` is about `z * 2^(log2_pow10 - 63 - shift)`; the bits from 73 up of `z` are
    // exact, and the value is not a float nor halfway between two (see the module's comment).
    round(
        (z >> 73) as u64,
        log2_pow10 - 63 - i64::from(shift) + 73,
        true,
        format,
    )
}

/// `floor(t * w / 2^64)`, the high 128 bits of the 192-bit product.
fn high_product(t: u128, w: u64) -> u128 {
    let low = (t & u128::from(u64::MAX)) * u128::from(w);
    let high = (t >> 64) * u128::from(w);
    high + (low >> 64)
}

/// The encoding in `format` of `(n + f) * 2^e`, `n` not zero and `0 < f < 1` when `inexact`,
/// else `f = 0`, rounded to nearest with ties to even. When `inexact`, `n` has more bits than
/// the precision, so `f` lies below the round bit.
#[inline]
fn round(n: u64, e: i64, inexact: bool, format: FloatFormat) -> Result<u64, Edge> {
    let p = format.precision();
    let top = e + 63 - i64::from(n.leading_zeros());
    // The exponent of the result's last bit, before rounding.
    let mut last = (top - (p - 1)).max(format.tiny());
    let shift = last - e;
    let mut m = if shift <= 0 {
        // `n` fits in the precision, so `inexact` is false (the readings give 54 bits or more).
        debug_assert!(!inexact, "an inexact reading has a round bit");
        n << -shift
    } else if shift > 64 {
        // `(n + f) * 2^e < 2^(e + 64)`, below half the least subnormal.
        0
    } else {
        let m = n.checked_shr(shift as u32).unwrap_or(0);
        let half = 1u64 << (shift - 1);
        let below = n & (half - 1 + half);
        let up = below > half || (below == half && (inexact || m % 2 == 1));
        m + u64::from(up)
    };
    if m >> p != 0 {
        m >>= 1;
        last += 1;
    }
    if m == 0 {
        return Err(Edge::Zero);
    }
    let fraction_bits = p - 1;
    if m >> fraction_bits == 0 {
        // Subnormal: exponent field 0.
        return Ok(m);
    }
    let exponent = last + fraction_bits;
    if exponent > format.emax() {
        return Err(Edge::Infinite);
    }
    let field = (exponent + format.emax()) as u64;
    Ok(field << fraction_bits | (m & ((1 << fraction_bits) - 1)))
}

/// The positive encoding `bits` in `format` as `m * 2^e`.
fn decode(bits: u64, format: FloatFormat) -> (u64, i64) {
    let fraction_bits = format.precision() - 1;
    let field = (bits >> fraction_bits) as i64;
    let fraction = bits & ((1 << fraction_bits) - 1);
    if field == 0 {
        (fraction, format.tiny())
    } else {
        (
            fraction | 1 << fraction_bits,
            field - format.emax() - fraction_bits,
        )
    }
}

/// How the literal `d` compares with `h * 2^e`, `h` odd and below `2^54`: the literal's digits
/// against the halfway point's. `|e|` is at most 1076, so the point has at most 800 digits.
fn compare_halfway(d: &Decimal<'_>, h: u64, e: i64) -> Ordering {
    // `h * 2^e` is `digits * 10^scale`.
    let (digits, scale) = if e >= 0 {
        (BigUint::from(h) << e as usize, 0)
    } else {
        (
            BigUint::from(h) * BigUint::from(5u32).pow(e.unsigned_abs() as u32),
            e,
        )
    };
    let digits = digits.to_string();
    let point = digits.len() as i64 + scale;
    if d.point != point {
        return d.point.cmp(&point);
    }
    let mut ours = d
        .mantissa
        .iter()
        .copied()
        .filter(|&b| b != b'.')
        .skip_while(|&b| b == b'0');
    for b in digits.bytes() {
        match ours.next().unwrap_or(b'0').cmp(&b) {
            Ordering::Equal => {}
            unequal => return unequal,
        }
    }
    if ours.any(|b| b != b'0') {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// `x` as `String` writes a float (DESIGN.md sec:reduction): the shortest digits that read
/// back to it, of two equally near the larger magnitude, in fixed notation when the decimal
/// exponent is in `-6..<21` (`0.001`, `100.0`, `-2.5`) and with an exponent otherwise
/// (`1.0e21`, `5.0e-324`), so `f64(String(x))` is `x`, bit for bit.
///
/// Complexity tradeoff: the digits came from std's `{:e}` and were rebuilt into this layout,
/// about 5,500 instructions; Schubfach finds them with three 64 x 128-bit products, and the
/// whole costs about 660 instructions. Both are O(1).
pub fn show_f64(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    let sign = if x.is_sign_negative() { "-" } else { "" };
    if x.is_infinite() {
        return format!("{sign}inf");
    }
    if x == 0.0 {
        return format!("{sign}0.0");
    }
    let (f, e) = shortest(x.to_bits() & !(1 << 63), F64_SHAPE);
    show_decimal(sign, f, e)
}

/// `x` as `String` writes an `f32`: as [`show_f64`] does, with the shortest digits that read
/// back to `x` at `f32` (`0.1`, not the `0.10000000149011612` of the `f64` that `x` widens
/// to), so `f32(String(x))` is `x`, bit for bit.
///
/// Complexity tradeoff: showing the widened `f64` would print its longer digits; Schubfach
/// at the `f32` shape costs the same three products as at `f64`. Both are O(1).
pub fn show_f32(x: f32) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    let sign = if x.is_sign_negative() { "-" } else { "" };
    if x.is_infinite() {
        return format!("{sign}inf");
    }
    if x == 0.0 {
        return format!("{sign}0.0");
    }
    let (f, e) = shortest(u64::from(x.to_bits() & !(1 << 31)), F32_SHAPE);
    show_decimal(sign, f, e)
}

/// The text of `f * 10^e` after `sign`, `f` nonzero with no trailing zero, laid out as
/// [`show_f64`] says.
fn show_decimal(sign: &str, f: u64, e: i32) -> String {
    // The digits of `f`, at the end of `digits`.
    let mut digits = [0u8; 20];
    let mut from = digits.len();
    let mut v = f;
    // Two digits for each division.
    while v >= 10 {
        let pair = 2 * (v % 100) as usize;
        from -= 2;
        digits[from..from + 2].copy_from_slice(&PAIRS[pair..pair + 2]);
        v /= 100;
    }
    if v > 0 {
        from -= 1;
        digits[from] = b'0' + v as u8;
    }
    let digits = &digits[from..];
    let len = digits.len() as i32;
    // The exponent of the first digit.
    let exp = e + len - 1;
    // The text: a sign, then `0.`, 5 zeros and 17 digits, or 21 digits and `.0`, or
    // 17 digits, `.` and `e-324`: at most 24 bytes.
    let mut text = [0u8; 32];
    let mut at = 0;
    let mut put = |bytes: &[u8]| {
        text[at..at + bytes.len()].copy_from_slice(bytes);
        at += bytes.len();
    };
    put(sign.as_bytes());
    if (-6..21).contains(&exp) {
        if exp < 0 {
            put(&b"0.00000"[..(1 - exp) as usize]);
            put(digits);
        } else if len <= exp + 1 {
            put(digits);
            put(&b"00000000000000000000"[..(exp + 1 - len) as usize]);
            put(b".0");
        } else {
            let (whole, fraction) = digits.split_at(exp as usize + 1);
            put(whole);
            put(b".");
            put(fraction);
        }
    } else {
        let (first, rest) = digits.split_at(1);
        put(first);
        put(b".");
        put(if rest.is_empty() { b"0" } else { rest });
        put(if exp < 0 { b"e-" } else { b"e" });
        let exp = exp.unsigned_abs();
        let mut power = 100;
        while power > exp {
            power /= 10;
        }
        while power > 0 {
            put(&[b'0' + (exp / power % 10) as u8]);
            power /= 10;
        }
    }
    String::from(std::str::from_utf8(&text[..at]).expect("ASCII text"))
}

/// `00` to `99`, two bytes each.
const PAIRS: &[u8; 200] = b"\
      0001020304050607080910111213141516171819202122232425262728293031323334353637383940414243444546474849\
      5051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899";

/// The layout of a binary format, for Schubfach.
#[derive(Clone, Copy)]
struct Shape {
    /// The bits of the stored significand: 52 for `f64`, 23 for `f32`.
    bits: u32,
    /// The least exponent of the last bit: -1074 for `f64`, -149 for `f32`.
    q_min: i32,
}

impl Shape {
    /// The least significand of a normal number, `2^bits`.
    fn c_min(self) -> u64 {
        1 << self.bits
    }
}

const F64_SHAPE: Shape = Shape {
    bits: 52,
    q_min: -1074,
};
const F32_SHAPE: Shape = Shape {
    bits: 23,
    q_min: -149,
};
/// The low 63 bits.
const MASK_63: u64 = (1 << 63) - 1;

/// The shortest decimal `f * 10^e` that reads back to the positive finite number of encoding
/// `bits` in the format of `shape`, `f` with no trailing zero: Schubfach's `toDecimal`.
fn shortest(bits: u64, shape: Shape) -> (u64, i32) {
    let c_min = shape.c_min();
    let t = bits & (c_min - 1);
    let field = (bits >> shape.bits) as i32;
    if field == 0 {
        return schubfach(shape.q_min, t, shape);
    }
    let c = c_min | t;
    let mq = -shape.q_min + 1 - field;
    // An integer below `2 * c_min` is its own shortest decimal.
    if 0 < mq && mq <= shape.bits as i32 && (c >> mq) << mq == c {
        return without_zeros(c >> mq, 0);
    }
    schubfach(-mq, c, shape)
}

/// Schubfach's `toDecimal(q, c, 0)` for `c * 2^q` in the format of `shape`: the shortest
/// decimal in the rounding interval, and of two equally near, the larger. The 126-bit `g`
/// of the table is more than `f32` needs (Java's `toDecimal(float)` uses 64 bits).
fn schubfach(q: i32, c: u64, shape: Shape) -> (u64, i32) {
    let out = c & 1;
    let cb = c << 2;
    let cbr = cb + 2;
    let (cbl, k) = if c != shape.c_min() || q == shape.q_min {
        (cb - 2, floor_log10_pow2(q))
    } else {
        (cb - 1, floor_log10_three_quarters_pow2(q))
    };
    let h = q + floor_log2_pow10(-k) + 2;
    // Schubfach's `g`, `floor(10^-k * 2^r) + 1` in `[2^125, 2^126)`, from the 128-bit table.
    let g = (POW5[(342 - k) as usize] >> 2) + 1;
    let (g1, g0) = ((g >> 63) as u64, g as u64 & MASK_63);
    let vb = round_odd(g1, g0, cb << h);
    let vbl = round_odd(g1, g0, cbl << h);
    let vbr = round_odd(g1, g0, cbr << h);
    let s = vb >> 2;
    // Java tests `s >= 100`, as its rule keeps two digits.
    if s >= 10 {
        let sp10 = 10 * (s / 10);
        let tp10 = sp10 + 10;
        let upin = vbl + out <= sp10 << 2;
        let wpin = (tp10 << 2) + out <= vbr;
        if upin != wpin {
            return without_zeros(if upin { sp10 } else { tp10 }, k);
        }
    }
    let t = s + 1;
    let uin = vbl + out <= s << 2;
    let win = (t << 2) + out <= vbr;
    if uin != win {
        return without_zeros(if uin { s } else { t }, k);
    }
    // Both are in: the nearer, and of two equally near the larger (Java: the even one).
    without_zeros(if vb < (s + t) << 1 { s } else { t }, k)
}

/// `f * 10^e` with the trailing zeros of `f` moved to `e`.
fn without_zeros(mut f: u64, mut e: i32) -> (u64, i32) {
    while f.is_multiple_of(10) {
        f /= 10;
        e += 1;
    }
    (f, e)
}

/// Schubfach's `rop`: `g * cp / 2^127` for `g = g1 * 2^63 + g0`, rounded to odd.
fn round_odd(g1: u64, g0: u64, cp: u64) -> u64 {
    let x1 = ((u128::from(g0) * u128::from(cp)) >> 64) as u64;
    let y = u128::from(g1) * u128::from(cp);
    let (y0, y1) = (y as u64, (y >> 64) as u64);
    let z = (y0 >> 1) + x1;
    let vbp = y1 + (z >> 63);
    vbp | ((z & MASK_63) + MASK_63) >> 63
}

/// `floor(e * log10 2)`, for `e` in `-1700..=1700` (`schubfach_logarithms_are_exact`).
fn floor_log10_pow2(e: i32) -> i32 {
    ((i64::from(e) * 661_971_961_083) >> 41) as i32
}

/// `floor(log10(3/4 * 2^e))`, for `e` in `-1700..=1700`.
fn floor_log10_three_quarters_pow2(e: i32) -> i32 {
    ((i64::from(e) * 661_971_961_083 - 274_743_187_321) >> 41) as i32
}

/// `floor(e * log2 10)`, for `e` in `-400..=400`.
fn floor_log2_pow10(e: i32) -> i32 {
    ((i64::from(e) * 913_124_641_741) >> 38) as i32
}

#[cfg(test)]
mod tests;
