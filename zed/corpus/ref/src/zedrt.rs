//! Helpers the reference programs share: the Zed rules their outputs depend on.
//!
//! - `fmt_float(x)`: how Zed prints a float: the shortest digits that round-trip, in fixed
//!   notation when the decimal exponent is in -6..<21 (at least one digit on each side of the
//!   point), otherwise one digit, a point, the remaining digits ('0' if none), 'e', and the
//!   exponent ('-' only when negative); special values print inf, -inf, nan.
//! - `fsum(xs)`: a float `+` fold or scan entry is the exact sum rounded once. An exact zero is
//!   0.0, and both inf and -inf, or a finite sum that rounds to an infinity, are errors.
//! - `read_lines(path)`: stdin as Lines, the lines of the input with the final newline not
//!   starting an extra empty line. "\r\n" and "\r" end a line too, and a leading byte order mark
//!   is kept as U+FEFF.
//!
//! Strings compare by code point (sec:order), which is the order of `str`.
//!
//! Where the Zed rule is the same or unstated, the outputs follow these readings of text, kept
//! here so that every program makes them the same way:
//! - `parse_int(s)` / `try_parse_int(s)`: surrounding whitespace, a sign, decimal digits of any
//!   script, '_' between digits; any size, read by halves (`read_digits`).
//! - `parse_float(s)` / `try_parse_float(s)`: the same reading of digits and a decimal float,
//!   and also inf, infinity and nan in any case.
//! - `lower(s)`: the full lowercase mapping (U+0130 becomes "i̇") and the final-sigma rule for
//!   U+03A3.
//! - `is_digit(c)`: a Numeric_Type of Decimal or Digit.
//!
//! The Unicode tables at the end are of Unicode 16.0.

use std::sync::LazyLock;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{ToPrimitive, Zero};

pub mod product;

/// The element of `xs` at `i`, or an error as for an index out of range.
pub fn at<T>(xs: &[T], i: usize) -> Result<&T, String> {
    xs.get(i)
        .ok_or_else(|| format!("index {i} out of range 0..{}", xs.len()))
}

/// How Zed prints `x`.
pub fn fmt_float(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "inf" } else { "-inf" }.into();
    }
    if x == 0.0 {
        return if x.is_sign_negative() { "-0.0" } else { "0.0" }.into();
    }
    let s = if x < 0.0 { "-" } else { "" };
    let sci = format!("{:e}", x.abs());
    let (mantissa, exp) = sci.split_once('e').expect("the {:e} format has an e");
    let e10: i32 = exp.parse().expect("the exponent is a number");
    let ds = mantissa.replace('.', "");
    if (-6..21).contains(&e10) {
        if e10 >= 0 {
            let int_len = e10 as usize + 1;
            let kept = int_len.min(ds.len());
            let ip = format!("{:0<int_len$}", &ds[..kept]);
            let fp = if ds.len() > int_len {
                &ds[int_len..]
            } else {
                "0"
            };
            return format!("{s}{ip}.{fp}");
        }
        return format!("{s}0.{}{ds}", "0".repeat((-e10 - 1) as usize));
    }
    let rest = if ds.len() > 1 { &ds[1..] } else { "0" };
    format!("{s}{}.{rest}e{e10}", &ds[..1])
}

/// A float `+` over values that arrive one at a time: the exact sum so far, whose size is fixed by
/// the range of doubles, so an addition does not grow with the number of values.
#[derive(Default)]
pub struct ExactSum {
    nan: bool,
    pos_inf: bool,
    neg_inf: bool,
    /// The sum of the finite values, in units of 2^-1074, the smallest exponent of a double.
    units: BigInt,
}

impl ExactSum {
    /// Adds `x`.
    pub fn add(&mut self, x: f64) {
        if x.is_nan() {
            self.nan = true;
        } else if x.is_infinite() {
            self.pos_inf |= x > 0.0;
            self.neg_inf |= x < 0.0;
        } else if x != 0.0 {
            let (m, e) = decompose(x);
            self.units += BigInt::from(m) << (e + 1074);
        }
    }

    /// The sum rounded once to the nearest double, ties to even.
    pub fn value(&self) -> Result<f64, String> {
        if self.pos_inf && self.neg_inf {
            return Err("-inf + inf in fsum".into());
        }
        if self.nan {
            return Ok(f64::NAN);
        }
        if self.pos_inf {
            return Ok(f64::INFINITY);
        }
        if self.neg_inf {
            return Ok(f64::NEG_INFINITY);
        }
        let r = round(&self.units, -1074);
        if r.is_infinite() {
            return Err("intermediate overflow in fsum".into());
        }
        Ok(r)
    }
}

/// The exact sum of `xs` rounded once to the nearest double, ties to even.
pub fn fsum(xs: impl IntoIterator<Item = f64>) -> Result<f64, String> {
    let mut sum = ExactSum::default();
    for x in xs {
        sum.add(x);
    }
    sum.value()
}

/// Finite `x` as mantissa * 2^exponent.
fn decompose(x: f64) -> (i64, i64) {
    let bits = x.to_bits();
    let biased = ((bits >> 52) & 0x7ff) as i64;
    let fraction = (bits & ((1 << 52) - 1)) as i64;
    let (m, e) = if biased == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1 << 52), biased - 1075)
    };
    (if bits >> 63 == 1 { -m } else { m }, e)
}

/// `sum` * 2^`scale` rounded to the nearest double, ties to even (0.0 for zero).
fn round(sum: &BigInt, scale: i64) -> f64 {
    if sum.is_zero() {
        return 0.0;
    }
    let a = sum.magnitude();
    let mut q = (scale + a.bits() as i64 - 1 - 52).max(-1074); // exponent of the last kept bit
    let mut m = a << (scale - q).max(0) as u64;
    if q > scale {
        let shift = (q - scale) as u64;
        m = a >> shift;
        let rem = a - (&m << shift);
        let half = num_bigint::BigUint::from(1u32) << (shift - 1);
        if rem > half || (rem == half && m.bit(0)) {
            m += 1u32;
        }
    }
    let mut mi = m.to_u64().expect("at most 54 bits are kept");
    if mi == 1 << 53 {
        mi >>= 1;
        q += 1;
    }
    let negative = sum.sign() == Sign::Minus;
    let bits = if mi >= 1 << 52 {
        let biased = q + 52 + 1023;
        if biased >= 0x7ff {
            return if negative {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
        ((biased as u64) << 52) | (mi - (1 << 52))
    } else {
        mi // subnormal: q is -1074
    };
    f64::from_bits(bits | (u64::from(negative) << 63))
}

/// The lines of the input at `path`.
pub fn read_lines(path: &str) -> Result<Vec<String>, String> {
    let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let text = String::from_utf8(bytes).map_err(|e| format!("{path}: {e}"))?;
    let text = text.replace("\r\n", "\n").replace('\r', "\n");
    if text.is_empty() {
        return Ok(Vec::new());
    }
    let text = text.strip_suffix('\n').unwrap_or(&text);
    Ok(text.split('\n').map(String::from).collect())
}

/// `s` read as an integer, or an error.
pub fn parse_int(s: &str) -> Result<BigInt, String> {
    try_parse_int(s).ok_or_else(|| format!("invalid int: {s}"))
}

fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}

/// `s` read as an integer.
pub fn try_parse_int(s: &str) -> Option<BigInt> {
    let t = ascii_digits_and_spaces(s)?;
    let t = t.trim_matches(is_space);
    let body = t.strip_prefix(['+', '-']).unwrap_or(t);
    let bytes = body.as_bytes();
    let well_formed = bytes.first()?.is_ascii_digit()
        && bytes.last()?.is_ascii_digit()
        && bytes.iter().all(|b| b.is_ascii_digit() || *b == b'_')
        && !body.contains("__");
    if !well_formed {
        return None;
    }
    let sign = match t.starts_with('-') {
        true => Sign::Minus,
        false => Sign::Plus,
    };
    Some(BigInt::from_biguint(
        sign,
        read_digits(&body.replace('_', "")),
    ))
}

/// The digits `read_digits` hands to num-bigint whole. The value read does not depend on it.
//
// Complexity tradeoff: a timed crossover of two algorithms with identical results, nothing
// given up: num-bigint's `parse`, O(n^2), up to `LEAF_DIGITS` digits, and the reading by
// halves above. It was `zed_kernel::num::LEAF_DIGITS`, set from the timings in the
// comment there (2026-11-07, item KERNEL-leaf-digits; COMPLEXITY.md, "Crossovers"): leaf 1024
// had the fewest instructions, or tied, at every size from 700 to 10^6 digits but 1,500. Those
// timings used the kernel's products, which are num-bigint's below 1024 words (about 19,700
// digits), so the products the leaf decides between are the same here. Measured here on
// 2026-11-12 (CROSSOVER-bench, `crossover corpus-leaf-digits`, load 41 to 48) over 700 to 10^6
// digits: summed over the sizes, each one's work over the least at that size, 4096 does the
// least (8.08), 1024 1.031 times as much, more than the 1.0004 that repeated runs vary; the
// kernel's own leaf is within that variation of its best there and keeps 1024. To be measured
// again at the Zed port, with the kernel's.
pub const LEAF_DIGITS: usize = 4096;

/// The value of a nonempty text of ASCII decimal digits.
///
/// num-bigint reads a text one machine word of digits at a time into the whole number read so
/// far, O(n^2) for `n` digits. This reads the text in two parts, the low part `LEAF_DIGITS *
/// 2^i` digits long and the high part no longer, and joins them as `high * 10^d + low`, `d =
/// LEAF_DIGITS * 2^i`, with the powers built once by squaring: O(M(n) log n) for the cost M(n) of
/// a product of n digits, the method of `zed_kernel::num::read_digits` (Brent and Zimmermann,
/// Modern Computer Arithmetic, section 1.7). The references do not use the kernel, so the long
/// products are [`product`]'s transform, M(n) = O(n log n), and the reading is O(n log^2 n)
/// (COMPLEXITY.md F38).
///
/// `high * 10^d` is `(high * 5^d) << d`: the power of five has 2.32 bits a digit against 3.32 for
/// the power of ten, so the products and the squarings that build the powers are 30 % shorter,
/// for one shift of the product. A power of at least [`product::KEPT_WORDS`] words that is squared
/// into the next keeps its transform, which gives its square and its products; the last power is
/// used once, so its product goes through [`product::TRANSFORM_WORDS`]'s crossover. The table of
/// twiddle factors is built once, for the longest transform the reading takes, and not at all
/// when it takes none.
fn read_digits(digits: &str) -> BigUint {
    read_digits_by(digits, LEAF_DIGITS)
}

/// [`read_digits`] with texts of at most `leaf` digits read whole, for the crossover benchmark
/// of `LEAF_DIGITS` (crate zed-benches, binary `crossover`). Not for other use.
#[doc(hidden)]
pub fn read_digits_by(digits: &str, leaf: usize) -> BigUint {
    let Some(top) = split_depth(digits.len(), leaf) else {
        return digits.parse().expect("ASCII decimal digits");
    };
    let first = BigUint::from(5u32).pow(leaf as u32);
    // Upper bounds on the bits of the factors: `5^(leaf * 2^i)` has at most `2^i` times
    // the bits of `first`, and a part of `d` digits fewer than 3.322 d bits.
    let first_bits = first.bits();
    let power_bits = |i: usize| first_bits << i;
    let digit_bits = |d: usize| (d as u64 * 3322).div_ceil(1000);
    let top_high = digit_bits(digits.len() - (leaf << top));
    let kept = |i: usize| i < top && power_bits(i).div_ceil(32) >= product::KEPT_WORDS;
    let kept_len = (0..top)
        .filter(|i| kept(*i))
        .map(|i| product::transform_len(power_bits(i), digit_bits(leaf << i)))
        .max();
    let top_len = (power_bits(top).min(top_high).div_ceil(32) >= product::TRANSFORM_WORDS)
        .then(|| product::transform_len(power_bits(top), top_high));
    let roots = kept_len
        .max(top_len)
        .map_or_else(Vec::new, product::twiddles);
    let mut fives = Vec::with_capacity(top + 1);
    let mut power = first;
    for i in 0..top {
        let factor = match kept(i) {
            true => product::Factor::new(power, digit_bits(leaf << i), &roots),
            false => product::Factor::plain(power),
        };
        power = factor.square(&roots);
        fives.push(factor);
    }
    fives.push(product::Factor::plain(power));
    read_parts(digits, &fives, &roots, leaf)
}

/// The `i` for which a text of `len` digits splits into a low part of `leaf * 2^i`
/// digits and a high part of at least one and at most as many; `None` when it is read whole.
fn split_depth(len: usize, leaf: usize) -> Option<usize> {
    (len > leaf).then(|| ((len - 1) / leaf).ilog2() as usize)
}

/// [`read_digits_by`] of a part, `fives[i]` being `5^(leaf * 2^i)`.
fn read_parts(
    digits: &str,
    fives: &[product::Factor],
    roots: &[product::Twiddle],
    leaf: usize,
) -> BigUint {
    let Some(i) = split_depth(digits.len(), leaf) else {
        return digits.parse().expect("ASCII decimal digits");
    };
    let low_digits = leaf << i;
    let (high, low) = digits.split_at(digits.len() - low_digits);
    (fives[i].times(&read_parts(high, fives, roots, leaf), roots) << low_digits)
        + read_parts(low, fives, roots, leaf)
}

/// `s` read as a float, or an error.
pub fn parse_float(s: &str) -> Result<f64, String> {
    try_parse_float(s).ok_or_else(|| format!("invalid float: {s}"))
}

/// Whether `t` is a numeral: `(\d+\.?\d*|\.\d+)(e[+-]?\d+)?`, in either case.
fn is_numeral(t: &str) -> bool {
    let digits = |s: &str| s.bytes().take_while(u8::is_ascii_digit).count();
    let whole = digits(t);
    let mut rest = &t[whole..];
    let mut fraction = 0;
    if let Some(after) = rest.strip_prefix('.') {
        fraction = digits(after);
        rest = &after[fraction..];
    }
    if whole + fraction == 0 {
        return false;
    }
    match rest.strip_prefix(['e', 'E']) {
        None => rest.is_empty(),
        Some(exp) => {
            let exp = exp.strip_prefix(['+', '-']).unwrap_or(exp);
            !exp.is_empty() && digits(exp) == exp.len()
        }
    }
}

/// `s` read as a float.
pub fn try_parse_float(s: &str) -> Option<f64> {
    let t = ascii_digits_and_spaces(s)?;
    let t = t.trim_matches(is_space);
    let bytes = t.as_bytes();
    let digit_at = |i: Option<usize>| i.and_then(|i| bytes.get(i)).is_some_and(u8::is_ascii_digit);
    let bad_mark = (0..bytes.len())
        .filter(|&i| bytes[i] == b'_')
        .any(|i| !digit_at(i.checked_sub(1)) || !digit_at(Some(i + 1)));
    if bad_mark {
        return None;
    }
    let t = t.replace('_', "");
    let (negative, body) = match t.strip_prefix('-') {
        Some(body) => (true, body),
        None => (false, t.strip_prefix('+').unwrap_or(&t)),
    };
    let word = body.to_ascii_lowercase();
    match word.as_str() {
        "inf" | "infinity" => Some(if negative {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        }),
        "nan" => Some(f64::NAN),
        _ if is_numeral(body) => t.parse().ok(),
        _ => None,
    }
}

/// The first step of `parse_int` and `parse_float`: a non-ASCII space becomes ' ', a decimal
/// digit of any script becomes its ASCII digit; any other non-ASCII character (or DEL) makes the
/// text unreadable.
fn ascii_digits_and_spaces(s: &str) -> Option<String> {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        let cp = c as u32;
        if cp < 127 {
            out.push(c);
        } else if in_ranges(&TABLES.spaces, cp) {
            out.push(' ');
        } else {
            out.push(char::from(b'0' + decimal_value(cp)?));
        }
    }
    Some(out)
}

fn decimal_value(c: u32) -> Option<u8> {
    let zeros = &TABLES.decimal_zeros;
    let i = zeros.partition_point(|z| *z <= c).checked_sub(1)?;
    u8::try_from(c - zeros[i]).ok().filter(|d| *d <= 9)
}

/// Whether `c` has a Numeric_Type of Decimal or Digit.
pub fn is_digit(c: char) -> bool {
    in_ranges(&TABLES.digits, c as u32)
}

/// The full lowercase mapping of `s`.
pub fn lower(s: &str) -> String {
    let cs: Vec<u32> = s.chars().map(u32::from).collect();
    let mut out = String::with_capacity(s.len());
    for (i, &c) in cs.iter().enumerate() {
        match c {
            0x3A3 => out.push(if final_sigma(&cs, i) { 'ς' } else { 'σ' }),
            0x130 => out.push_str("i\u{307}"),
            _ => out.push(char::from_u32(lower_of(c)).expect("the table maps to characters")),
        }
    }
    out
}

/// Capital sigma at `i` is final when a cased letter precedes it and none follows it,
/// case-ignorable characters between them skipped (Unicode's Final_Sigma context).
fn final_sigma(cs: &[u32], i: usize) -> bool {
    let cased = |c: &u32| in_ranges(&TABLES.cased, *c);
    let ignorable = |c: &&u32| in_ranges(&TABLES.case_ignorable, **c);
    let before = cs[..i].iter().rev().find(|c| !ignorable(c));
    let after = cs[i + 1..].iter().find(|c| !ignorable(c));
    before.is_some_and(cased) && !after.is_some_and(cased)
}

fn lower_of(c: u32) -> u32 {
    let runs = &TABLES.lower_runs;
    let Some(i) = runs.partition_point(|r| r.start <= c).checked_sub(1) else {
        return c;
    };
    let r = &runs[i];
    if c <= r.end && (c - r.start).is_multiple_of(r.stride) {
        c.checked_add_signed(r.delta)
            .expect("the table maps to characters")
    } else {
        c
    }
}

fn in_ranges(ranges: &[(u32, u32)], c: u32) -> bool {
    let i = ranges.partition_point(|r| r.0 <= c);
    i > 0 && c <= ranges[i - 1].1
}

fn hex(s: &str) -> u32 {
    u32::from_str_radix(s, 16).expect("a table holds hexadecimal numbers")
}

fn parse_ranges(data: &str) -> Vec<(u32, u32)> {
    let range = |f: &str| match f.split_once('-') {
        None => (hex(f), hex(f)),
        Some((a, b)) => (hex(a), hex(b)),
    };
    data.split_whitespace().map(range).collect()
}

/// Each code point start, start + stride, ..., end lower-cases to itself + delta.
struct Run {
    start: u32,
    end: u32,
    stride: u32,
    delta: i32,
}

fn parse_run(f: &str) -> Run {
    let (span, delta) = f.split_once(':').expect("a run has a delta");
    let delta = delta.parse().expect("a delta is a number");
    match span.split_once('-') {
        None => Run {
            start: hex(span),
            end: hex(span),
            stride: 1,
            delta,
        },
        Some((a, rest)) => {
            let (b, stride) = rest.split_once('/').expect("a range run has a stride");
            Run {
                start: hex(a),
                end: hex(b),
                stride: stride.parse().expect("a stride is a number"),
                delta,
            }
        }
    }
}

struct Tables {
    lower_runs: Vec<Run>,
    cased: Vec<(u32, u32)>,
    case_ignorable: Vec<(u32, u32)>,
    digits: Vec<(u32, u32)>,
    decimal_zeros: Vec<u32>,
    spaces: Vec<(u32, u32)>,
}

static TABLES: LazyLock<Tables> = LazyLock::new(|| Tables {
    lower_runs: LOWER_DATA.split_whitespace().map(parse_run).collect(),
    cased: parse_ranges(CASED_DATA),
    case_ignorable: parse_ranges(CASE_IGNORABLE_DATA),
    digits: parse_ranges(DIGIT_DATA),
    decimal_zeros: DECIMAL_DATA.split_whitespace().map(hex).collect(),
    spaces: parse_ranges(SPACE_DATA),
});

// Unicode 16.0 tables; whitespace-separated hexadecimal code points. LOWER_DATA:
// start-end/stride:delta (or start:delta): the lowercase mapping without U+0130 and U+03A3,
// handled above. CASED_DATA: cased characters that are not case-ignorable. CASE_IGNORABLE_DATA:
// case-ignorable characters. DIGIT_DATA: a Numeric_Type of Decimal or Digit. DECIMAL_DATA: the
// zero of each run of ten decimal digits (Numeric_Type Decimal). SPACE_DATA: white space at or
// above U+007F (Bidi_Class WS, B or S, or category Zs).

const LOWER_DATA: &str = "
41-5a/1:32 c0-d6/1:32 d8-de/1:32 100-12e/2:1 132-136/2:1 139-147/2:1 14a-176/2:1 178:-121
179-17d/2:1 181:210 182-184/2:1 186:206 187:1 189-18a/1:205 18b:1 18e:79 18f:202 190:203 191:1
193:205 194:207 196:211 197:209 198:1 19c:211 19d:213 19f:214 1a0-1a4/2:1 1a6:218 1a7:1 1a9:218
1ac:1 1ae:218 1af:1 1b1-1b2/1:217 1b3-1b5/2:1 1b7:219 1b8:1 1bc:1 1c4:2 1c5:1 1c7:2 1c8:1 1ca:2
1cb-1db/2:1 1de-1ee/2:1 1f1:2 1f2-1f4/2:1 1f6:-97 1f7:-56 1f8-21e/2:1 220:-130 222-232/2:1
23a:10795 23b:1 23d:-163 23e:10792 241:1 243:-195 244:69 245:71 246-24e/2:1 370-372/2:1 376:1
37f:116 386:38 388-38a/1:37 38c:64 38e-38f/1:63 391-3a1/1:32 3a4-3ab/1:32 3cf:8 3d8-3ee/2:1
3f4:-60 3f7:1 3f9:-7 3fa:1 3fd-3ff/1:-130 400-40f/1:80 410-42f/1:32 460-480/2:1 48a-4be/2:1
4c0:15 4c1-4cd/2:1 4d0-52e/2:1 531-556/1:48 10a0-10c5/1:7264 10c7:7264 10cd:7264
13a0-13ef/1:38864 13f0-13f5/1:8 1c89:1 1c90-1cba/1:-3008 1cbd-1cbf/1:-3008 1e00-1e94/2:1
1e9e:-7615 1ea0-1efe/2:1 1f08-1f0f/1:-8 1f18-1f1d/1:-8 1f28-1f2f/1:-8 1f38-1f3f/1:-8
1f48-1f4d/1:-8 1f59-1f5f/2:-8 1f68-1f6f/1:-8 1f88-1f8f/1:-8 1f98-1f9f/1:-8 1fa8-1faf/1:-8
1fb8-1fb9/1:-8 1fba-1fbb/1:-74 1fbc:-9 1fc8-1fcb/1:-86 1fcc:-9 1fd8-1fd9/1:-8 1fda-1fdb/1:-100
1fe8-1fe9/1:-8 1fea-1feb/1:-112 1fec:-7 1ff8-1ff9/1:-128 1ffa-1ffb/1:-126 1ffc:-9 2126:-7517
212a:-8383 212b:-8262 2132:28 2160-216f/1:16 2183:1 24b6-24cf/1:26 2c00-2c2f/1:48 2c60:1
2c62:-10743 2c63:-3814 2c64:-10727 2c67-2c6b/2:1 2c6d:-10780 2c6e:-10749 2c6f:-10783 2c70:-10782
2c72:1 2c75:1 2c7e-2c7f/1:-10815 2c80-2ce2/2:1 2ceb-2ced/2:1 2cf2:1 a640-a66c/2:1 a680-a69a/2:1
a722-a72e/2:1 a732-a76e/2:1 a779-a77b/2:1 a77d:-35332 a77e-a786/2:1 a78b:1 a78d:-42280
a790-a792/2:1 a796-a7a8/2:1 a7aa:-42308 a7ab:-42319 a7ac:-42315 a7ad:-42305 a7ae:-42308
a7b0:-42258 a7b1:-42282 a7b2:-42261 a7b3:928 a7b4-a7c2/2:1 a7c4:-48 a7c5:-42307 a7c6:-35384
a7c7-a7c9/2:1 a7cb:-42343 a7cc:1 a7d0:1 a7d6-a7da/2:1 a7dc:-42561 a7f5:1 ff21-ff3a/1:32
10400-10427/1:40 104b0-104d3/1:40 10570-1057a/1:39 1057c-1058a/1:39 1058c-10592/1:39
10594-10595/1:39 10c80-10cb2/1:64 10d50-10d65/1:32 118a0-118bf/1:32 16e40-16e5f/1:32
1e900-1e921/1:34";

const CASED_DATA: &str = "
41-5a 61-7a aa b5 ba c0-d6 d8-f6 f8-1ba 1bc-1bf 1c4-293 295-2af 370-373 376-377 37b-37d 37f 386
388-38a 38c 38e-3a1 3a3-3f5 3f7-481 48a-52f 531-556 560-588 10a0-10c5 10c7 10cd 10d0-10fa
10fd-10ff 13a0-13f5 13f8-13fd 1c80-1c8a 1c90-1cba 1cbd-1cbf 1d00-1d2b 1d6b-1d77 1d79-1d9a
1e00-1f15 1f18-1f1d 1f20-1f45 1f48-1f4d 1f50-1f57 1f59 1f5b 1f5d 1f5f-1f7d 1f80-1fb4 1fb6-1fbc
1fbe 1fc2-1fc4 1fc6-1fcc 1fd0-1fd3 1fd6-1fdb 1fe0-1fec 1ff2-1ff4 1ff6-1ffc 2102 2107 210a-2113
2115 2119-211d 2124 2126 2128 212a-212d 212f-2134 2139 213c-213f 2145-2149 214e 2160-217f
2183-2184 24b6-24e9 2c00-2c7b 2c7e-2ce4 2ceb-2cee 2cf2-2cf3 2d00-2d25 2d27 2d2d a640-a66d
a680-a69b a722-a76f a771-a787 a78b-a78e a790-a7cd a7d0-a7d1 a7d3 a7d5-a7dc a7f5-a7f6 a7fa
ab30-ab5a ab60-ab68 ab70-abbf fb00-fb06 fb13-fb17 ff21-ff3a ff41-ff5a 10400-1044f 104b0-104d3
104d8-104fb 10570-1057a 1057c-1058a 1058c-10592 10594-10595 10597-105a1 105a3-105b1 105b3-105b9
105bb-105bc 10c80-10cb2 10cc0-10cf2 10d50-10d65 10d70-10d85 118a0-118df 16e40-16e7f 1d400-1d454
1d456-1d49c 1d49e-1d49f 1d4a2 1d4a5-1d4a6 1d4a9-1d4ac 1d4ae-1d4b9 1d4bb 1d4bd-1d4c3 1d4c5-1d505
1d507-1d50a 1d50d-1d514 1d516-1d51c 1d51e-1d539 1d53b-1d53e 1d540-1d544 1d546 1d54a-1d550
1d552-1d6a5 1d6a8-1d6c0 1d6c2-1d6da 1d6dc-1d6fa 1d6fc-1d714 1d716-1d734 1d736-1d74e 1d750-1d76e
1d770-1d788 1d78a-1d7a8 1d7aa-1d7c2 1d7c4-1d7cb 1df00-1df09 1df0b-1df1e 1df25-1df2a 1e900-1e943
1f130-1f149 1f150-1f169 1f170-1f189";

const CASE_IGNORABLE_DATA: &str = "
27 2e 3a 5e 60 a8 ad af b4 b7-b8 2b0-36f 374-375 37a 384-385 387 483-489 559 55f 591-5bd 5bf
5c1-5c2 5c4-5c5 5c7 5f4 600-605 610-61a 61c 640 64b-65f 670 6d6-6dd 6df-6e8 6ea-6ed 70f 711
730-74a 7a6-7b0 7eb-7f5 7fa 7fd 816-82d 859-85b 888 890-891 897-89f 8c9-902 93a 93c 941-948 94d
951-957 962-963 971 981 9bc 9c1-9c4 9cd 9e2-9e3 9fe a01-a02 a3c a41-a42 a47-a48 a4b-a4d a51
a70-a71 a75 a81-a82 abc ac1-ac5 ac7-ac8 acd ae2-ae3 afa-aff b01 b3c b3f b41-b44 b4d b55-b56
b62-b63 b82 bc0 bcd c00 c04 c3c c3e-c40 c46-c48 c4a-c4d c55-c56 c62-c63 c81 cbc cbf cc6 ccc-ccd
ce2-ce3 d00-d01 d3b-d3c d41-d44 d4d d62-d63 d81 dca dd2-dd4 dd6 e31 e34-e3a e46-e4e eb1 eb4-ebc
ec6 ec8-ece f18-f19 f35 f37 f39 f71-f7e f80-f84 f86-f87 f8d-f97 f99-fbc fc6 102d-1030 1032-1037
1039-103a 103d-103e 1058-1059 105e-1060 1071-1074 1082 1085-1086 108d 109d 10fc 135d-135f
1712-1714 1732-1733 1752-1753 1772-1773 17b4-17b5 17b7-17bd 17c6 17c9-17d3 17d7 17dd 180b-180f
1843 1885-1886 18a9 1920-1922 1927-1928 1932 1939-193b 1a17-1a18 1a1b 1a56 1a58-1a5e 1a60 1a62
1a65-1a6c 1a73-1a7c 1a7f 1aa7 1ab0-1ace 1b00-1b03 1b34 1b36-1b3a 1b3c 1b42 1b6b-1b73 1b80-1b81
1ba2-1ba5 1ba8-1ba9 1bab-1bad 1be6 1be8-1be9 1bed 1bef-1bf1 1c2c-1c33 1c36-1c37 1c78-1c7d
1cd0-1cd2 1cd4-1ce0 1ce2-1ce8 1ced 1cf4 1cf8-1cf9 1d2c-1d6a 1d78 1d9b-1dff 1fbd 1fbf-1fc1
1fcd-1fcf 1fdd-1fdf 1fed-1fef 1ffd-1ffe 200b-200f 2018-2019 2024 2027 202a-202e 2060-2064
2066-206f 2071 207f 2090-209c 20d0-20f0 2c7c-2c7d 2cef-2cf1 2d6f 2d7f 2de0-2dff 2e2f 3005
302a-302d 3031-3035 303b 3099-309e 30fc-30fe a015 a4f8-a4fd a60c a66f-a672 a674-a67d a67f
a69c-a69f a6f0-a6f1 a700-a721 a770 a788-a78a a7f2-a7f4 a7f8-a7f9 a802 a806 a80b a825-a826 a82c
a8c4-a8c5 a8e0-a8f1 a8ff a926-a92d a947-a951 a980-a982 a9b3 a9b6-a9b9 a9bc-a9bd a9cf a9e5-a9e6
aa29-aa2e aa31-aa32 aa35-aa36 aa43 aa4c aa70 aa7c aab0 aab2-aab4 aab7-aab8 aabe-aabf aac1 aadd
aaec-aaed aaf3-aaf4 aaf6 ab5b-ab5f ab69-ab6b abe5 abe8 abed fb1e fbb2-fbc2 fe00-fe0f fe13
fe20-fe2f fe52 fe55 feff ff07 ff0e ff1a ff3e ff40 ff70 ff9e-ff9f ffe3 fff9-fffb 101fd 102e0
10376-1037a 10780-10785 10787-107b0 107b2-107ba 10a01-10a03 10a05-10a06 10a0c-10a0f 10a38-10a3a
10a3f 10ae5-10ae6 10d24-10d27 10d4e 10d69-10d6d 10d6f 10eab-10eac 10efc-10eff 10f46-10f50
10f82-10f85 11001 11038-11046 11070 11073-11074 1107f-11081 110b3-110b6 110b9-110ba 110bd 110c2
110cd 11100-11102 11127-1112b 1112d-11134 11173 11180-11181 111b6-111be 111c9-111cc 111cf
1122f-11231 11234 11236-11237 1123e 11241 112df 112e3-112ea 11300-11301 1133b-1133c 11340
11366-1136c 11370-11374 113bb-113c0 113ce 113d0 113d2 113e1-113e2 11438-1143f 11442-11444 11446
1145e 114b3-114b8 114ba 114bf-114c0 114c2-114c3 115b2-115b5 115bc-115bd 115bf-115c0 115dc-115dd
11633-1163a 1163d 1163f-11640 116ab 116ad 116b0-116b5 116b7 1171d 1171f 11722-11725 11727-1172b
1182f-11837 11839-1183a 1193b-1193c 1193e 11943 119d4-119d7 119da-119db 119e0 11a01-11a0a
11a33-11a38 11a3b-11a3e 11a47 11a51-11a56 11a59-11a5b 11a8a-11a96 11a98-11a99 11c30-11c36
11c38-11c3d 11c3f 11c92-11ca7 11caa-11cb0 11cb2-11cb3 11cb5-11cb6 11d31-11d36 11d3a 11d3c-11d3d
11d3f-11d45 11d47 11d90-11d91 11d95 11d97 11ef3-11ef4 11f00-11f01 11f36-11f3a 11f40 11f42 11f5a
13430-13440 13447-13455 1611e-16129 1612d-1612f 16af0-16af4 16b30-16b36 16b40-16b43 16d40-16d42
16d6b-16d6c 16f4f 16f8f-16f9f 16fe0-16fe1 16fe3-16fe4 1aff0-1aff3 1aff5-1affb 1affd-1affe
1bc9d-1bc9e 1bca0-1bca3 1cf00-1cf2d 1cf30-1cf46 1d167-1d169 1d173-1d182 1d185-1d18b 1d1aa-1d1ad
1d242-1d244 1da00-1da36 1da3b-1da6c 1da75 1da84 1da9b-1da9f 1daa1-1daaf 1e000-1e006 1e008-1e018
1e01b-1e021 1e023-1e024 1e026-1e02a 1e030-1e06d 1e08f 1e130-1e13d 1e2ae 1e2ec-1e2ef 1e4eb-1e4ef
1e5ee-1e5ef 1e8d0-1e8d6 1e944-1e94b 1f3fb-1f3ff e0001 e0020-e007f e0100-e01ef";

const DIGIT_DATA: &str = "
30-39 b2-b3 b9 660-669 6f0-6f9 7c0-7c9 966-96f 9e6-9ef a66-a6f ae6-aef b66-b6f be6-bef c66-c6f
ce6-cef d66-d6f de6-def e50-e59 ed0-ed9 f20-f29 1040-1049 1090-1099 1369-1371 17e0-17e9
1810-1819 1946-194f 19d0-19da 1a80-1a89 1a90-1a99 1b50-1b59 1bb0-1bb9 1c40-1c49 1c50-1c59 2070
2074-2079 2080-2089 2460-2468 2474-247c 2488-2490 24ea 24f5-24fd 24ff 2776-277e 2780-2788
278a-2792 a620-a629 a8d0-a8d9 a900-a909 a9d0-a9d9 a9f0-a9f9 aa50-aa59 abf0-abf9 ff10-ff19
104a0-104a9 10a40-10a43 10d30-10d39 10d40-10d49 10e60-10e68 11052-1105a 11066-1106f 110f0-110f9
11136-1113f 111d0-111d9 112f0-112f9 11450-11459 114d0-114d9 11650-11659 116c0-116c9 116d0-116e3
11730-11739 118e0-118e9 11950-11959 11bf0-11bf9 11c50-11c59 11d50-11d59 11da0-11da9 11f50-11f59
16130-16139 16a60-16a69 16ac0-16ac9 16b50-16b59 16d70-16d79 1ccf0-1ccf9 1d7ce-1d7ff 1e140-1e149
1e2f0-1e2f9 1e4f0-1e4f9 1e5f1-1e5fa 1e950-1e959 1f100-1f10a 1fbf0-1fbf9";

const DECIMAL_DATA: &str = "
30 660 6f0 7c0 966 9e6 a66 ae6 b66 be6 c66 ce6 d66 de6 e50 ed0 f20 1040 1090 17e0 1810 1946 19d0
1a80 1a90 1b50 1bb0 1c40 1c50 a620 a8d0 a900 a9d0 a9f0 aa50 abf0 ff10 104a0 10d30 10d40 11066
110f0 11136 111d0 112f0 11450 114d0 11650 116c0 116d0 116da 11730 118e0 11950 11bf0 11c50 11d50
11da0 11f50 16130 16a60 16ac0 16b50 16d70 1ccf0 1d7ce 1d7d8 1d7e2 1d7ec 1d7f6 1e140 1e2f0 1e4f0
1e5f1 1e950 1fbf0";

const SPACE_DATA: &str = "
85 a0 1680 2000-200a 2028-2029 202f 205f 3000";
