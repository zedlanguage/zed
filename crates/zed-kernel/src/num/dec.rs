//! Signed integers held as their decimal digits: the exponent written in a decimal literal, the
//! `N` of `1eNr`, kept as written (DESIGN.md sec:domains, "Kept powers", and step L1.17b).
//!
//! Complexity tradeoff (plan rows KEPT-power-form and PERF-rat-literal-text-length): reading
//! `n` decimal digits into binary and writing them back each cost O(M(n) log n), O(n log^2 n)
//! with the transform products of `fast`, since no radix conversion in O(n log n) is known
//! (the order RADIX-nlog2-10_5 seeks to improve). Held as digits, the operations an exponent
//! of a literal meets cost O(n) each: reading and printing the text, comparing two, adding or
//! subtracting two, multiplying by one word, and a residue or a modular power, by schoolbook
//! digit loops (D. E. Knuth, "The Art of Computer Programming", vol. 2, 3rd ed., 1997,
//! section 4.3.1, Algorithms A (addition), S (subtraction) and M (multiplication) in radix
//! `b`, here `b = 10`; the method is the schoolbook one, cited for its cost, O(n) for A and S
//! and O(n m) for M with an `m`-digit multiplier, here `m = 1` word). The cost given up is a
//! constant factor of about 3.3 in memory (one byte a digit where binary holds 3.32 bits) and
//! the conversion, O(n log^2 n), when an operation needs the binary form, such as the product
//! of two wide exponents; [`conversions`] counts those, so a test can show that a literal's
//! checking makes none.

use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use super::fast::{LEAF_DIGITS, read_digits_by};

thread_local! {
    /// The number of conversions between digits and binary made so far by this thread: a test
    /// reads it before and after a check to show that none happened. Per thread, so tests
    /// running beside it do not count; a conversion on another thread of the same check would
    /// not count either (the checker runs a file on the thread that calls it).
    static CONVERSIONS: Cell<usize> = const { Cell::new(0) };
}

/// The conversions between decimal digits and binary made so far by this thread
/// ([`Dec::to_bigint`]).
pub fn conversions() -> usize {
    CONVERSIONS.with(Cell::get)
}

fn count() {
    CONVERSIONS.with(|c| c.set(c.get() + 1));
}

/// A signed integer as its decimal digits: `digits` ASCII, most significant first, with no
/// leading zero except the one digit of zero, which is never negative.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Dec {
    negative: bool,
    digits: Box<[u8]>,
}

impl fmt::Debug for Dec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Dec({self})")
    }
}

impl fmt::Display for Dec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negative {
            f.write_str("-")?;
        }
        // The digits are ASCII by construction.
        f.write_str(std::str::from_utf8(&self.digits).expect("ASCII digits"))
    }
}

/// `a + b` on magnitudes, O(len) (Knuth's Algorithm A in radix 10).
fn add_mag(a: &[u8], b: &[u8]) -> Vec<u8> {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(a.len() + 1);
    let mut carry = 0u8;
    for i in 0..a.len() {
        let x = a[a.len() - 1 - i] - b'0';
        let y = if i < b.len() {
            b[b.len() - 1 - i] - b'0'
        } else {
            0
        };
        let s = x + y + carry;
        carry = s / 10;
        out.push(b'0' + s % 10);
    }
    if carry > 0 {
        out.push(b'0' + carry);
    }
    out.reverse();
    out
}

/// `a - b` on magnitudes with `a >= b`, O(len) (Knuth's Algorithm S in radix 10), leading
/// zeros removed.
fn sub_mag(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i8;
    for i in 0..a.len() {
        let x = (a[a.len() - 1 - i] - b'0') as i8;
        let y = if i < b.len() {
            (b[b.len() - 1 - i] - b'0') as i8
        } else {
            0
        };
        let mut d = x - y - borrow;
        borrow = 0;
        if d < 0 {
            d += 10;
            borrow = 1;
        }
        out.push(b'0' + d as u8);
    }
    debug_assert_eq!(borrow, 0, "a >= b");
    while out.len() > 1 && out.last() == Some(&b'0') {
        out.pop();
    }
    out.reverse();
    out
}

/// The order of two magnitudes without leading zeros: by length, then by digits.
fn cmp_mag(a: &[u8], b: &[u8]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}

impl Dec {
    /// The integer of the decimal `digits` (ASCII digits, not empty) with the sign given; the
    /// leading zeros are dropped. O(n).
    pub fn read(negative: bool, digits: &str) -> Dec {
        debug_assert!(!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()));
        let t = digits.trim_start_matches('0');
        let t = if t.is_empty() { "0" } else { t };
        Dec::of(negative, t.as_bytes().into())
    }

    /// The integer of the magnitude `digits` with the sign given, zero never negative.
    fn of(negative: bool, digits: Box<[u8]>) -> Dec {
        let negative = negative && &*digits != b"0";
        Dec { negative, digits }
    }

    /// The integer `x`.
    pub fn from_i128(x: i128) -> Dec {
        Dec::of(x < 0, x.unsigned_abs().to_string().into_bytes().into())
    }

    /// It in binary, converted at O(n log^2 n) and counted in [`conversions`].
    pub fn to_bigint(&self) -> BigInt {
        count();
        let sign = if self.negative {
            Sign::Minus
        } else {
            Sign::Plus
        };
        // The digits are ASCII by construction.
        let text = std::str::from_utf8(&self.digits).expect("ASCII digits");
        BigInt::from_biguint(sign, read_digits_by(text, LEAF_DIGITS))
    }

    /// It as an `i64`, when it fits: at most 19 digits are read, so this is O(1) and no
    /// conversion.
    pub fn to_i64(&self) -> Option<i64> {
        if self.digits.len() > 19 {
            return None;
        }
        // At most 19 ASCII digits fit an `i128`.
        let text = std::str::from_utf8(&self.digits).expect("ASCII digits");
        let m: i128 = text.parse().expect("at most 19 digits");
        (if self.negative { -m } else { m }).to_i64()
    }

    /// Whether it is below 0.
    pub fn is_negative(&self) -> bool {
        self.negative
    }

    /// `-self`, O(n).
    pub fn neg(&self) -> Dec {
        Dec::of(!self.negative, self.digits.clone())
    }

    /// `self + other`, O(n).
    pub fn add(&self, other: &Dec) -> Dec {
        if self.negative == other.negative {
            return Dec::of(self.negative, add_mag(&self.digits, &other.digits).into());
        }
        match cmp_mag(&self.digits, &other.digits) {
            Ordering::Less => Dec::of(other.negative, sub_mag(&other.digits, &self.digits).into()),
            _ => Dec::of(self.negative, sub_mag(&self.digits, &other.digits).into()),
        }
    }

    /// `self - other`, O(n).
    pub fn sub(&self, other: &Dec) -> Dec {
        self.add(&other.neg())
    }

    /// `self + k`, O(n).
    pub fn add_i64(&self, k: i64) -> Dec {
        self.add(&Dec::from_i128(i128::from(k)))
    }

    /// `self * k`, O(n) (Knuth's Algorithm M with a one-word multiplier, in radix 10).
    pub fn mul_u64(&self, k: u64) -> Dec {
        if k == 0 {
            return Dec::from_i128(0);
        }
        let mut out = Vec::with_capacity(self.digits.len() + 20);
        let mut carry = 0u128;
        for &d in self.digits.iter().rev() {
            let s = u128::from(d - b'0') * u128::from(k) + carry;
            out.push(b'0' + (s % 10) as u8);
            carry = s / 10;
        }
        while carry > 0 {
            out.push(b'0' + (carry % 10) as u8);
            carry /= 10;
        }
        out.reverse();
        Dec::of(self.negative, out.into())
    }

    /// `|self| mod m`, `m` not zero, by Horner's rule over blocks of 18 digits, O(n).
    pub fn rem_u64(&self, m: u64) -> u64 {
        let m = u128::from(m);
        let mut r = 0u128;
        for block in self.digits.chunks(18) {
            let mut v = 0u128;
            let mut scale = 1u128;
            for &d in block {
                v = v * 10 + u128::from(d - b'0');
                scale *= 10;
            }
            // `r < m < 2^64` and `scale <= 10^18 < 2^60`, so `r * scale + v < 2^125`.
            r = (r * scale + v) % m;
        }
        r as u64
    }

    /// `base^|self| mod m`, `m` above 1, by left-to-right exponentiation over the decimal
    /// digits: `x^(10 a + d) = (x^a)^10 x^d`, O(n) products modulo `m` (four squarings and at
    /// most two products for the tenth power, and one table lookup for `x^d`).
    pub fn pow_mod(&self, base: u64, m: u64) -> u64 {
        let mul = |a: u64, b: u64| zed_numtheory::mul_mod(a, b, m);
        let mut table = [1u64 % m; 10];
        for d in 1..10 {
            table[d] = mul(table[d - 1], base % m);
        }
        let mut r = 1u64 % m;
        for &d in self.digits.iter() {
            let r2 = mul(r, r);
            let r4 = mul(r2, r2);
            let r8 = mul(r4, r4);
            r = mul(mul(r8, r2), table[usize::from(d - b'0')]);
        }
        r
    }
}

impl PartialOrd for Dec {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Dec {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => cmp_mag(&self.digits, &other.digits),
            (true, true) => cmp_mag(&other.digits, &self.digits),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(x: i128) -> Dec {
        Dec::from_i128(x)
    }

    #[test]
    fn small_arithmetic_agrees_with_i128() {
        let xs = [
            0i128,
            1,
            -1,
            9,
            10,
            -10,
            99,
            100,
            999_999_999_999,
            -1_000_000_000_000,
            i64::MAX as i128,
            i64::MIN as i128,
            12_345_678_901_234_567_890,
        ];
        for &a in &xs {
            for &b in &xs {
                assert_eq!(d(a).add(&d(b)), d(a + b), "{a} + {b}");
                assert_eq!(d(a).sub(&d(b)), d(a - b), "{a} - {b}");
                assert_eq!(d(a).cmp(&d(b)), a.cmp(&b), "{a} cmp {b}");
            }
            for k in [0u64, 1, 2, 7, 10, u64::MAX] {
                if let Some(p) = a.checked_mul(i128::from(k)) {
                    assert_eq!(d(a).mul_u64(k), d(p), "{a} * {k}");
                }
            }
            for m in [2u64, 7, 10, (1 << 61) - 1, (1 << 61) - 2, u64::MAX] {
                assert_eq!(
                    i128::from(d(a).rem_u64(m)),
                    a.abs() % i128::from(m),
                    "{a} mod {m}"
                );
            }
            assert_eq!(d(a).to_i64(), i64::try_from(a).ok(), "{a} as i64");
            assert_eq!(d(a).to_string(), a.to_string());
        }
    }

    #[test]
    fn reading_drops_leading_zeros_and_the_sign_of_zero() {
        assert_eq!(Dec::read(false, "000120"), d(120));
        assert_eq!(Dec::read(true, "000"), d(0));
        assert!(!Dec::read(true, "0").is_negative());
        assert_eq!(Dec::read(true, "5").to_string(), "-5");
    }

    #[test]
    fn modular_powers_agree_with_square_and_multiply() {
        let m = (1u64 << 61) - 1;
        for (b, e) in [
            (10u64, 0u64),
            (10, 1),
            (10, 12345),
            (2, 1_000_003),
            (5, 99),
            (7, 61),
        ] {
            let mut want = 1u128;
            let mut x = u128::from(b);
            let mut k = e;
            while k > 0 {
                if k & 1 == 1 {
                    want = want * x % u128::from(m);
                }
                x = x * x % u128::from(m);
                k >>= 1;
            }
            assert_eq!(u128::from(d(i128::from(e)).pow_mod(b, m)), want, "{b}^{e}");
        }
    }

    #[test]
    fn conversions_round_trip_and_are_counted() {
        let text = format!("1{}", "0".repeat(60));
        let x = Dec::read(true, &text);
        let before = conversions();
        let b = x.to_bigint();
        assert_eq!(b, -num_traits::pow(BigInt::from(10u32), 60));
        assert_eq!(conversions(), before + 1);
    }

    #[test]
    fn wide_values_add_and_compare_by_digits() {
        let n = format!("1{}", "0".repeat(1000));
        let x = Dec::read(false, &n);
        let y = x.add_i64(1);
        assert_eq!(y.sub(&x), d(1));
        assert!(y > x && x.neg() > y.neg());
        assert_eq!(x.mul_u64(3).to_string(), format!("3{}", "0".repeat(1000)));
        // Every digit carries: `(10^100 - 1) * (2^64 - 1)`.
        let nines = Dec::read(true, &"9".repeat(100));
        let want = nines.to_bigint() * BigInt::from(u64::MAX);
        assert_eq!(nines.mul_u64(u64::MAX).to_bigint(), want);
    }
}
