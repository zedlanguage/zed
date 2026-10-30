//! Exact numbers (step L1.17): unbounded integers, rationals, and the order of numbers by
//! value across `int`, `rat` and floats (DESIGN.md sec:keys, the natural order).
//!
//! The semantic `int` is unbounded (sec:numeric). An integer inside the 64-bit range is a
//! [`Value::Int`](crate::Value::Int); one outside it is a `Value::Big`, so every integer has
//! one representation and the fast path stays a machine word. A [`Rat`] is reduced, with a
//! positive denominator, so equal rationals are equal values.

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// The largest integer the evaluator builds, in bits: beyond it an operation is
/// [`KernelError::Overflow`](crate::KernelError::Overflow), a limit of the evaluator's memory
/// and not of the language.
pub const MAX_BITS: u64 = 1 << 20;

/// A rational number, reduced, with a positive denominator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rat {
    num: BigInt,
    den: BigInt,
}

impl Rat {
    /// `num / den`, reduced; `None` when `den` is zero.
    pub fn new(num: BigInt, den: BigInt) -> Option<Self> {
        if den.is_zero() {
            return None;
        }
        let g = num.gcd(&den);
        let sign = if den.is_negative() { -1 } else { 1 };
        Some(Rat {
            num: sign * (num / &g),
            den: sign * (den / g),
        })
    }

    /// The integer `n` as a rational.
    pub fn int(n: BigInt) -> Self {
        Rat {
            num: n,
            den: BigInt::one(),
        }
    }

    /// The exact value of a decimal literal's text, such as `0.1` or `2.5e-3`; `None` when
    /// it is beyond [`MAX_BITS`].
    pub fn decimal(text: &str) -> Option<Self> {
        let (mantissa, exp) = match text.find(['e', 'E']) {
            Some(i) => (&text[..i], text[i + 1..].parse::<i64>().ok()?),
            None => (text, 0),
        };
        let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        let digits: BigInt = format!("{whole}{frac}").parse().ok()?;
        let exp = exp.checked_sub(frac.len() as i64)?;
        // 10^e has more than 3e bits.
        if exp.unsigned_abs().saturating_mul(3) > MAX_BITS {
            return None;
        }
        let scale = BigInt::from(10).pow(exp.unsigned_abs() as u32);
        if exp >= 0 {
            Rat::new(digits * scale, BigInt::one())
        } else {
            Rat::new(digits, scale)
        }
    }

    /// The numerator.
    pub fn numer(&self) -> &BigInt {
        &self.num
    }

    /// The denominator, positive.
    pub fn denom(&self) -> &BigInt {
        &self.den
    }

    /// `a + b`.
    pub fn add(&self, b: &Rat) -> Rat {
        Rat::new(&self.num * &b.den + &b.num * &self.den, &self.den * &b.den).expect("den > 0")
    }

    /// `a - b`.
    pub fn sub(&self, b: &Rat) -> Rat {
        self.add(&b.neg())
    }

    /// `a * b`.
    pub fn mul(&self, b: &Rat) -> Rat {
        Rat::new(&self.num * &b.num, &self.den * &b.den).expect("den > 0")
    }

    /// `a / b`; `None` when `b` is zero.
    pub fn div(&self, b: &Rat) -> Option<Rat> {
        Rat::new(&self.num * &b.den, &self.den * &b.num)
    }

    /// `-a`.
    pub fn neg(&self) -> Rat {
        Rat {
            num: -&self.num,
            den: self.den.clone(),
        }
    }

    /// The number of bits of its larger part.
    pub fn bits(&self) -> u64 {
        self.num.bits().max(self.den.bits())
    }
}

impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Written as its literal: `3r`, `-1r/3r`.
impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den.is_one() {
            write!(f, "{}r", self.num)
        } else {
            write!(f, "{}r/{}r", self.num, self.den)
        }
    }
}

/// A number placed on the extended line, for comparing numbers of different kinds.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Exact {
    NegInf,
    Finite(Rat),
    PosInf,
    /// After every number, as the canonical NaN is after `+inf` in a float's total order.
    NaN,
}

impl Exact {
    /// The exact value of a float: every finite double is a dyadic rational.
    pub(crate) fn float(x: f64) -> Exact {
        if x.is_nan() {
            return Exact::NaN;
        }
        if x.is_infinite() {
            return if x > 0.0 {
                Exact::PosInf
            } else {
                Exact::NegInf
            };
        }
        let bits = x.to_bits();
        let exp = ((bits >> 52) & 0x7ff) as i64;
        let frac = bits & ((1 << 52) - 1);
        let (mantissa, exp) = if exp == 0 {
            (frac, -1074)
        } else {
            (frac | (1 << 52), exp - 1075)
        };
        let mut m = BigInt::from(mantissa);
        if bits >> 63 == 1 {
            m = -m;
        }
        let two = BigInt::from(2);
        let r = if exp >= 0 {
            Rat::int(m * two.pow(exp as u32))
        } else {
            Rat::new(m, two.pow((-exp) as u32)).expect("den > 0")
        };
        Exact::Finite(r)
    }
}
