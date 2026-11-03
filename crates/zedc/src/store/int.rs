//! The solver's integers (DESIGN.md sec:domains, "exact, over unbounded integers"): unbounded,
//! with `i128` arithmetic while a value fits, since nearly all of them do. Zed's `int` is
//! unbounded, so this module goes at the port (ZED_PORT_GAPS.md).

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use num_bigint::{BigInt, Sign};
use num_integer::Integer;

/// An integer. A value that fits in `i128` is always `Small`, so that two equal values have
/// one form.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Repr {
    Small(i128),
    Big(Box<BigInt>),
}

/// An unbounded integer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Int(Repr);

impl Default for Int {
    fn default() -> Int {
        Int::ZERO
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<i64> for Int {
    fn from(v: i64) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Int {
        Int(Repr::Small(v as i128))
    }
}

impl From<i128> for Int {
    fn from(v: i128) -> Int {
        Int(Repr::Small(v))
    }
}

impl From<BigInt> for Int {
    fn from(v: BigInt) -> Int {
        Int(match i128::try_from(&v) {
            Ok(s) => Repr::Small(s),
            Err(_) => Repr::Big(Box::new(v)),
        })
    }
}

impl Int {
    /// Zero.
    pub const ZERO: Int = Int(Repr::Small(0));
    /// One.
    pub const ONE: Int = Int(Repr::Small(1));

    fn big(&self) -> Cow<'_, BigInt> {
        match &self.0 {
            Repr::Small(v) => Cow::Owned(BigInt::from(*v)),
            Repr::Big(v) => Cow::Borrowed(v),
        }
    }

    /// The value, when it fits in `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match self.0 {
            Repr::Small(v) => Some(v),
            Repr::Big(_) => None,
        }
    }

    /// Whether the value is below zero.
    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Big(v) => v.sign() == Sign::Minus,
        }
    }

    /// Whether the value is above zero.
    pub fn is_positive(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v > 0,
            Repr::Big(v) => v.sign() == Sign::Plus,
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.0 == Repr::Small(0)
    }

    /// Whether the value is 1 or -1.
    pub fn is_unit(&self) -> bool {
        matches!(self.0, Repr::Small(1 | -1))
    }

    /// The absolute value.
    pub fn abs(&self) -> Int {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// The greatest common divisor, never negative.
    pub fn gcd(&self, other: &Int) -> Int {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => {
                let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
                while b != 0 {
                    (a, b) = (b, a % b);
                }
                i128::try_from(a).map_or_else(|_| BigInt::from(a).into(), Int::from)
            }
            _ => self.big().gcd(&other.big()).into(),
        }
    }

    /// `self / m` rounded down, for `m` above zero.
    pub fn div_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            (Repr::Small(a), Repr::Small(b)) => a.div_euclid(*b).into(),
            _ => self.big().div_floor(&m.big()).into(),
        }
    }

    /// The remainder of [`Int::div_floor`], for `m` above zero.
    pub fn mod_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            (Repr::Small(a), Repr::Small(b)) => a.rem_euclid(*b).into(),
            _ => self.big().mod_floor(&m.big()).into(),
        }
    }
}

impl Add for &Int {
    type Output = Int;

    fn add(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_add(*b)
        {
            return v.into();
        }
        (&*self.big() + &*other.big()).into()
    }
}

impl Sub for &Int {
    type Output = Int;

    fn sub(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_sub(*b)
        {
            return v.into();
        }
        (&*self.big() - &*other.big()).into()
    }
}

impl Mul for &Int {
    type Output = Int;

    fn mul(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_mul(*b)
        {
            return v.into();
        }
        (&*self.big() * &*other.big()).into()
    }
}

impl Neg for &Int {
    type Output = Int;

    fn neg(self) -> Int {
        if let Repr::Small(a) = self.0
            && let Some(v) = a.checked_neg()
        {
            return v.into();
        }
        (-&*self.big()).into()
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(b),
            (Repr::Big(a), Repr::Big(b)) => a.cmp(b),
            // A big value lies outside every small one.
            (Repr::Big(a), Repr::Small(_)) => {
                if a.sign() == Sign::Minus {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (Repr::Small(_), Repr::Big(b)) => {
                if b.sign() == Sign::Minus {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Repr::Small(v) => write!(f, "{v}"),
            Repr::Big(v) => write!(f, "{v}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_past_i128_keep_their_order_and_come_back_small() {
        let max = Int::from(i128::MAX);
        let min = Int::from(i128::MIN);
        let past = &max + &Int::ONE;
        assert_eq!(past.to_i128(), None);
        assert_eq!((&past - &Int::ONE).to_i128(), Some(i128::MAX));
        assert!(past > max && min > &min - &Int::ONE);
        assert_eq!(-&past, min);
        assert!(past > min && &min - &Int::ONE < -&past);
        // -i128::MIN is past i128; negated again it is the small value, one form for one value.
        assert_eq!(-&(-&min), min);
        assert_eq!(min.abs(), &max + &Int::ONE);
        assert_eq!((&max * &max).div_floor(&max), max);
        assert_eq!((&(&max * &max) + &Int::from(5)).mod_floor(&max), 5.into());
    }

    #[test]
    fn division_rounds_down_and_the_gcd_is_never_negative() {
        let (a, m) = (Int::from(-7), Int::from(2));
        assert_eq!(a.div_floor(&m), Int::from(-4));
        assert_eq!(a.mod_floor(&m), Int::ONE);
        assert_eq!(Int::from(-12).gcd(&Int::from(18)), Int::from(6));
        // Both are powers of two, so the gcd of i128::MIN with itself does not fit in i128.
        let min = Int::from(i128::MIN);
        assert_eq!(min.gcd(&min), -&min);
        assert_eq!(Int::ZERO.gcd(&Int::from(-5)), Int::from(5));
    }
}
