//! The rationals of the compiler's linear solvers: [`Q`], a pair of [`Int`]s in lowest terms.
//! Shared by the Omega test, `twovar` and `live3` of zedc-solvers, the lower-hull tree of
//! zedc-preimage's `product`, and the crates above zedc-int (DRY-rat-q-2026-11-26: it was
//! `zedc_solvers::linear::Q`, out of reach of the crates that do not depend on the solvers).
//! zed-kernel's `Rat` stays a separate type: it holds kept forms (a power not built) and orders
//! them by bounds, which these solvers never meet.

use crate::int::Int;

/// A rational, in lowest terms with a positive denominator. Equality is structural, which is
/// equality of value only because every constructor reduces; order is by value (cross
/// products). Why every `Q` is reduced: the fields are private to this module, and only
/// [`Q::new`] and [`Q::of`] build one from outside values. [`Q::new`] divides by
/// `g = gcd(n, d)`, which `Int::gcd` gives at least 0 and which is above 0 since `d` is not 0;
/// the quotients are exact and coprime, and a negative `d` is then negated with `n`, so `d > 0`
/// (and `0 / d` becomes `0 / 1`, since `gcd(0, d) = |d|`). [`Q::of`] gives `d = 1`.
/// [`Q::neg`] negates `n` only, and `gcd(-n, d) = gcd(n, d) = 1`; the other operations end in
/// [`Q::new`] or [`Q::of`]. Two reduced forms of one value are equal: `n / d = n' / d'` gives
/// `n·d' = n'·d`, so `d | d'` and `d' | d` by coprimality, so `d = d'` (both positive) and
/// `n = n'`. Tests: `tests::rationals_stay_in_lowest_terms_with_a_positive_denominator`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Q {
    n: Int,
    d: Int,
}

impl Q {
    /// The whole number `n`.
    pub fn of(n: Int) -> Q {
        Q { n, d: Int::ONE }
    }

    /// The rational `n / d`, in lowest terms with a positive denominator; `d` is not 0.
    pub fn new(n: Int, d: Int) -> Q {
        let g = n.gcd(&d);
        let (mut n, mut d) = if g == Int::ONE {
            (n, d)
        } else {
            (n.div_floor(&g), d.div_floor(&g))
        };
        if d.is_negative() {
            (n, d) = (-&n, -&d);
        }
        Q { n, d }
    }

    /// `self + o`; two whole numbers take the short way, with no gcd.
    pub fn add(&self, o: &Q) -> Q {
        if self.d == Int::ONE && o.d == Int::ONE {
            return Q::of(&self.n + &o.n);
        }
        Q::new(&(&self.n * &o.d) + &(&o.n * &self.d), &self.d * &o.d)
    }

    /// `self - o`.
    pub fn sub(&self, o: &Q) -> Q {
        self.add(&o.neg())
    }

    /// `-self`.
    pub fn neg(&self) -> Q {
        Q {
            n: -&self.n,
            d: self.d.clone(),
        }
    }

    /// `self · o`; two whole numbers take the short way, with no gcd.
    pub fn mul(&self, o: &Q) -> Q {
        if self.d == Int::ONE && o.d == Int::ONE {
            return Q::of(&self.n * &o.n);
        }
        Q::new(&self.n * &o.n, &self.d * &o.d)
    }

    /// `self / o`; `o` is not 0.
    pub fn div(&self, o: &Q) -> Q {
        Q::new(&self.n * &o.d, &self.d * &o.n)
    }

    /// The greatest integer at most `self`.
    pub fn floor(&self) -> Int {
        self.n.div_floor(&self.d)
    }

    /// The least integer at least `self`.
    pub fn ceil(&self) -> Int {
        self.n.div_ceil(&self.d)
    }

    /// The numerator, in lowest terms; its sign is the rational's.
    pub fn numer(&self) -> &Int {
        &self.n
    }

    /// The denominator, in lowest terms and above zero.
    pub fn denom(&self) -> &Int {
        &self.d
    }

    /// The numerator and the denominator, as [`Q::numer`] and [`Q::denom`] give them, without
    /// a copy.
    pub fn into_parts(self) -> (Int, Int) {
        (self.n, self.d)
    }

    /// Whether the value is 0.
    pub fn is_zero(&self) -> bool {
        self.n.is_zero()
    }

    /// Whether the value is below 0.
    pub fn is_negative(&self) -> bool {
        self.n.is_negative()
    }

    /// Whether the value is above 0.
    pub fn is_positive(&self) -> bool {
        self.n.is_positive()
    }
}

impl Ord for Q {
    fn cmp(&self, o: &Q) -> std::cmp::Ordering {
        (&self.n * &o.d).cmp(&(&o.n * &self.d))
    }
}

impl PartialOrd for Q {
    fn partial_cmp(&self, o: &Q) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

#[cfg(test)]
mod tests {
    use super::Q;
    use crate::int::Int;

    fn q(n: i64, d: i64) -> Q {
        Q::new(Int::from(n), Int::from(d))
    }

    #[test]
    fn rationals_stay_in_lowest_terms_with_a_positive_denominator() {
        let i = |n: i64| Q::of(Int::from(n));
        assert_eq!(
            q(6, -4),
            Q {
                n: Int::from(-3),
                d: Int::from(2)
            }
        );
        assert_eq!(q(0, -5), i(0));
        assert_eq!(q(-7, 7), i(-1));
        assert_eq!(q(6, -4).into_parts(), (Int::from(-3), Int::from(2)));
        // Each operation on whole numbers, which takes the short way, and on fractions.
        assert_eq!(i(2).add(&i(-5)), i(-3));
        assert_eq!(q(1, 2).add(&q(1, 3)), q(5, 6));
        assert_eq!(q(1, 2).add(&q(-1, 2)), i(0));
        assert_eq!(q(1, 3).sub(&q(1, 2)), q(-1, 6));
        assert_eq!(i(3).mul(&i(-4)), i(-12));
        assert_eq!(q(2, 3).mul(&q(-9, 4)), q(-3, 2));
        assert_eq!(q(2, 3).div(&q(-4, 9)), q(-3, 2));
        assert_eq!(q(-1, 3).neg(), q(1, 3));
        // Floor and ceiling on both sides of zero and at a whole number.
        assert_eq!(
            (q(-7, 2).floor(), q(-7, 2).ceil()),
            (Int::from(-4), Int::from(-3))
        );
        assert_eq!(
            (q(7, 2).floor(), q(7, 2).ceil()),
            (Int::from(3), Int::from(4))
        );
        assert_eq!(
            (i(-3).floor(), i(-3).ceil()),
            (Int::from(-3), Int::from(-3))
        );
        // Signs and order.
        assert!(i(0).is_zero() && !q(1, 9).is_zero());
        assert!(q(-1, 9).is_negative() && !q(-1, 9).is_positive());
        assert!(q(1, 9).is_positive() && !i(0).is_negative() && !i(0).is_positive());
        let sorted = [q(-1, 2), q(-1, 3), i(0), q(1, 3), q(1, 2), i(1)];
        assert!(sorted.windows(2).all(|w| w[0] < w[1]));
        assert_eq!(q(2, 4).cmp(&q(1, 2)), std::cmp::Ordering::Equal);
    }
}
