//! The rationals and the coefficient terms of the linear-relation domain (DESIGN.md
//! sec:domains, step L1.38), shared by the Omega test, `twovar` and `utvpi`.

use zedc_int::int::Int;

/// A coefficient at a variable.
pub type Term = (usize, Int);

/// A rational, in lowest terms with a positive denominator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Q {
    pub(crate) n: Int,
    pub(crate) d: Int,
}

impl Q {
    pub(crate) fn of(n: Int) -> Q {
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

    pub(crate) fn add(&self, o: &Q) -> Q {
        if self.d == Int::ONE && o.d == Int::ONE {
            return Q::of(&self.n + &o.n);
        }
        Q::new(&(&self.n * &o.d) + &(&o.n * &self.d), &self.d * &o.d)
    }

    pub(crate) fn sub(&self, o: &Q) -> Q {
        self.add(&o.neg())
    }

    pub(crate) fn neg(&self) -> Q {
        Q {
            n: -&self.n,
            d: self.d.clone(),
        }
    }

    pub(crate) fn mul(&self, o: &Q) -> Q {
        if self.d == Int::ONE && o.d == Int::ONE {
            return Q::of(&self.n * &o.n);
        }
        Q::new(&self.n * &o.n, &self.d * &o.d)
    }

    pub(crate) fn div(&self, o: &Q) -> Q {
        Q::new(&self.n * &o.d, &self.d * &o.n)
    }

    /// The greatest integer at most `self`.
    pub(crate) fn floor(&self) -> Int {
        self.n.div_floor(&self.d)
    }

    /// The least integer at least `self`.
    pub(crate) fn ceil(&self) -> Int {
        -&(-&self.n).div_floor(&self.d)
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.n.is_zero()
    }

    pub(crate) fn is_negative(&self) -> bool {
        self.n.is_negative()
    }

    pub(crate) fn is_positive(&self) -> bool {
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
    use zedc_int::int::Int;

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
