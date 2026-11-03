//! The rationals and the coefficient terms of the linear-relation domain (DESIGN.md
//! sec:domains, step L1.38), shared by the Omega test, `twovar` and `utvpi`.

use super::int::Int;

/// A coefficient at a variable.
pub(crate) type Term = (usize, Int);

/// A rational, in lowest terms with a positive denominator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Q {
    pub(crate) n: Int,
    pub(crate) d: Int,
}

impl Q {
    pub(crate) fn of(n: Int) -> Q {
        Q { n, d: Int::ONE }
    }

    pub(crate) fn new(n: Int, d: Int) -> Q {
        let g = n.gcd(&d);
        let (mut n, mut d) = (n.div_floor(&g), d.div_floor(&g));
        if d.is_negative() {
            (n, d) = (-&n, -&d);
        }
        Q { n, d }
    }

    pub(crate) fn add(&self, o: &Q) -> Q {
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
