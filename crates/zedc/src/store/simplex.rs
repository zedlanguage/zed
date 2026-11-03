//! Rational feasibility of a system of linear inequalities (DESIGN.md sec:domains, step
//! L1.38): the general simplex of Dutertre and de Moura, used by the Omega test only as a proof
//! that a system has no rational point, and for the rational point the UTVPI test starts from.

use std::collections::{BTreeMap, BTreeSet};

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

    pub(crate) fn mul(&self, o: &Q) -> Q {
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

    pub(crate) fn lt(&self, o: &Q) -> bool {
        &self.n * &o.d < &o.n * &self.d
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

    pub(crate) fn abs(&self) -> Q {
        if self.is_negative() {
            self.neg()
        } else {
            self.clone()
        }
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

/// The general simplex over rows `Σ a[i]·x[i] + k >= 0`: one slack variable for each row of two
/// or more terms, and each variable with its bounds. A pivot takes the basic variable that
/// violates its bound most and the nonbasic variable of largest coefficient in its row
/// (Dantzig's rule), while each pivot lowers the total violation; from the first pivot that
/// does not, it takes the first of each by index (Bland's rule), which cannot cycle. Rational
/// feasibility has one answer whatever the rule; the point found does not, and the Omega test's
/// last step keeps that point only when it is integer, so the rule decides which systems with
/// no exact elimination get a point and which are refused (the rule and the order of the
/// variables are fixed, so each system has one answer).
pub(crate) struct Simplex {
    /// Each basic variable as a sum over the nonbasic ones.
    rows: BTreeMap<usize, BTreeMap<usize, Q>>,
    /// For each variable, the basic variables whose rows hold it.
    cols: Vec<BTreeSet<usize>>,
    /// The values; at a point once [`Simplex::feasible`] holds.
    pub(crate) val: Vec<Q>,
    lo: Vec<Option<Q>>,
    hi: Vec<Option<Q>>,
}

impl Simplex {
    /// The simplex over `n` variables and the rows `(a, k)`.
    pub(crate) fn new<'a>(n: usize, rows: impl Iterator<Item = (&'a [Term], &'a Int)>) -> Simplex {
        let rows: Vec<(&[Term], &Int)> = rows.collect();
        let wide = rows.iter().filter(|(a, _)| a.len() > 1).count();
        let zero = || Q::of(Int::ZERO);
        let mut s = Simplex {
            rows: BTreeMap::new(),
            cols: vec![BTreeSet::new(); n + wide],
            val: vec![zero(); n + wide],
            lo: vec![None; n + wide],
            hi: vec![None; n + wide],
        };
        let mut slack = n;
        for (a, k) in rows {
            if let [(j, c)] = a {
                // `c·x + k >= 0`, so `x >= -k / c` for `c` above zero and `x <= k / -c` below.
                let b = Q::new(-k, c.clone());
                let tighter = |old: &Option<Q>, low: bool| {
                    old.as_ref()
                        .is_none_or(|o| if low { o.lt(&b) } else { b.lt(o) })
                };
                if c.is_positive() {
                    if tighter(&s.lo[*j], true) {
                        s.lo[*j] = Some(b);
                    }
                } else if tighter(&s.hi[*j], false) {
                    s.hi[*j] = Some(b);
                }
            } else {
                s.lo[slack] = Some(Q::of(-k));
                s.rows.insert(
                    slack,
                    a.iter().map(|(j, c)| (*j, Q::of(c.clone()))).collect(),
                );
                for (j, _) in a {
                    s.cols[*j].insert(slack);
                }
                slack += 1;
            }
        }
        for j in 0..n {
            let v = match (&s.lo[j], &s.hi[j]) {
                (Some(l), _) if !l.is_negative() => l.clone(),
                (_, Some(h)) if h.is_negative() => h.clone(),
                _ => continue,
            };
            s.set(j, v);
        }
        s
    }

    /// Gives the nonbasic `j` the value `v`.
    fn set(&mut self, j: usize, v: Q) {
        let d = v.sub(&self.val[j]);
        for b in &self.cols[j] {
            self.val[*b] = self.val[*b].add(&self.rows[b][&j].mul(&d));
        }
        self.val[j] = v;
    }

    /// Moves the basic `b` to `v` by the nonbasic `n`, which trade places.
    fn pivot(&mut self, b: usize, n: usize, v: Q) {
        let row = self.rows.remove(&b).expect("basic");
        let a = row[&n].clone();
        let theta = v.sub(&self.val[b]).div(&a);
        self.val[b] = v;
        self.val[n] = self.val[n].add(&theta);
        // `n = (b - Σ c·o) / a`.
        let inv = Q::of(Int::ONE).div(&a);
        let mut new: BTreeMap<usize, Q> = BTreeMap::new();
        new.insert(b, inv.clone());
        for (o, c) in &row {
            self.cols[*o].remove(&b);
            if *o != n {
                new.insert(*o, c.mul(&inv).neg());
            }
        }
        for r in std::mem::take(&mut self.cols[n]) {
            let e = self
                .rows
                .get_mut(&r)
                .expect("basic")
                .remove(&n)
                .expect("held");
            self.val[r] = self.val[r].add(&e.mul(&theta));
            let at = self.rows.get_mut(&r).expect("basic");
            for (o, c) in &new {
                let t = e.mul(c);
                let sum = at.get(o).map_or(t.clone(), |x| x.add(&t));
                if sum.is_zero() {
                    at.remove(o);
                    self.cols[*o].remove(&r);
                } else {
                    at.insert(*o, sum);
                    self.cols[*o].insert(r);
                }
            }
        }
        for o in new.keys() {
            self.cols[*o].insert(n);
        }
        self.rows.insert(n, new);
    }

    /// How far the basic `b` lies outside its bounds, the bound, and whether it is below it.
    fn violation(&self, b: usize) -> Option<(Q, Q, bool)> {
        let v = &self.val[b];
        match (&self.lo[b], &self.hi[b]) {
            (Some(l), _) if v.lt(l) => Some((l.sub(v), l.clone(), true)),
            (_, Some(h)) if h.lt(v) => Some((v.sub(h), h.clone(), false)),
            _ => None,
        }
    }

    /// The sum of the violations.
    fn total(&self) -> Q {
        self.rows
            .keys()
            .filter_map(|b| self.violation(*b))
            .fold(Q::of(Int::ZERO), |t, (g, _, _)| t.add(&g))
    }

    /// Whether the bounds hold somewhere, with `val` such a point when they do. While each
    /// pivot lowers the total violation no state repeats, since the states are finitely many
    /// (each nonbasic variable at its first value or at a bound); from the first pivot that does
    /// not, Bland's rule holds to the end, and under it the general simplex ends.
    pub(crate) fn feasible(&mut self) -> bool {
        let mut bland = false;
        let mut last = self.total();
        loop {
            let mut broken: Option<(usize, Q, bool, Q)> = None;
            for b in self.rows.keys() {
                if let Some((g, to, up)) = self.violation(*b) {
                    if bland {
                        broken = Some((*b, to, up, g));
                        break;
                    }
                    if broken.as_ref().is_none_or(|x| x.3.lt(&g)) {
                        broken = Some((*b, to, up, g));
                    }
                }
            }
            let Some((b, to, up, _)) = broken else {
                return true;
            };
            let mut entering: Option<(usize, Q)> = None;
            for (n, c) in &self.rows[&b] {
                let rise = c.is_positive() == up;
                let free = if rise {
                    self.hi[*n].as_ref().is_none_or(|h| self.val[*n].lt(h))
                } else {
                    self.lo[*n].as_ref().is_none_or(|l| l.lt(&self.val[*n]))
                };
                if !free {
                    continue;
                }
                if bland {
                    entering = Some((*n, c.clone()));
                    break;
                }
                let m = c.abs();
                if entering.as_ref().is_none_or(|e| e.1.lt(&m)) {
                    entering = Some((*n, m));
                }
            }
            let Some((n, _)) = entering else {
                return false;
            };
            self.pivot(b, n, to);
            if !bland {
                let now = self.total();
                bland = !now.lt(&last);
                last = now;
            }
        }
    }
}
