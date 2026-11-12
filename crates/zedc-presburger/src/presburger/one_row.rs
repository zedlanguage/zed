//! The answer of a conjunction of bounds on single atoms and at most one longer row
//! (PRES-disj-cost-xr).
//!
//! A formula such as `0 <= y[i] <= 1000 + i` for each i, with `Σ y[i] == s`, is a box and one
//! row. The solver eliminates the row's atoms one at a time and copies the shrinking row at each
//! step, O(n²) term work, and a projection asks that question again at each end it bisects. Here
//! the box and the row are read once:
//! - each bound of one atom, `a·x + k >= 0` or `a·x + k == 0`, is rounded to an integer end
//!   of `x`; an equation that no integer meets, or ends that cross, leave no point;
//! - over the box, the row's least and greatest values are sums of one corner per term. A row
//!   `t >= 0` has a point when its greatest value is at least zero: the other atoms at the ends
//!   that make it greatest are themselves a point of the box, whatever its coefficients. A row
//!   `t == 0` whose coefficients are all 1 or -1 takes every integer value between its least
//!   and its greatest, since each term moves it by one, so it has a point exactly when zero
//!   lies between them. An equation with another coefficient is left to the solver: its values
//!   can have gaps (`2·x + 2·y == 3`);
//! - the projection of `x` is the interval its bounds give, met with what the row allows `x`
//!   with the other atoms anywhere in their box: the same sums less `x`'s own term. Each is
//!   an interval, so the projection is exact.
//!
//! A sum with an atom unbounded on the side it is read from is infinite; the sums count those
//! terms apart from the finite part, so that taking one term out costs O(1).
//!
//! Each atom is read as a variable of its own, as the solver reads it. Before the solver,
//! [`super::decide`] and [`super::project_each`] may answer by propagation, which reads a
//! product through its factors, so a formula with a product atom is left to them; inside the
//! solver ([`super::solve`] without a model) it is read here as the solver reads it.
//!
//! The search over disjunctions ([`super::pick`]) still reads the solver's own point: another
//! point of the same box changes the questions it asks next. The public [`super::satisfiable`]
//! entry gives the point built here ([`OneRow::point`]) directly, in the same near-linear work
//! as [`super::decide`], without changing those internal search models (I19).

use std::collections::BTreeMap;

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::Conjuncts;
use super::formula::{Atom, Con, Formula, Model, Rel};

/// The least or the greatest value of a sum over a box: its finite part, and how many of its
/// terms are unbounded on that side.
#[derive(Default)]
struct Sum {
    finite: Int,
    open: usize,
}

impl Sum {
    fn add(&mut self, v: Option<Int>) {
        match v {
            Some(v) => self.finite = &self.finite + &v,
            None => self.open += 1,
        }
    }

    /// The sum without the term `v` (`None` for an unbounded term), or `None` when that is
    /// unbounded.
    fn without(&self, v: Option<&Int>) -> Option<Int> {
        match v {
            Some(v) if self.open == 0 => Some(&self.finite - v),
            None if self.open == 1 => Some(self.finite.clone()),
            _ => None,
        }
    }
}

/// The ends of each atom, `None` for an end that is unbounded.
type Ends = (Option<Int>, Option<Int>);

/// A conjunction of bounds on single atoms and at most one longer row, read once.
pub(super) struct OneRow {
    ends: BTreeMap<Atom, Ends>,
    row: Option<Con>,
    least: Sum,
    most: Sum,
    empty: bool,
}

impl OneRow {
    /// A formula, given as its top-level conjuncts (`Formula::conjunct_list`), read as a box and one
    /// row, when it is a conjunction of constraints with no product atom, and such a box and row;
    /// `None` for any other formula. A conjunct other than a constraint fails it before any list
    /// is made.
    // Complexity tradeoff: the solver's elimination of the row's n atoms copies the shrinking
    // row at each step, O(n²) term work, and a projection repeats that for each end it bisects.
    // Here the ends are kept in an ordered map and the row's two sums are made once, O(n log n);
    // each projected atom takes its own term out of the sums, O(log n), not a new sum of the
    // other n - 1 terms, which would cost O(n²) over all atoms. Test:
    // `l01_38_presburger::one_row::a_box_and_one_row_scale`. COMPLEXITY.md row PRES-disj-cost.
    pub(super) fn of(conjuncts: &Conjuncts) -> Option<OneRow> {
        if !conjuncts.iter().all(|g| matches!(g, Formula::Con(_))) {
            return None;
        }
        let cons: Vec<&Con> = conjuncts
            .iter()
            .map(|g| match g {
                Formula::Con(c) if !c.lin.terms.keys().any(|a| matches!(a, Atom::Product(..))) => {
                    Some(c)
                }
                _ => None,
            })
            .collect::<Option<_>>()?;
        OneRow::of_cons(&cons)
    }

    /// `cons`, a conjunction, read as a box and one row; `None` when it is not one.
    pub(super) fn of_cons(cons: &[&Con]) -> Option<OneRow> {
        let mut ends: BTreeMap<Atom, Ends> = BTreeMap::new();
        let mut row: Option<&Con> = None;
        let mut empty = false;
        for c in cons {
            let mut terms = c.lin.terms.iter();
            let k = &c.lin.constant;
            match (terms.next(), terms.next()) {
                (None, _) => {
                    empty |= k.is_negative() || (c.rel == Rel::Eq && !k.is_zero());
                }
                (Some((a, coef)), None) => {
                    // `coef·a + k` compared with zero.
                    let (lo, hi) = match c.rel {
                        Rel::Eq => {
                            empty |= !k.mod_floor(coef).is_zero();
                            let v = -&k.div_floor(coef);
                            (Some(v.clone()), Some(v))
                        }
                        // `a >= -k / coef`, rounded up.
                        Rel::Ge if coef.is_positive() => (Some(-&k.div_floor(coef)), None),
                        // `a <= k / -coef`, rounded down.
                        Rel::Ge => (None, Some(k.div_floor(&-coef))),
                    };
                    let (l, h) = ends.entry(a.clone()).or_default();
                    if let Some(lo) = lo
                        && l.as_ref().is_none_or(|v| lo > *v)
                    {
                        *l = Some(lo);
                    }
                    if let Some(hi) = hi
                        && h.as_ref().is_none_or(|v| hi < *v)
                    {
                        *h = Some(hi);
                    }
                }
                (Some(_), Some(_)) => {
                    if row.is_some()
                        || (c.rel == Rel::Eq && !c.lin.terms.values().all(Int::is_unit))
                    {
                        return None;
                    }
                    row = Some(c);
                }
            }
        }
        empty |= ends
            .values()
            .any(|e| matches!(e, (Some(l), Some(h)) if l > h));
        let (mut least, mut most) = (Sum::default(), Sum::default());
        if let Some(c) = row {
            least.finite = c.lin.constant.clone();
            most.finite = c.lin.constant.clone();
            for (a, coef) in &c.lin.terms {
                let (l, h) = signed(ends.entry(a.clone()).or_default(), coef);
                least.add(l);
                most.add(h);
            }
            empty |= most.open == 0 && most.finite.is_negative();
            empty |= c.rel == Rel::Eq && least.open == 0 && least.finite.is_positive();
        }
        Some(OneRow {
            ends,
            row: row.cloned(),
            least,
            most,
            empty,
        })
    }

    /// Whether the conjunction has a point.
    pub(super) fn exists(&self) -> bool {
        !self.empty
    }

    /// A point, when there is one, with a value for every atom read. Each atom starts at a value
    /// of its own ends, the greatest end that the row reads upward when that end is finite; the
    /// row's value there is then moved to zero, or above it for a row `t >= 0`, by moving atoms
    /// toward their other ends, each as far as it may go, until the row is met. The row takes
    /// every value between its least and its greatest when it is an equation (its coefficients
    /// are 1 or -1) and is met at its greatest when it is `t >= 0`, so the moves reach it. O(n)
    /// after the read.
    pub(super) fn point(&self) -> Option<Model> {
        if self.empty {
            return None;
        }
        let start = |(l, h): &Ends, up: bool| {
            let v = if up {
                h.as_ref().or(l.as_ref())
            } else {
                l.as_ref().or(h.as_ref())
            };
            v.cloned().unwrap_or(Int::ZERO)
        };
        let mut m: Model = Model::new();
        for (a, e) in &self.ends {
            let up = self
                .row
                .as_ref()
                .and_then(|c| c.lin.terms.get(a))
                .is_some_and(|c| c.is_positive());
            m.insert(a.clone(), start(e, up));
        }
        let Some(c) = &self.row else {
            return Some(m);
        };
        let mut value = c.lin.constant.clone();
        for (a, coef) in &c.lin.terms {
            value = &value + &(coef * &m[a]);
        }
        // For `t >= 0` only a value below zero is moved; for `t == 0`, both signs.
        let lower = c.rel == Rel::Eq && value.is_positive();
        if !value.is_negative() && !lower {
            return Some(m);
        }
        for (a, coef) in &c.lin.terms {
            if value.is_zero() || (c.rel == Rel::Ge && value.is_positive()) {
                break;
            }
            // Move `a` so that `coef·a` changes by `-value` (exact, the coefficient being 1 or
            // -1, for an equation; for `t >= 0` by at least `-value`, the steps rounded up), as
            // far as `a`'s end allows.
            let (l, h) = &self.ends[a];
            let step = if c.rel == Rel::Ge {
                // `ceil(-value / |coef|)` steps toward the end that raises `coef·a`.
                let steps = -&value.div_floor(&coef.abs());
                if coef.is_positive() { steps } else { -&steps }
            } else {
                (-&value).div_floor(coef)
            };
            let now = m[a].clone();
            let mut to = &now + &step;
            if let Some(h) = h
                && to > *h
            {
                to = h.clone();
            }
            if let Some(l) = l
                && to < *l
            {
                to = l.clone();
            }
            value = &value + &(coef * &(&to - &now));
            m.insert(a.clone(), to);
        }
        Some(m)
    }

    /// The projection onto `a`, exact: every value in it is the value of `a` at some point.
    pub(super) fn project(&self, a: &Atom) -> IntervalSet {
        if self.empty {
            return IntervalSet::empty();
        }
        let Some(e) = self.ends.get(a) else {
            return IntervalSet::range(End::NegInf, End::PosInf);
        };
        let (mut lo, mut hi) = e.clone();
        if let Some(c) = &self.row
            && let Some(coef) = c.lin.terms.get(a)
        {
            // With `a`'s term out, the row's other terms and constant range over
            // [other_least, other_most]; `coef·a` must lie in [-other_most, -other_least]
            // for an equation, and at or above -other_most for a row `t >= 0`.
            let (l, h) = signed(e, coef);
            let below = self.most.without(h.as_ref()).map(|v| -&v);
            let above = match c.rel {
                Rel::Eq => self.least.without(l.as_ref()).map(|v| -&v),
                Rel::Ge => None,
            };
            // `coef·a >= v` and `coef·a <= v` as ends of `a`, rounded inward.
            let up = |v: Int| -&(-&v).div_floor(coef);
            let down = |v: Int| v.div_floor(coef);
            let (nl, nh) = if coef.is_positive() {
                (below.map(up), above.map(down))
            } else {
                (above.map(up), below.map(down))
            };
            if let Some(nl) = nl
                && lo.as_ref().is_none_or(|v| nl > *v)
            {
                lo = Some(nl);
            }
            if let Some(nh) = nh
                && hi.as_ref().is_none_or(|v| nh < *v)
            {
                hi = Some(nh);
            }
        }
        IntervalSet::range(
            lo.map_or(End::NegInf, |v| End::Fin(Num::from(&v))),
            hi.map_or(End::PosInf, |v| End::Fin(Num::from(&v))),
        )
    }
}

/// The least and the greatest of `coef·x` over the ends `e` of `x`.
fn signed(e: &Ends, coef: &Int) -> Ends {
    let (l, h) = e;
    let (l, h) = (l.as_ref().map(|v| coef * v), h.as_ref().map(|v| coef * v));
    if coef.is_positive() { (l, h) } else { (h, l) }
}

#[cfg(test)]
mod tests {
    use super::super::formula::Lin;
    use super::*;

    /// Each atom's ends; `None` is an open end.
    type Ends = [(Option<i64>, Option<i64>); 3];

    /// A random box of three atoms, some ends open, and a row `t >= 0` or `t == 0` (its
    /// coefficients 1 or -1 for an equation), from `seed`.
    fn case(seed: u64) -> (Vec<Con>, [Atom; 3], Ends) {
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut next = |n: u64| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s % n
        };
        let atoms = ["x", "y", "z"].map(|n| Atom::Sym(n.into()));
        let mut cons = Vec::new();
        let mut ends = [(None, None); 3];
        for (a, e) in atoms.iter().zip(&mut ends) {
            let lo = next(7) as i64 - 3;
            let hi = lo + next(4) as i64;
            let x = Lin::atom(a.clone());
            if next(5) != 0 {
                cons.push(Con::ge(&x, &Lin::constant(lo)));
                e.0 = Some(lo);
            }
            if next(5) != 0 {
                cons.push(Con::ge(&Lin::constant(hi), &x));
                e.1 = Some(hi);
            }
        }
        let eq = next(2) == 0;
        let mut row = Lin::constant(next(13) as i64 - 6);
        for a in &atoms {
            let c = match (eq, next(3)) {
                (_, 0) => 0,
                (true, _) => [1, -1][next(2) as usize],
                (false, _) => [1, -1, 2, -3][next(4) as usize],
            };
            row = row.plus(&Lin::atom(a.clone()).times(c));
        }
        let zero = Lin::constant(0);
        cons.push(if eq {
            Con::eq(&row, &zero)
        } else {
            Con::ge(&row, &zero)
        });
        (cons, atoms, ends)
    }

    #[test]
    fn a_point_is_built_wherever_there_is_one_and_projections_are_exact() {
        let mut built = 0;
        for seed in 0..3000 {
            let (cons, atoms, ends) = case(seed);
            let refs: Vec<&Con> = cons.iter().collect();
            let Some(b) = OneRow::of_cons(&refs) else {
                continue;
            };
            // Every point lies in the window when all ends are given; with an end open, the
            // window still holds a point when there is one near the box, and the built point
            // is checked against the constraints.
            let closed = ends.iter().all(|(l, h)| l.is_some() && h.is_some());
            let mut found: [Option<(i64, i64)>; 3] = [None; 3];
            for x in -9..=9 {
                for y in -9..=9 {
                    for z in -9..=9 {
                        let m: Model = atoms
                            .iter()
                            .cloned()
                            .zip([x, y, z].map(Int::from))
                            .collect();
                        if cons.iter().all(|c| c.holds_linear(&m)) {
                            for (f, v) in found.iter_mut().zip([x, y, z]) {
                                *f = Some(f.map_or((v, v), |(l, h)| (l.min(v), h.max(v))));
                            }
                        }
                    }
                }
            }
            match b.point() {
                Some(m) => {
                    built += 1;
                    assert!(
                        cons.iter().all(|c| c.holds_linear(&m)),
                        "seed {seed}: {m:?}"
                    );
                }
                None => assert!(found[0].is_none(), "seed {seed}: a point was missed"),
            }
            if closed {
                assert_eq!(b.exists(), found[0].is_some(), "seed {seed}");
                for (a, f) in atoms.iter().zip(found) {
                    let want = f.map_or(IntervalSet::empty(), |(l, h)| {
                        IntervalSet::range(End::Fin(Num::from(l)), End::Fin(Num::from(h)))
                    });
                    assert_eq!(b.project(a), want, "seed {seed}, {a:?}");
                }
            }
        }
        assert!(built > 1000, "{built} points");
    }
}
