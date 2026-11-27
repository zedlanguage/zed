//! The affine hull of a set of integer points (Karr's join): the affine equalities that hold at
//! every point, and the join that keeps the equalities two sets both satisfy. Karr: M. Karr,
//! "Affine relationships among variables of a program", Acta Informatica 6(2), 1976,
//! doi:10.1007/bf00268497, read 2026-11-21: the join is his affine union (4.11), computed by
//! his sec. 5.2 column by column on a unique reduced row-echelon form; this file keeps the
//! definition but not that form or that algorithm (below). The full citation and summary are in
//! zedc-presburger's `lib.rs`, "References", whose step L1.39 this was written for; it moved
//! here from zedc-presburger `hull.rs` (plan row DRY-affine-crate-2026-11-26), generic over the
//! form of a row ([`Form`]).
//!
//! The equalities are kept in reduced row echelon form over the rationals, each row scaled to
//! integers with no common factor and its first coefficient positive. No row mentions another
//! row's pivot. A new row's pivot is its atom the fewest rows mention, the first of them on a
//! tie, so that adding it rewrites as few rows as it can: rows `x1 - x2`, `x1 - x3`, … each
//! take their last atom and rewrite none, where taking `x1` would rewrite every row before.
//! Two hulls of one set may then have different rows. A row `t` means `t == 0`. The rows are in
//! persistent maps, so a hull made from another by a few changes shares the rest with it, and the
//! join of the two finds the rows that differ in time near their number: the rows by pivot are a
//! treap whose shape its pivots fix (module `rows`), so the subtrees two such hulls share sit at
//! the same places in both. Coefficients are unbounded integers.

mod rows;

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use imbl::OrdMap;
use rows::Rows;

use crate::Coef;
pub use crate::form::Form;
use zedc_int::int::Int;

/// The affine hull of a set of points, as the equalities that hold on it.
#[derive(Clone, Debug)]
pub struct Hull<F: Form> {
    /// The rows by their pivots.
    rows: Rows<F>,
    /// The pivots of the rows that mention each atom other than their pivot.
    uses: OrdMap<F::Atom, OrdMap<F::Atom, ()>>,
    /// Whether the set has no point.
    pub is_empty: bool,
}

// Written out, since a derived `Default` asks the atoms to have one too.
impl<F: Form> Default for Hull<F> {
    fn default() -> Self {
        Hull {
            rows: Rows::default(),
            uses: OrdMap::new(),
            is_empty: false,
        }
    }
}

impl<F: Form> Hull<F> {
    /// The hull of every point: no equality.
    pub fn all() -> Hull<F> {
        Hull::default()
    }

    /// The hull of the empty set.
    pub fn empty() -> Hull<F> {
        Hull {
            is_empty: true,
            ..Hull::default()
        }
    }

    /// The hull of the points where each term of `terms` is zero.
    pub fn of<'a>(terms: impl IntoIterator<Item = &'a F>) -> Hull<F>
    where
        F: 'a,
    {
        terms.into_iter().fold(Hull::all(), |h, t| h.and(t))
    }

    /// The rows, in pivot order.
    pub fn rows(&self) -> impl Iterator<Item = &F> {
        self.rows.values().map(|t| &**t)
    }

    /// `t` with each row's pivot replaced by the rest of its row: for a row `k * p + s` and `t`
    /// of `a * p + r`, the term `|k| * (a * p + r) - sign(k) * a * (k * p + s)`, which mentions
    /// no `p` and is zero, or of the sign of `t`, where `t` is, at the points of the hull. One
    /// pass suffices, since no row mentions another's pivot. The result is not divided by the
    /// gcd of its coefficients: a caller that reads it as a constraint does that (zedc-presburger
    /// `hull::reduce`).
    pub fn reduce_form(&self, t: &F) -> F {
        let mut out = t.clone();
        for a in t.terms().keys() {
            if let Some(row) = self.rows.get(a) {
                let k = &row.terms()[a];
                let s = if k.is_negative() {
                    out.terms()[a].neg()
                } else {
                    out.terms()[a].clone()
                };
                out = combine(&out, &k.abs(), &**row, &s);
            }
        }
        out
    }

    /// The hull of the points of this one where `t` is zero. The hull is taken by value, so
    /// that rows and uses it holds alone are changed in place rather than copied.
    pub fn and(mut self, t: &F) -> Hull<F> {
        if self.is_empty {
            return self;
        }
        let mut r = t.clone();
        for a in t.terms().keys() {
            if let Some(p) = self.rows.get(a) {
                r = eliminate(&r, &**p, a);
            }
        }
        if r.terms().is_empty() {
            return if r.constant().is_zero() {
                self
            } else {
                Hull::empty()
            };
        }
        let r = primitive(r);
        let pivot = r
            .terms()
            .keys()
            .min_by_key(|a| self.uses.get(*a).map_or(0, OrdMap::len))
            .expect("a term")
            .clone();
        // Once the pivot is eliminated from the rows that mention it, no row other than the
        // new one mentions it, so its entry in `uses` is taken out whole. `remove` and `get_mut`
        // copy the path to a key even when it is absent, if the map is shared, so an absent key
        // is looked up first.
        let mentions = if self.uses.contains_key(&pivot) {
            self.uses.remove(&pivot).expect("a pivot in `uses`")
        } else {
            OrdMap::new()
        };
        for q in mentions.keys() {
            let row = self.rows.get_mut(q).expect("a row of each pivot in `uses`");
            let now = eliminate(&**row, &r, &pivot);
            used(&mut self.uses, &**row, q, false);
            used(&mut self.uses, &now, q, true);
            *row = Arc::new(now);
        }
        used(&mut self.uses, &r, &pivot, true);
        self.rows.insert(pivot, Arc::new(r));
        self
    }

    /// The hull of the union of the two sets: the equalities both hold. The rows the two have
    /// in common are kept, and the rest are intersected. The rows both span are the common
    /// rows plus what the rest of each span in common, since neither rest mentions a common
    /// row's pivot; so a join of hulls that differ in a few rows costs near the rows that
    /// differ. The rows of `self` that `other` lacks or holds otherwise are found first and
    /// removed after, so that `self` is changed in place.
    pub fn join(mut self, other: &Hull<F>) -> Hull<F> {
        if self.is_empty {
            return other.clone();
        }
        if other.is_empty {
            return self;
        }
        let (mut gone, mut a, mut b) = (Vec::new(), Vec::new(), Vec::new());
        self.rows.diff(&other.rows, |s, t| {
            if let Some((p, s)) = s {
                gone.push(p.clone());
                a.push(s.clone());
            }
            if let Some(t) = t {
                b.push(t.clone());
            }
        });
        for (p, s) in gone.iter().zip(&a) {
            self.rows.remove(p);
            used(&mut self.uses, &**s, p, false);
        }
        // The common rows are reduced against each other already.
        intersect(&a, &b).iter().fold(self, |h, t| h.and(t))
    }
}

impl<F: Form + fmt::Display> fmt::Display for Hull<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty {
            return write!(f, "empty");
        }
        let rows: Vec<String> = self.rows().map(|t| format!("{t} == 0")).collect();
        write!(f, "{}", rows.join(", "))
    }
}

/// Adds the row `t` at `pivot` to `uses`, or removes it.
fn used<F: Form>(
    uses: &mut OrdMap<F::Atom, OrdMap<F::Atom, ()>>,
    t: &F,
    pivot: &F::Atom,
    add: bool,
) {
    for a in t.terms().keys().filter(|a| *a != pivot) {
        if add {
            uses.entry(a.clone()).or_default().insert(pivot.clone(), ());
        } else if uses.contains_key(a)
            && let Some(m) = uses.get_mut(a)
        {
            m.remove(pivot);
            if m.is_empty() {
                uses.remove(a);
            }
        }
    }
}

/// `k · r - c · p`, with no zero coefficient. O(|r| + |p| log |r|).
// Complexity tradeoff: naive version, as zedc-presburger wrote it with `Lin`'s operations,
// `r.times(k).minus(&p.times(c))`: `minus` scales `p · c` once more by -1 into a third map before
// adding it, two copies of `p`. Used: `p`'s terms added at `-c` straight into the copy of `r`
// ([`crate::add_scaled`]), one pass over `p`, the same terms and constant. Tradeoff: none; one
// map fewer.
fn combine<F: Form>(r: &F, k: &Int, p: &F, c: &Int) -> F {
    let mut out = F::default();
    let (terms, constant) = out.parts_mut();
    *terms = crate::scaled(r.terms(), k);
    let minus_c = c.neg();
    crate::add_scaled(terms, p.terms(), &minus_c);
    *constant = r.constant().mul(k).add(&p.constant().mul(&minus_c));
    out
}

/// `r` with the atom `a` removed by adding a multiple of `p`, whose coefficient of `a` is
/// positive.
fn eliminate<F: Form>(r: &F, p: &F, a: &F::Atom) -> F {
    match r.terms().get(a) {
        None => r.clone(),
        Some(c) => primitive(combine(r, &p.terms()[a], p, c)),
    }
}

/// The gcd of a term's coefficients and constant.
fn content<F: Form>(t: &F) -> Int {
    crate::content(t.terms().values().chain([t.constant()]))
}

/// `t` divided by `k`, above zero, which divides each coefficient and the constant.
fn over<F: Form>(t: &F, k: &Int) -> F {
    let mut out = t.clone();
    let (terms, constant) = out.parts_mut();
    crate::divide_row(terms, constant, k);
    out
}

/// `t` divided by the gcd of its coefficients and constant, its first coefficient positive.
fn primitive<F: Form>(t: F) -> F {
    let g = content(&t);
    if g.is_zero() {
        return t;
    }
    let mut t = if g.is_unit() { t } else { over(&t, &g) };
    if t.terms().values().next().is_some_and(Int::is_negative) {
        let (terms, constant) = t.parts_mut();
        terms.values_mut().for_each(|c| *c = c.neg());
        *constant = constant.neg();
    }
    t
}

/// Terms spanning the terms both `a` and `b` span (Zassenhaus): each term `t` of `a` enters as
/// the pair `(t, t)` and each of `b` as `(t, 0)`, and the pairs are brought to echelon form on
/// their first halves; the second half of a pair whose first half becomes zero is a sum of
/// terms of `a` that is also a sum of terms of `b`.
fn intersect<F: Form>(a: &[Arc<F>], b: &[Arc<F>]) -> Vec<F> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    // The pairs by the first atom of their first half; `None` for a first half that is a
    // constant.
    let mut pivots: BTreeMap<Option<F::Atom>, (F, F)> = BTreeMap::new();
    let mut out = Vec::new();
    let pairs = a
        .iter()
        .map(|t| ((**t).clone(), (**t).clone()))
        .chain(b.iter().map(|t| ((**t).clone(), F::default())));
    for (mut l, mut r) in pairs {
        loop {
            if l.terms().is_empty() && l.constant().is_zero() {
                out.push(r);
                break;
            }
            let k = l.terms().keys().next().cloned();
            let Some((pl, pr)) = pivots.get(&k) else {
                pivots.insert(k, (l, r));
                break;
            };
            let (c, cp) = match &k {
                None => (l.constant(), pl.constant()),
                Some(k) => (&l.terms()[k], &pl.terms()[k]),
            };
            let nl = combine(&l, cp, pl, c);
            let nr = combine(&r, cp, pr, c);
            let g = content(&nl).gcd(&content(&nr));
            (l, r) = if g.is_zero() || g.is_unit() {
                (nl, nr)
            } else {
                (over(&nl, &g), over(&nr, &g))
            };
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::form::tests::Lin;

    /// `Σ c·x + k` from pairs of name and coefficient.
    fn lin(terms: &[(&str, i64)], k: i64) -> Lin {
        let mut out = Lin {
            constant: Int::from(k),
            ..Lin::default()
        };
        for (x, c) in terms {
            crate::add_term(&mut out.terms, &Arc::from(*x), &Int::from(*c));
        }
        out
    }

    /// A term with no coefficients is divided by the absolute value of its constant. The old
    /// `content` started its gcd fold at the constant itself, so for no coefficients it was the
    /// constant, sign included, and `primitive(-3)` was `-3 / -3 = 1` while `primitive(-1)` was
    /// `-1`. `Hull::and` reads such a row only as zero or not, so this test reads the helpers
    /// themselves.
    #[test]
    fn the_primitive_of_a_negative_constant_keeps_its_sign() {
        assert_eq!(content(&lin(&[], -3)), Int::from(3));
        assert_eq!(primitive(lin(&[], -3)), lin(&[], -1));
        assert_eq!(primitive(lin(&[], -1)), lin(&[], -1));
        assert_eq!(primitive(lin(&[], 6)), lin(&[], 1));
        assert_eq!(primitive(lin(&[], 0)), lin(&[], 0));
    }

    /// `k · r - c · p` as the two scalings and a subtraction give it, with the terms that
    /// cancel left out, and the primitive form turns the first coefficient positive.
    #[test]
    fn a_combination_of_two_rows_drops_the_terms_that_cancel() {
        let (r, p) = (
            lin(&[("x", 2), ("y", 3)], 5),
            lin(&[("x", 1), ("z", -4)], -1),
        );
        assert_eq!(
            combine(&r, &Int::from(1), &p, &Int::from(2)),
            lin(&[("y", 3), ("z", 8)], 7)
        );
        assert_eq!(
            primitive(lin(&[("x", -2), ("y", 4)], 6)),
            lin(&[("x", 1), ("y", -2)], -3)
        );
    }

    /// The join keeps the equalities both sets hold: `x == y` with `z == 1` and `x == y` with
    /// `z == 2` join to `x == y` alone, and the row a pivot substitution reads holds there.
    #[test]
    fn a_join_keeps_the_common_equalities() {
        let a = Hull::of(&[lin(&[("x", 1), ("y", -1)], 0), lin(&[("z", 1)], -1)]);
        let b = Hull::of(&[lin(&[("x", 1), ("y", -1)], 0), lin(&[("z", 1)], -2)]);
        let j = a.join(&b);
        let rows: Vec<Lin> = j.rows().cloned().collect();
        assert_eq!(rows, vec![lin(&[("x", 1), ("y", -1)], 0)]);
        // `x + y` on `x == y` is `2y` or `2x`, whichever atom the row's pivot is not.
        let r = j.reduce_form(&lin(&[("x", 1), ("y", 1)], 0));
        assert!(
            r == lin(&[("y", 2)], 0) || r == lin(&[("x", 2)], 0),
            "{r:?}"
        );
        assert!(Hull::<Lin>::empty().join(&j).rows().eq(j.rows()));
        assert!(Hull::of(&[lin(&[], 1)]).is_empty);
    }
}
