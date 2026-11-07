//! The affine hull of a set of integer points (Karr's join, step L1.39): the affine equalities
//! that hold at every point, and the join that keeps the equalities two sets both satisfy.
//!
//! The equalities are kept in reduced row echelon form over the rationals, each row scaled to
//! integers with no common factor and its first coefficient positive. No row mentions another
//! row's pivot. A new row's pivot is its atom the fewest rows mention, the first of them on a
//! tie, so that adding it rewrites as few rows as it can: rows `x1 - x2`, `x1 - x3`, … each
//! take their last atom and rewrite none, where taking `x1` would rewrite every row before.
//! Two hulls of one set may then have different rows. A row `t` means `t == 0`. The rows are in persistent maps, so a hull made from another
//! by a few changes shares the rest with it, and the join of the two finds the rows that
//! differ in time near their number. Coefficients are unbounded integers.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use imbl::OrdMap;
use imbl::ordmap::DiffItem;

use super::presburger::{Atom, Con, Formula, Lin, Rel};
use zedc_int::int::Int;

/// The affine hull of a set of points, as the equalities that hold on it.
#[derive(Clone, Debug, Default)]
pub struct Hull {
    /// The rows by their pivots.
    rows: OrdMap<Atom, Arc<Lin>>,
    /// The pivots of the rows that mention each atom other than their pivot.
    uses: OrdMap<Atom, OrdMap<Atom, ()>>,
    /// Whether the set has no point.
    pub is_empty: bool,
}

impl Hull {
    /// The hull of every point: no equality.
    pub fn all() -> Hull {
        Hull::default()
    }

    /// The hull of the empty set.
    pub fn empty() -> Hull {
        Hull {
            is_empty: true,
            ..Hull::default()
        }
    }

    /// The hull of the points where each term of `terms` is zero.
    pub fn of<'a>(terms: impl IntoIterator<Item = &'a Lin>) -> Hull {
        terms.into_iter().fold(Hull::all(), |h, t| h.and(t))
    }

    /// The rows, in pivot order.
    pub fn rows(&self) -> impl Iterator<Item = &Lin> {
        self.rows.values().map(|t| &**t)
    }

    /// A constraint that holds at the same points of the hull as `c`, with each row's pivot
    /// replaced by the rest of its row: for a row `k * p + s` and `c` of `a * p + r`, the term
    /// `|k| * (a * p + r) - sign(k) * a * (k * p + s)`, which mentions no `p`. One pass
    /// suffices, since no row mentions another's pivot. The result's coefficients have no
    /// common factor: a `>=` constant is rounded down, and an equality whose constant the
    /// factor does not divide is `false`.
    pub fn reduce(&self, c: &Con) -> Formula {
        let mut lin = c.lin.clone();
        for a in c.lin.terms.keys() {
            if let Some(t) = self.rows.get(a) {
                let k = &t.terms[a];
                let s = if k.is_negative() {
                    -&lin.terms[a]
                } else {
                    lin.terms[a].clone()
                };
                lin = lin.times(k.abs()).minus(&t.times(s));
            }
        }
        let g = lin.terms.values().fold(Int::ZERO, |g, c| g.gcd(c));
        if g.is_zero() {
            let holds = match c.rel {
                Rel::Ge => !lin.constant.is_negative(),
                Rel::Eq => lin.constant.is_zero(),
            };
            return if holds {
                Formula::top()
            } else {
                Formula::bottom()
            };
        }
        if c.rel == Rel::Eq && !lin.constant.mod_floor(&g).is_zero() {
            return Formula::bottom();
        }
        let constant = lin.constant.div_floor(&g);
        let terms = lin
            .terms
            .into_iter()
            .map(|(a, k)| (a, k.div_floor(&g)))
            .collect();
        Formula::Con(Con {
            lin: Lin { terms, constant },
            rel: c.rel,
        })
    }

    /// The hull of the points of this one where `t` is zero. The hull is taken by value, so
    /// that rows and uses it holds alone are changed in place rather than copied.
    pub fn and(mut self, t: &Lin) -> Hull {
        if self.is_empty {
            return self;
        }
        let mut r = t.clone();
        for a in t.terms.keys() {
            if let Some(p) = self.rows.get(a) {
                r = eliminate(&r, p, a);
            }
        }
        if r.terms.is_empty() {
            return if r.constant.is_zero() {
                self
            } else {
                Hull::empty()
            };
        }
        let r = primitive(r);
        let pivot = r
            .terms
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
            let now = eliminate(row, &r, &pivot);
            used(&mut self.uses, row, q, false);
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
    pub fn join(mut self, other: &Hull) -> Hull {
        if self.is_empty {
            return other.clone();
        }
        if other.is_empty {
            return self;
        }
        let (mut gone, mut a, mut b) = (Vec::new(), Vec::new(), Vec::new());
        for d in self.rows.diff(&other.rows) {
            let (s, t) = match d {
                DiffItem::Add(_, t) => (None, Some(t)),
                DiffItem::Remove(p, s) => (Some((p, s)), None),
                DiffItem::Update { old, new } => (Some(old), Some(new.1)),
            };
            if let Some((p, s)) = s {
                gone.push(p.clone());
                a.push(s.clone());
            }
            if let Some(t) = t {
                b.push(t.clone());
            }
        }
        for (p, s) in gone.iter().zip(&a) {
            self.rows.remove(p);
            used(&mut self.uses, s, p, false);
        }
        // The common rows are reduced against each other already.
        intersect(&a, &b).iter().fold(self, |h, t| h.and(t))
    }
}

impl fmt::Display for Hull {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty {
            return write!(f, "empty");
        }
        let rows: Vec<String> = self.rows().map(|t| format!("{t} == 0")).collect();
        write!(f, "{}", rows.join(", "))
    }
}

/// Adds the row `t` at `pivot` to `uses`, or removes it.
fn used(uses: &mut OrdMap<Atom, OrdMap<Atom, ()>>, t: &Lin, pivot: &Atom, add: bool) {
    for a in t.terms.keys().filter(|a| *a != pivot) {
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

/// `r` with the atom `a` removed by adding a multiple of `p`, whose coefficient of `a` is
/// positive.
fn eliminate(r: &Lin, p: &Lin, a: &Atom) -> Lin {
    match r.terms.get(a) {
        None => r.clone(),
        Some(c) => primitive(r.times(p.terms[a].clone()).minus(&p.times(c.clone()))),
    }
}

/// The gcd of a term's coefficients and constant.
fn content(t: &Lin) -> Int {
    t.terms.values().fold(t.constant.clone(), |g, c| g.gcd(c))
}

/// `t` divided by `k`, above zero, which divides each coefficient and the constant.
fn over(t: &Lin, k: &Int) -> Lin {
    Lin {
        terms: t
            .terms
            .iter()
            .map(|(a, c)| (a.clone(), c.div_floor(k)))
            .collect(),
        constant: t.constant.div_floor(k),
    }
}

/// `t` divided by the gcd of its coefficients and constant, its first coefficient positive.
fn primitive(t: Lin) -> Lin {
    let g = content(&t);
    if g.is_zero() {
        return t;
    }
    let t = if g.is_unit() { t } else { over(&t, &g) };
    if t.terms.values().next().is_some_and(Int::is_negative) {
        t.times(-1)
    } else {
        t
    }
}

/// Terms spanning the terms both `a` and `b` span (Zassenhaus): each term `t` of `a` enters as
/// the pair `(t, t)` and each of `b` as `(t, 0)`, and the pairs are brought to echelon form on
/// their first halves; the second half of a pair whose first half becomes zero is a sum of
/// terms of `a` that is also a sum of terms of `b`.
fn intersect(a: &[Arc<Lin>], b: &[Arc<Lin>]) -> Vec<Lin> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    // The pairs by the first atom of their first half; `None` for a first half that is a
    // constant.
    let mut pivots: BTreeMap<Option<Atom>, (Lin, Lin)> = BTreeMap::new();
    let mut out = Vec::new();
    let pairs = a
        .iter()
        .map(|t| ((**t).clone(), (**t).clone()))
        .chain(b.iter().map(|t| ((**t).clone(), Lin::default())));
    for (mut l, mut r) in pairs {
        loop {
            if l.terms.is_empty() && l.constant.is_zero() {
                out.push(r);
                break;
            }
            let k = l.terms.keys().next().cloned();
            let Some((pl, pr)) = pivots.get(&k) else {
                pivots.insert(k, (l, r));
                break;
            };
            let (c, cp) = match &k {
                None => (&l.constant, &pl.constant),
                Some(k) => (&l.terms[k], &pl.terms[k]),
            };
            let nl = l.times(cp.clone()).minus(&pl.times(c.clone()));
            let nr = r.times(cp.clone()).minus(&pr.times(c.clone()));
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
