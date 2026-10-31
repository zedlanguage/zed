//! Intervals with symbolic affine bounds (DESIGN.md sec:domains: "integer intervals and
//! congruences, with symbolic affine bounds (`int[0..<n]`, `int[0..<a::len]`)"; step L1.24).
//!
//! An element is an interval union over the integers, as in module `interval`, together with
//! a set of symbolic lower bounds and a set of symbolic upper bounds: the value lies in the
//! union and within every bound. A symbolic bound is an affine expression in at least one
//! symbol with an optional numeric floor, `max(c, a)` for an upper bound and `min(c, a)` for a
//! lower one; the floor is what a join with a number needs. A bound with no symbol is a number,
//! and goes into the union. Of two bounds with the same terms, one that implies the other
//! replaces it; bounds with different terms cannot be compared without the symbols' values, so
//! both are kept.
//!
//! Join keeps, for each pair of bounds with the same terms, the looser of the two, and for each
//! bound of one side, its loosening by the other side's numeric end. Meet keeps every bound of
//! either side. The order compares bounds the same way, so it is sound and not complete:
//! `int[0..=n]` is below `int[..=m]` only when its union's end is at most `m`'s floor, or it
//! has a bound with the terms of `m`. Widening widens the union and keeps only the symbolic
//! bounds the old element had, so a chain of widenings is finite.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::interval::{End, IntervalSet};
use super::lattice::{Landmarks, Lattice};

/// A symbol an affine bound names: a name in scope or its length, `n` or `a::len`. The store
/// names each symbol by its source text, unique within one store.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Sym(pub String);

/// `constant + Σ coefficient · symbol`, with no zero coefficient.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Affine {
    /// The symbols and their coefficients. Bounds are compared by this first, so the bounds
    /// with one set of terms are neighbors in a `BTreeSet`.
    pub terms: BTreeMap<Sym, i64>,
    /// The constant.
    pub constant: i64,
}

impl Affine {
    /// The number `c`.
    pub fn constant(c: i64) -> Affine {
        Affine {
            terms: BTreeMap::new(),
            constant: c,
        }
    }

    /// The symbol `s`.
    pub fn sym(s: &str) -> Affine {
        Affine {
            terms: BTreeMap::from([(Sym(s.into()), 1)]),
            constant: 0,
        }
    }

    /// `self + c`, or `None` past the 64-bit range.
    pub fn plus(&self, c: i64) -> Option<Affine> {
        Some(Affine {
            terms: self.terms.clone(),
            constant: self.constant.checked_add(c)?,
        })
    }

    /// `k · self`, or `None` past the 64-bit range.
    pub fn times(&self, k: i64) -> Option<Affine> {
        if k == 0 {
            return Some(Affine::constant(0));
        }
        let mut terms = BTreeMap::new();
        for (s, c) in &self.terms {
            terms.insert(s.clone(), c.checked_mul(k)?);
        }
        Some(Affine {
            terms,
            constant: self.constant.checked_mul(k)?,
        })
    }

    /// The value at the given symbol values, or `None` past the 128-bit range.
    pub fn eval(&self, at: &impl Fn(&Sym) -> i64) -> Option<i128> {
        self.terms
            .iter()
            .try_fold(self.constant as i128, |v, (s, c)| {
                v.checked_add((*c as i128).checked_mul(at(s) as i128)?)
            })
    }

    /// Whether the bound has no symbol.
    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }
}

impl fmt::Display for Affine {
    /// `n`, `-n`, `2 * n - m + 1`, `0`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (s, &c)) in self.terms.iter().enumerate() {
            let (sign, k) = (if c < 0 { "-" } else { "+" }, c.unsigned_abs());
            match i {
                0 if c < 0 => write!(f, "-")?,
                0 => {}
                _ => write!(f, " {sign} ")?,
            }
            if k != 1 {
                write!(f, "{k} * ")?;
            }
            write!(f, "{}", s.0)?;
        }
        match (self.terms.is_empty(), self.constant) {
            (true, c) => write!(f, "{c}"),
            (false, 0) => Ok(()),
            (false, c) if c < 0 => write!(f, " - {}", c.unsigned_abs()),
            (false, c) => write!(f, " + {c}"),
        }
    }
}

/// Which side a bound is on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Side {
    /// `x ≥ min(floor, affine)`.
    Lower,
    /// `x ≤ max(floor, affine)`.
    Upper,
}

impl Side {
    /// The floor of a bound with none: the end that `min` or `max` ignores.
    fn none(self) -> End {
        match self {
            Side::Lower => End::PosInf,
            Side::Upper => End::NegInf,
        }
    }

    /// The floor that makes a bound hold of every integer.
    fn vacuous(self) -> End {
        match self {
            Side::Lower => End::NegInf,
            Side::Upper => End::PosInf,
        }
    }

    /// The looser of two ends: the smaller for a lower bound, the larger for an upper.
    fn looser_end(self, a: End, b: End) -> End {
        match self {
            Side::Lower => a.min(b),
            Side::Upper => a.max(b),
        }
    }

    /// The looser of two constants.
    fn looser(self, a: i64, b: i64) -> i64 {
        match self {
            Side::Lower => a.min(b),
            Side::Upper => a.max(b),
        }
    }

    /// The end of the interval hull on this side.
    fn hull_end(self, ints: &IntervalSet) -> End {
        let (lo, hi) = ints.bounds().unwrap_or((End::PosInf, End::NegInf));
        match self {
            Side::Lower => lo,
            Side::Upper => hi,
        }
    }
}

/// A symbolic bound on one side: `min(floor, affine)` for a lower bound and `max(floor, affine)`
/// for an upper, where the floor is a number or, for a bound with none, the infinity `min` or
/// `max` ignores. The affine part has at least one symbol.
///
/// The floor is what a join with a number gives: a value in `[0]` or in `[1..=n]` is at most
/// `max(0, n)`, and not at most `n`, since `[1..=n]` is empty when `n < 0`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Bound {
    /// The affine part.
    pub affine: Affine,
    /// The floor.
    pub floor: End,
}

impl Bound {
    /// The bound's value at the given symbol values, or `None` past the 128-bit range.
    fn eval(&self, side: Side, at: &impl Fn(&Sym) -> i64) -> Option<i128> {
        let a = self.affine.eval(at)?;
        Some(match (side, self.floor) {
            (_, End::Fin(c)) if side == Side::Lower => a.min(c as i128),
            (_, End::Fin(c)) => a.max(c as i128),
            _ => a,
        })
    }

    /// Whether `self` is at least as tight as `other` for every symbol value: the same terms,
    /// and a constant and a floor each at least as tight.
    fn implies(&self, side: Side, other: &Bound) -> bool {
        self.affine.terms == other.affine.terms
            && side.looser(self.affine.constant, other.affine.constant) == other.affine.constant
            && side.looser_end(self.floor, other.floor) == other.floor
    }

    /// The bound both `self` and `other` imply, when they have the same terms.
    fn loosen(&self, side: Side, other: &Bound) -> Option<Bound> {
        (self.affine.terms == other.affine.terms).then(|| Bound {
            affine: Affine {
                terms: self.affine.terms.clone(),
                constant: side.looser(self.affine.constant, other.affine.constant),
            },
            floor: side.looser_end(self.floor, other.floor),
        })
    }

    /// The bound `self` and the number `end` both imply.
    fn loosen_end(&self, side: Side, end: End) -> Option<Bound> {
        let floor = side.looser_end(self.floor, end);
        (floor != side.vacuous()).then(|| Bound {
            affine: self.affine.clone(),
            floor,
        })
    }

    fn fmt_on(&self, side: Side) -> String {
        match (self.floor, side) {
            (End::Fin(c), Side::Lower) => format!("min({c}, {})", self.affine),
            (End::Fin(c), Side::Upper) => format!("max({c}, {})", self.affine),
            _ => self.affine.to_string(),
        }
    }
}

/// An interval union with symbolic bounds.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Bounds {
    ints: IntervalSet,
    lower: BTreeSet<Bound>,
    upper: BTreeSet<Bound>,
}

impl Bounds {
    /// The integers in `ints`, with no symbolic bound.
    pub fn ints(ints: IntervalSet) -> Bounds {
        Bounds::new(ints, [], [])
    }

    /// The integers in `ints` at or above each of `lower` and at or below each of `upper`.
    pub fn new(
        ints: IntervalSet,
        lower: impl IntoIterator<Item = Affine>,
        upper: impl IntoIterator<Item = Affine>,
    ) -> Bounds {
        let bound = |side: Side| {
            move |affine: Affine| Bound {
                affine,
                floor: side.none(),
            }
        };
        Bounds::from_bounds(
            ints,
            lower.into_iter().map(bound(Side::Lower)),
            upper.into_iter().map(bound(Side::Upper)),
        )
    }

    /// The integers in `ints` within each of the given bounds.
    pub fn from_bounds(
        ints: IntervalSet,
        lower: impl IntoIterator<Item = Bound>,
        upper: impl IntoIterator<Item = Bound>,
    ) -> Bounds {
        let mut b = Bounds {
            ints,
            lower: BTreeSet::new(),
            upper: BTreeSet::new(),
        };
        for l in lower {
            b.add(Side::Lower, l);
        }
        for u in upper {
            b.add(Side::Upper, u);
        }
        b.normal()
    }

    /// The range `lo..=hi` with affine ends, `None` meaning unbounded: `range(Some(0), Some(n -
    /// 1))` is `int[0..<n]`.
    pub fn range(lo: Option<Affine>, hi: Option<Affine>) -> Bounds {
        Bounds::new(IntervalSet::top(), lo, hi)
    }

    /// The interval union, without the symbolic bounds.
    pub fn concrete(&self) -> &IntervalSet {
        &self.ints
    }

    /// The symbolic bounds on one side.
    pub fn bounds(&self, side: Side) -> &BTreeSet<Bound> {
        match side {
            Side::Lower => &self.lower,
            Side::Upper => &self.upper,
        }
    }

    fn side_mut(&mut self, side: Side) -> &mut BTreeSet<Bound> {
        match side {
            Side::Lower => &mut self.lower,
            Side::Upper => &mut self.upper,
        }
    }

    /// Adds a bound: one with no symbol meets the union; otherwise it is dropped when a bound
    /// already there implies it, and drops each bound already there that it implies.
    fn add(&mut self, side: Side, b: Bound) {
        if b.affine.is_constant() {
            let c = side.looser_end(End::Fin(b.affine.constant), b.floor);
            let half = match side {
                Side::Lower => IntervalSet::range(c, End::PosInf),
                Side::Upper => IntervalSet::range(End::NegInf, c),
            };
            self.ints = self.ints.meet(&half);
            return;
        }
        let set = self.side_mut(side);
        if same_terms(set, &b.affine.terms).any(|o| o.implies(side, &b)) {
            return;
        }
        let implied: Vec<Bound> = same_terms(set, &b.affine.terms)
            .filter(|o| b.implies(side, o))
            .cloned()
            .collect();
        for o in implied {
            set.remove(&o);
        }
        set.insert(b);
    }

    /// Drops each bound the union implies, a floor at or past the union's end; and gives the
    /// bottom when the union is empty or a lower bound with no floor exceeds an upper one with
    /// the same terms and no floor.
    fn normal(mut self) -> Bounds {
        for side in [Side::Lower, Side::Upper] {
            let end = side.hull_end(&self.ints);
            self.side_mut(side)
                .retain(|b| side.looser_end(b.floor, end) != b.floor);
        }
        let crossed = self.lower.iter().any(|l| {
            same_terms(&self.upper, &l.affine.terms).any(|u| {
                l.floor == End::PosInf
                    && u.floor == End::NegInf
                    && l.affine.constant > u.affine.constant
            })
        });
        if self.ints.is_empty() || crossed {
            Bounds::bottom()
        } else {
            self
        }
    }

    /// Whether `v` is in the element at the given symbol values.
    pub fn contains(&self, v: i64, at: &impl Fn(&Sym) -> i64) -> bool {
        let x = v as i128;
        self.ints.contains(v)
            && self
                .lower
                .iter()
                .all(|l| l.eval(Side::Lower, at).is_some_and(|b| b <= x))
            && self
                .upper
                .iter()
                .all(|u| u.eval(Side::Upper, at).is_some_and(|b| x <= b))
    }

    /// The element shifted by `c`: `x + c` for each member `x`. A bound past the 64-bit range is
    /// dropped, which only widens the element.
    pub fn offset(&self, c: i64) -> Bounds {
        let shift = |s: &BTreeSet<Bound>, end: fn(i128) -> End| {
            s.iter()
                .filter_map(|b| {
                    Some(Bound {
                        affine: b.affine.plus(c)?,
                        floor: shift_end(b.floor, c, end),
                    })
                })
                .collect::<Vec<_>>()
        };
        let ints = self
            .ints
            .lift1(|(lo, hi)| vec![(shift_end(lo, c, End::lower), shift_end(hi, c, End::upper))]);
        Bounds::from_bounds(
            ints,
            shift(&self.lower, End::lower),
            shift(&self.upper, End::upper),
        )
    }

    /// The bounds on one side that every member of `a` or of `b` is within: for each pair with
    /// the same terms, the looser; and for each bound of one side, the looser of it and the
    /// other side's end.
    fn joined(side: Side, a: &Bounds, b: &Bounds) -> Vec<Bound> {
        let (sa, sb) = (a.bounds(side), b.bounds(side));
        let mut out: Vec<Bound> = sa
            .iter()
            .flat_map(|x| same_terms(sb, &x.affine.terms).filter_map(|y| x.loosen(side, y)))
            .collect();
        out.extend(
            sa.iter()
                .filter_map(|x| x.loosen_end(side, side.hull_end(&b.ints))),
        );
        out.extend(
            sb.iter()
                .filter_map(|y| y.loosen_end(side, side.hull_end(&a.ints))),
        );
        out
    }
}

/// The bounds of `set` with the given terms, which are neighbors since a bound is ordered by
/// its terms first: a range of the set, not a scan of it, so the operations on bounds over
/// many symbols are `O(k log k)` and not `O(k²)` (DESIGN.md Part G).
fn same_terms<'a>(
    set: &'a BTreeSet<Bound>,
    terms: &BTreeMap<Sym, i64>,
) -> impl Iterator<Item = &'a Bound> {
    let at = |constant, floor| Bound {
        affine: Affine {
            terms: terms.clone(),
            constant,
        },
        floor,
    };
    set.range(at(i64::MIN, End::NegInf)..=at(i64::MAX, End::PosInf))
}

/// `e + c`, rounded by `end` as a lower or an upper end.
fn shift_end(e: End, c: i64, end: fn(i128) -> End) -> End {
    match e {
        End::Fin(v) => end(v as i128 + c as i128),
        e => e,
    }
}

impl Lattice for Bounds {
    fn bottom() -> Self {
        Bounds {
            ints: IntervalSet::empty(),
            lower: BTreeSet::new(),
            upper: BTreeSet::new(),
        }
    }
    fn top() -> Self {
        Bounds::ints(IntervalSet::top())
    }
    fn join(&self, other: &Self) -> Self {
        if *self == Bounds::bottom() {
            return other.clone();
        }
        if *other == Bounds::bottom() {
            return self.clone();
        }
        Bounds::from_bounds(
            self.ints.join(&other.ints),
            Bounds::joined(Side::Lower, self, other),
            Bounds::joined(Side::Upper, self, other),
        )
    }
    fn meet(&self, other: &Self) -> Self {
        Bounds::from_bounds(
            self.ints.meet(&other.ints),
            self.lower.iter().chain(&other.lower).cloned(),
            self.upper.iter().chain(&other.upper).cloned(),
        )
    }
    /// The union widens as in module `interval`, and a symbolic bound of `next` is kept only
    /// when `self` has it. So the bounds of a chain of widenings only shrink, and the chain is
    /// finite.
    fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        if *self == Bounds::bottom() {
            return next.clone();
        }
        Bounds::from_bounds(
            self.ints.widen(&next.ints, marks),
            next.lower.intersection(&self.lower).cloned(),
            next.upper.intersection(&self.upper).cloned(),
        )
    }
    /// The union narrows as in module `interval`, and a side takes the symbolic bounds of
    /// `next` only while it has none: each side gains bounds at most once, so every chain of
    /// narrowings is finite.
    fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        let side =
            |s: &BTreeSet<_>, n: &BTreeSet<_>| if s.is_empty() { n.clone() } else { s.clone() };
        Bounds::from_bounds(
            self.ints.narrow(&next.ints, marks),
            side(&self.lower, &next.lower),
            side(&self.upper, &next.upper),
        )
    }
    /// Sound and not complete: each bound of `other` must be implied by a bound of `self` with
    /// the same terms, or by the end of `self`'s union.
    fn leq(&self, other: &Self) -> bool {
        let implied = |side: Side| {
            other.bounds(side).iter().all(|t| {
                same_terms(self.bounds(side), &t.affine.terms).any(|m| m.implies(side, t))
                    || side.looser_end(t.floor, side.hull_end(&self.ints)) == t.floor
            })
        };
        *self == Bounds::bottom()
            || (self.ints.is_subset(&other.ints) && implied(Side::Lower) && implied(Side::Upper))
    }
}

impl fmt::Display for Bounds {
    /// The design's form without the carrier: `[0..=n - 1]`, `[0..=max(0, n)]`,
    /// `[max(0, m)..]`, `[..=min(9, n)]`. A union of several pieces with symbolic bounds prints
    /// the two parts joined by `&`: `[0..=3, 5..] & [..=n]`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.lower.is_empty() && self.upper.is_empty() {
            return write!(f, "{}", self.ints);
        }
        let (lo, hi) = match self.ints.pieces() {
            [(lo, hi)] => (*lo, *hi),
            _ => {
                write!(f, "{} & ", self.ints)?;
                (End::NegInf, End::PosInf)
            }
        };
        let end = |side: Side, num: End| {
            let mut items: Vec<String> = Vec::new();
            if let End::Fin(v) = num {
                items.push(v.to_string());
            }
            items.extend(self.bounds(side).iter().map(|b| b.fmt_on(side)));
            let word = if side == Side::Lower { "max" } else { "min" };
            match items.len() {
                0 => String::new(),
                1 => items.remove(0),
                _ => format!("{word}({})", items.join(", ")),
            }
        };
        let (l, u) = (end(Side::Lower, lo), end(Side::Upper, hi));
        if u.is_empty() {
            write!(f, "[{l}..]")
        } else {
            write!(f, "[{l}..={u}]")
        }
    }
}
