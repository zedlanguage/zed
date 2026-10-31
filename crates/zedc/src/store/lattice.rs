//! The lattices of the constraint store and their widenings (DESIGN.md sec:domains and
//! sec:constraints; the widening per lattice is fixed by step M0.5).
//!
//! Each lattice here is a prelude `Lattice` value written by hand (sec:checking_in_zed): its
//! source is `zed/prelude/lattice.zed`, and this module is the Rust-hosted checker's copy, which
//! row S keeps as the differential oracle.

use std::collections::BTreeSet;
use std::fmt;

use zed_kernel::Value;

use super::interval::{End, IntervalSet};

/// The most members a finite set keeps when the reduction lists an interval's integers
/// (docs/thresholds.md, replacement 3c removes it).
pub const FINITE_SET_LIMIT: usize = 64;

/// The values written in a program, at which a widening stops a bound and a narrowing stops a
/// descent (step M0.5): each integer literal and each declared bound `k`, as `k - 1`, `k` and
/// `k + 1`, and the other literal values. A program has finitely many, so a chain that moves
/// only to landmarks and old endpoints is finite, with no count of its steps.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Landmarks {
    ints: BTreeSet<i64>,
    values: BTreeSet<Value>,
}

impl Landmarks {
    /// No landmarks: a bound that moves goes to an old endpoint or to infinity.
    pub fn none() -> Self {
        Landmarks::default()
    }

    /// The landmarks of the given integer literals and other values.
    pub fn of(
        ints: impl IntoIterator<Item = i64>,
        values: impl IntoIterator<Item = Value>,
    ) -> Self {
        let mut out = Landmarks {
            values: values.into_iter().collect(),
            ..Landmarks::default()
        };
        for k in ints {
            out.ints.extend(
                [k.checked_sub(1), Some(k), k.checked_add(1)]
                    .into_iter()
                    .flatten(),
            );
        }
        out
    }

    /// The integer landmarks, in order.
    pub fn ints(&self) -> &BTreeSet<i64> {
        &self.ints
    }

    /// Whether `v` is a landmark.
    pub fn has(&self, v: &impl Mark) -> bool {
        v.marked(self)
    }
}

/// A member of a finite set, which a widening keeps exact when it is a landmark.
pub trait Mark {
    /// Whether the value is one of `marks`.
    fn marked(&self, marks: &Landmarks) -> bool;
}

impl Mark for i64 {
    fn marked(&self, marks: &Landmarks) -> bool {
        marks.ints.contains(self)
    }
}

impl Mark for Value {
    fn marked(&self, marks: &Landmarks) -> bool {
        match self {
            Value::Int(n) => marks.ints.contains(n),
            v => marks.values.contains(v),
        }
    }
}

/// A lattice of the store, with the widening that bounds its ascending chains and the
/// narrowing that bounds its descending ones.
pub trait Lattice: Clone + PartialEq + fmt::Debug {
    /// The least element: no value.
    fn bottom() -> Self;
    /// The greatest element: no information.
    fn top() -> Self;
    /// The least upper bound.
    fn join(&self, other: &Self) -> Self;
    /// The greatest lower bound.
    fn meet(&self, other: &Self) -> Self;
    /// `self ∇ next` for `next ⊒ self`: an upper bound of both such that every chain of
    /// widenings is finite. For a lattice of finite height it is the join.
    fn widen(&self, next: &Self, marks: &Landmarks) -> Self;
    /// `self Δ next` for `next ⊑ self`: a value between the two such that every chain of
    /// narrowings is finite. For a lattice with no infinite descending chain it is `next`.
    fn narrow(&self, next: &Self, marks: &Landmarks) -> Self;
    /// The order: whether `self ⊑ other`. The default reads it off the meet, which is exact
    /// for a lattice whose elements have one representation each.
    fn leq(&self, other: &Self) -> bool {
        self.meet(other) == *self
    }
}

impl Lattice for IntervalSet {
    fn bottom() -> Self {
        IntervalSet::empty()
    }
    fn top() -> Self {
        IntervalSet::top()
    }
    fn join(&self, other: &Self) -> Self {
        IntervalSet::join(self, other)
    }
    fn meet(&self, other: &Self) -> Self {
        IntervalSet::meet(self, other)
    }
    fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        IntervalSet::widen(self, next, marks)
    }
    fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        IntervalSet::narrow(self, next, marks)
    }
}

/// A congruence class `residue mod modulus`, or the bottom. Modulus 0 is the one value
/// `residue`, and modulus 1 is every integer. The residue is kept in `0..modulus`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Congruence {
    /// No value.
    Bottom,
    /// The integers `x` with `x mod modulus == residue`.
    Class {
        /// The modulus, 0 for a single value.
        modulus: u64,
        /// The residue, in `0..modulus`, or the value when the modulus is 0.
        residue: i64,
    },
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The inverse of `a` modulo `n`, for `a` and `n` coprime, in `0..n` (1 when `n` is 1).
fn inverse(a: i128, n: i128) -> i128 {
    // The extended Euclidean algorithm on (a, n), keeping only the coefficient of a.
    let (mut r0, mut r1, mut t0, mut t1) = (a.rem_euclid(n), n, 1i128, 0i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    t0.rem_euclid(n)
}

impl Congruence {
    /// The class `residue mod modulus`, normalized.
    pub fn new(modulus: u64, residue: i64) -> Self {
        let residue = if modulus == 0 {
            residue
        } else {
            residue.rem_euclid(modulus as i64)
        };
        Congruence::Class { modulus, residue }
    }

    /// The one value `v`.
    pub fn single(v: i64) -> Self {
        Congruence::new(0, v)
    }

    /// Whether `v` is a member.
    pub fn contains(&self, v: i64) -> bool {
        match *self {
            Congruence::Bottom => false,
            Congruence::Class {
                modulus: 0,
                residue,
            } => v == residue,
            Congruence::Class { modulus, residue } => v.rem_euclid(modulus as i64) == residue,
        }
    }
}

impl std::fmt::Display for Congruence {
    /// `{}`, `5`, `1 mod 3`, or `any` for every integer.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Congruence::Bottom => write!(f, "{{}}"),
            Congruence::Class {
                modulus: 0,
                residue,
            } => write!(f, "{residue}"),
            Congruence::Class { modulus: 1, .. } => write!(f, "any"),
            Congruence::Class { modulus, residue } => write!(f, "{residue} mod {modulus}"),
        }
    }
}

impl Lattice for Congruence {
    fn bottom() -> Self {
        Congruence::Bottom
    }
    fn top() -> Self {
        Congruence::new(1, 0)
    }
    fn join(&self, other: &Self) -> Self {
        use Congruence::*;
        match (*self, *other) {
            (Bottom, c) | (c, Bottom) => c,
            (
                Class {
                    modulus: m,
                    residue: r,
                },
                Class {
                    modulus: n,
                    residue: s,
                },
            ) => {
                let d = r.abs_diff(s);
                Congruence::new(gcd(gcd(m, n), d), r)
            }
        }
    }
    fn meet(&self, other: &Self) -> Self {
        use Congruence::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (
                Class {
                    modulus: 0,
                    residue: v,
                },
                c,
            )
            | (
                c,
                Class {
                    modulus: 0,
                    residue: v,
                },
            ) => {
                if c.contains(v) {
                    Congruence::single(v)
                } else {
                    Bottom
                }
            }
            (
                Class {
                    modulus: m,
                    residue: r,
                },
                Class {
                    modulus: n,
                    residue: s,
                },
            ) => {
                // The Chinese remainder theorem: solvable iff r ≡ s mod g = gcd(m, n), and then
                // the solutions are one class modulo lcm(m, n): x = r + m·k, where
                // (m/g)·k ≡ (s - r)/g mod n/g.
                let g = gcd(m, n);
                if (s as i128 - r as i128).rem_euclid(g as i128) != 0 {
                    return Bottom;
                }
                let (m1, n1) = ((m / g) as i128, (n / g) as i128);
                let Ok(l) = u64::try_from(m1 * n as i128) else {
                    // The class is too fine to represent; either operand is a sound bound.
                    return if m >= n { *self } else { *other };
                };
                let k = ((s as i128 - r as i128) / g as i128).rem_euclid(n1) * inverse(m1, n1);
                let x = (r as i128 + m as i128 * k.rem_euclid(n1)).rem_euclid(l as i128);
                Congruence::new(l, x as i64)
            }
        }
    }
    /// Above any class other than the bottom, an ascending chain divides the modulus at each
    /// step, so it is finite: the widening is the join.
    fn widen(&self, next: &Self, _: &Landmarks) -> Self {
        self.join(next)
    }
    /// A descending chain can multiply the modulus without end (`0 mod 2`, `0 mod 4`, ...), so
    /// the narrowing takes `next` only from the top, or when `next` is one value or none: a
    /// chain of narrowings changes at most three times.
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        match next {
            _ if *self == Congruence::top() => *next,
            Congruence::Bottom | Congruence::Class { modulus: 0, .. } => *next,
            _ => *self,
        }
    }
}

/// A finite set of scalars or atoms, or the top: no finite-set fact.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FiniteSet<T: Ord> {
    /// Exactly these values.
    Set(BTreeSet<T>),
    /// Any value of the carrier.
    Top,
}

impl<T: Ord + Clone> FiniteSet<T> {
    /// The set of the given values.
    pub fn of(values: impl IntoIterator<Item = T>) -> Self {
        FiniteSet::Set(values.into_iter().collect())
    }
}

impl<T: Ord + Clone + fmt::Debug + Mark> Lattice for FiniteSet<T> {
    fn bottom() -> Self {
        FiniteSet::Set(BTreeSet::new())
    }
    fn top() -> Self {
        FiniteSet::Top
    }
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (FiniteSet::Set(a), FiniteSet::Set(b)) => FiniteSet::Set(a.union(b).cloned().collect()),
            _ => FiniteSet::Top,
        }
    }
    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (FiniteSet::Set(a), FiniteSet::Set(b)) => {
                FiniteSet::Set(a.intersection(b).cloned().collect())
            }
            (FiniteSet::Top, s) | (s, FiniteSet::Top) => s.clone(),
        }
    }
    /// The join when every member it adds is a landmark, else the top; the bottom widens to
    /// `next`. The members of a chain are the first element's and landmarks, so it rises
    /// finitely often.
    fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        if *self == FiniteSet::bottom() {
            return next.clone();
        }
        match (self, self.join(next)) {
            (FiniteSet::Set(old), FiniteSet::Set(j))
                if j.iter().all(|v| old.contains(v) || v.marked(marks)) =>
            {
                FiniteSet::Set(j)
            }
            _ => FiniteSet::Top,
        }
    }
    /// A descending chain leaves the top at most once and then loses members: it is `next`.
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        next.clone()
    }
}

/// A cardinality or a length: one interval of the nonnegative integers (sec:domains, `card` and
/// `len`). It has no pieces, since a level's size is one interval in every refinement.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Card(IntervalSet);

impl Card {
    /// The sizes from `lo` to `hi`.
    pub fn range(lo: End, hi: End) -> Self {
        Card(IntervalSet::range(lo, hi).meet(&Card::top().0))
    }

    /// The interval.
    pub fn interval(&self) -> &IntervalSet {
        &self.0
    }
}

impl Lattice for Card {
    fn bottom() -> Self {
        Card(IntervalSet::empty())
    }
    fn top() -> Self {
        Card(IntervalSet::range(End::Fin(0), End::PosInf))
    }
    fn join(&self, other: &Self) -> Self {
        Card(self.0.join(&other.0).hull())
    }
    fn meet(&self, other: &Self) -> Self {
        Card(self.0.meet(&other.0))
    }
    /// The interval widening, whose `-inf` is then the least size, 0.
    fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        Card(self.0.widen(&next.0, marks).meet(&Card::top().0))
    }
    fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        Card(self.0.narrow(&next.0, marks).meet(&Card::top().0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use End::*;

    fn classes() -> Vec<Congruence> {
        let mut out = vec![Congruence::Bottom];
        for m in 0..=6u64 {
            for r in 0..m.max(1) as i64 {
                out.push(Congruence::new(m, r));
            }
        }
        out.extend((-3..=3).map(Congruence::single));
        out
    }

    #[test]
    fn congruence_join_and_meet_agree_with_their_members() {
        // On -30..=30, the join contains both operands and the meet is exactly the common
        // members.
        let window = -30..=30i64;
        for a in classes() {
            for b in classes() {
                let (j, m) = (a.join(&b), a.meet(&b));
                for v in window.clone() {
                    assert!(
                        !(a.contains(v) || b.contains(v)) || j.contains(v),
                        "{a:?} ⊔ {b:?}"
                    );
                    assert_eq!(
                        m.contains(v),
                        a.contains(v) && b.contains(v),
                        "{a:?} ⊓ {b:?} at {v}"
                    );
                }
            }
        }
    }

    #[test]
    fn congruence_join_is_the_least_class_above_both() {
        assert_eq!(
            Congruence::single(1).join(&Congruence::single(5)),
            Congruence::new(4, 1)
        );
        assert_eq!(
            Congruence::new(4, 1).join(&Congruence::single(3)),
            Congruence::new(2, 1)
        );
        assert_eq!(
            Congruence::new(4, 1).join(&Congruence::new(6, 1)),
            Congruence::new(2, 1)
        );
        assert_eq!(
            Congruence::new(2, 1).join(&Congruence::single(2)),
            Congruence::top()
        );
    }

    #[test]
    fn finite_sets_widen_to_the_top_unless_the_new_members_are_landmarks() {
        let small = FiniteSet::of(0..100);
        let none = Landmarks::none();
        assert_eq!(FiniteSet::bottom().widen(&small, &none), small);
        let more = small.join(&FiniteSet::of([200]));
        assert_eq!(small.widen(&more, &none), FiniteSet::Top);
        assert_eq!(small.widen(&more, &Landmarks::of([200], [])), more);
        assert_eq!(FiniteSet::of([1]).meet(&FiniteSet::Top), FiniteSet::of([1]));
    }

    #[test]
    fn a_cardinality_never_goes_below_zero() {
        let c = Card::range(Fin(2), Fin(3));
        let none = Landmarks::none();
        assert_eq!(
            c.widen(&Card::range(Fin(1), Fin(3)), &none),
            Card::range(Fin(0), Fin(3))
        );
        assert_eq!(
            c.widen(&Card::range(Fin(2), Fin(4)), &none),
            Card::range(Fin(2), PosInf)
        );
        assert_eq!(Card::range(NegInf, Fin(1)), Card::range(Fin(0), Fin(1)));
    }
}
