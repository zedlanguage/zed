//! The lattices of the constraint store and their widenings (DESIGN.md sec:domains and
//! sec:constraints; the widening per lattice is fixed by step M0.5).
//!
//! Each lattice here is a prelude `Lattice` value written by hand (sec:checking_in_zed): its
//! source is `zed/prelude/lattice.zed`, and this module is the Rust-hosted checker's copy, which
//! row S keeps as the differential oracle.

use std::collections::BTreeSet;
use std::fmt;

use zed_kernel::Value;

use super::interval::{End, IntervalSet, Num};

/// The values written in a program, at which a widening stops a bound and a narrowing stops a
/// descent (step M0.5): each integer literal and each declared bound `k`, as `k - 1`, `k` and
/// `k + 1`, and the other literal values. A program has finitely many, so a chain that moves
/// only to landmarks and old endpoints is finite, with no count of its steps. A cell takes the
/// landmarks of its loop only (`iterate::Scopes`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Landmarks {
    ints: BTreeSet<Num>,
    values: BTreeSet<Value>,
}

impl Landmarks {
    /// No landmarks: a bound that moves goes to an old endpoint or to infinity.
    pub fn none() -> Self {
        Landmarks::default()
    }

    /// The landmarks of the given integer literals and other values.
    pub fn of(
        ints: impl IntoIterator<Item = impl Into<Num>>,
        values: impl IntoIterator<Item = Value>,
    ) -> Self {
        let mut out = Landmarks {
            values: values.into_iter().collect(),
            ..Landmarks::default()
        };
        for k in ints {
            let k: Num = k.into();
            out.ints.extend([&k - &Num::ONE, &k + &Num::ONE, k]);
        }
        out
    }

    /// Adds the landmarks of `other`.
    pub fn extend(&mut self, other: &Landmarks) {
        self.ints.extend(other.ints.iter().cloned());
        self.values.extend(other.values.iter().cloned());
    }

    /// The integer landmarks, in order.
    pub fn ints(&self) -> &BTreeSet<Num> {
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
        marks.ints.contains(&Num::from(*self))
    }
}

impl Mark for Value {
    fn marked(&self, marks: &Landmarks) -> bool {
        match self {
            Value::Int(n) => marks.ints.contains(&Num::from(*n)),
            Value::Big(n) => marks.ints.contains(&Num::from(&**n)),
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
/// `residue`, and modulus 1 is every integer. The residue is kept in `0..modulus`. Both are
/// [`Num`]s, so a class past the 64-bit range is held exactly.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Congruence {
    /// No value.
    Bottom,
    /// The integers `x` with `x mod modulus == residue`.
    Class {
        /// The modulus, at least 0, and 0 for a single value.
        modulus: Num,
        /// The residue, in `0..modulus`, or the value when the modulus is 0.
        residue: Num,
    },
}

/// The inverse of `a` modulo `n`, for `a` and `n` coprime and `n >= 1`, in `0..n` (0 when `n`
/// is 1).
fn inverse(a: &Num, n: &Num) -> Num {
    // The extended Euclidean algorithm on (a, n), keeping only the coefficient of a.
    let (mut r0, mut r1) = (a.rem_euclid(n), n.clone());
    let (mut t0, mut t1) = (Num::ONE, Num::ZERO);
    while !r1.is_zero() {
        let q = r0.div_floor(&r1);
        let r2 = &r0 - &(&q * &r1);
        let t2 = &t0 - &(&q * &t1);
        (r0, r1) = (r1, r2);
        (t0, t1) = (t1, t2);
    }
    t0.rem_euclid(n)
}

impl Congruence {
    /// The class `residue mod modulus`, normalized: the modulus taken by its magnitude.
    pub fn new(modulus: impl Into<Num>, residue: impl Into<Num>) -> Self {
        let (modulus, residue) = (modulus.into().abs(), residue.into());
        let residue = if modulus.is_zero() {
            residue
        } else {
            residue.rem_euclid(&modulus)
        };
        Congruence::Class { modulus, residue }
    }

    /// The one value `v`.
    pub fn single(v: impl Into<Num>) -> Self {
        Congruence::new(Num::ZERO, v)
    }

    /// Whether `v` is a member.
    pub fn contains(&self, v: &Num) -> bool {
        match self {
            Congruence::Bottom => false,
            Congruence::Class { modulus, residue } if modulus.is_zero() => v == residue,
            Congruence::Class { modulus, residue } => v.rem_euclid(modulus) == *residue,
        }
    }
}

impl std::fmt::Display for Congruence {
    /// `{}`, `5`, `1 mod 3`, or `any` for every integer.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Congruence::Bottom => write!(f, "{{}}"),
            Congruence::Class { modulus, residue } if modulus.is_zero() => write!(f, "{residue}"),
            Congruence::Class { modulus, .. } if *modulus == Num::ONE => write!(f, "any"),
            Congruence::Class { modulus, residue } => write!(f, "{residue} mod {modulus}"),
        }
    }
}

impl Lattice for Congruence {
    fn bottom() -> Self {
        Congruence::Bottom
    }
    fn top() -> Self {
        Congruence::new(Num::ONE, Num::ZERO)
    }
    fn join(&self, other: &Self) -> Self {
        use Congruence::*;
        match (self, other) {
            (Bottom, c) | (c, Bottom) => c.clone(),
            (
                Class {
                    modulus: m,
                    residue: r,
                },
                Class {
                    modulus: n,
                    residue: s,
                },
            ) => Congruence::new(m.gcd(n).gcd(&(r - s)), r.clone()),
        }
    }
    fn meet(&self, other: &Self) -> Self {
        use Congruence::*;
        match (self, other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (
                Class {
                    modulus,
                    residue: v,
                },
                c,
            )
            | (
                c,
                Class {
                    modulus,
                    residue: v,
                },
            ) if modulus.is_zero() => {
                if c.contains(v) {
                    Congruence::single(v.clone())
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
                // (m/g)·k ≡ (s - r)/g mod n/g. Exact for every size: the lcm of two moduli
                // past the 64-bit range is held as a `Num`.
                let g = m.gcd(n);
                let d = s - r;
                if !d.rem_euclid(&g).is_zero() {
                    return Bottom;
                }
                let (m1, n1) = (m.div_floor(&g), n.div_floor(&g));
                let k = &d.div_floor(&g).rem_euclid(&n1) * &inverse(&m1, &n1);
                Congruence::new(&m1 * n, r + &(m * &k.rem_euclid(&n1)))
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
    ///
    /// Complexity tradeoff: a congruence below the top that `next` refines to a larger modulus
    /// keeps the old one, so a loop that shows `0 mod 4` after `0 mod 2` keeps `0 mod 2`.
    /// Why: without this, a descending chain need not end. Trigger: a narrowing from a class of
    /// modulus other than 1 to a class of a larger modulus. Test:
    /// `m0_05_widening_and_iteration::widening::a_congruence_narrows_at_most_three_times`.
    /// COMPLEXITY.md row C9. The limit of the chain is not computable in general; a closer rule
    /// would accept a refinement whose modulus is among the program's literals (a landmark
    /// rule, as the interval narrowing has), which keeps each chain finite.
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        match next {
            _ if *self == Congruence::top() => next.clone(),
            Congruence::Bottom => Congruence::Bottom,
            Congruence::Class { modulus, .. } if modulus.is_zero() => next.clone(),
            _ => self.clone(),
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
    ///
    /// Complexity tradeoff: a set that gains a member the program does not write goes to the
    /// top, so all members are lost, even when the loop adds only finitely many. Why: finite
    /// sets form infinite ascending chains, so a fixpoint needs a widening; with this one a
    /// chain rises at most once per landmark. Trigger: a widening whose join adds a value
    /// that is not a landmark. Test:
    /// `m0_05_widening_and_iteration::widening::a_finite_set_widens_to_the_top_at_a_member_the_program_does_not_write`.
    /// COMPLEXITY.md row S13. A complete solution would need the loop's exact set of values,
    /// which is undecidable in general.
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
        Card(IntervalSet::range(End::of(0), End::PosInf))
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
                for v in window.clone().map(Num::from) {
                    assert!(
                        !(a.contains(&v) || b.contains(&v)) || j.contains(&v),
                        "{a:?} ⊔ {b:?}"
                    );
                    assert_eq!(
                        m.contains(&v),
                        a.contains(&v) && b.contains(&v),
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
        let c = Card::range(End::of(2), End::of(3));
        let none = Landmarks::none();
        assert_eq!(
            c.widen(&Card::range(End::of(1), End::of(3)), &none),
            Card::range(End::of(0), End::of(3))
        );
        assert_eq!(
            c.widen(&Card::range(End::of(2), End::of(4)), &none),
            Card::range(End::of(2), PosInf)
        );
        assert_eq!(
            Card::range(NegInf, End::of(1)),
            Card::range(End::of(0), End::of(1))
        );
    }
}
