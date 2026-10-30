//! The lattices of the constraint store and their widenings (DESIGN.md sec:domains and
//! sec:constraints; the widening per lattice is fixed by step M0.5).
//!
//! Each lattice here is a prelude `Lattice` value written by hand (sec:checking_in_zed): its
//! source is `zed/prelude/lattice.zed`, and this module is the Rust-hosted checker's copy, which
//! row S keeps as the differential oracle.

use std::collections::BTreeSet;
use std::fmt;

use super::interval::{End, IntervalSet};

/// The most members a finite set keeps at a widening point; a widening that would exceed it
/// gives the top (step M0.5).
pub const FINITE_SET_LIMIT: usize = 64;

/// A lattice of the store, with the widening that bounds its ascending chains.
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
    fn widen(&self, next: &Self) -> Self;
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
    fn widen(&self, next: &Self) -> Self {
        IntervalSet::widen(self, next)
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
    fn widen(&self, next: &Self) -> Self {
        self.join(next)
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

impl<T: Ord + Clone + fmt::Debug> Lattice for FiniteSet<T> {
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
    /// The join while it has at most [`FINITE_SET_LIMIT`] members, else the top: a chain
    /// rises at most that many times before it reaches the top.
    fn widen(&self, next: &Self) -> Self {
        match self.join(next) {
            FiniteSet::Set(s) if s.len() > FINITE_SET_LIMIT => FiniteSet::Top,
            j => j,
        }
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
    fn widen(&self, next: &Self) -> Self {
        Card(self.0.widen(&next.0).meet(&Card::top().0))
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
    fn finite_sets_widen_to_the_top_past_the_limit() {
        let small = FiniteSet::of(0..FINITE_SET_LIMIT as i64);
        assert_eq!(FiniteSet::bottom().widen(&small), small);
        assert_eq!(
            small.widen(&FiniteSet::of([FINITE_SET_LIMIT as i64])),
            FiniteSet::Top
        );
        assert_eq!(FiniteSet::of([1]).meet(&FiniteSet::Top), FiniteSet::of([1]));
    }

    #[test]
    fn a_cardinality_never_goes_below_zero() {
        let c = Card::range(Fin(2), Fin(3));
        assert_eq!(
            c.widen(&Card::range(Fin(1), Fin(3))),
            Card::range(Fin(0), Fin(3))
        );
        assert_eq!(
            c.widen(&Card::range(Fin(2), Fin(4))),
            Card::range(Fin(2), PosInf)
        );
        assert_eq!(Card::range(NegInf, Fin(1)), Card::range(Fin(0), Fin(1)));
    }
}
