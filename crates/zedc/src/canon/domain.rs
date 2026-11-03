//! Domain normal forms: the integer facts of a declaration (its interval, congruence and
//! finite-set facets) rewritten to the one representation of the set of integers they admit.
//!
//! The set admitted is the meet of the three facts. Its normal form is an interval and a
//! congruence and no finite set: the congruence is the least class holding every member, and
//! the interval's pieces are the maximal runs of class members, each with both endpoints
//! members. A finite set is always expressible this way, so `int[0..=10]` with `1 mod 4`,
//! `int[1..=9]` with `1 mod 4` and the set `{1, 5, 9}` share one normal form.

use crate::store::interval::{End, IntervalSet, Num};
use crate::store::lattice::{Congruence, FiniteSet, Lattice};
use crate::store::revision::{reduce_congruence, reduce_finite};

/// The integer facts of a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Domain {
    /// The interval facet.
    pub ints: IntervalSet,
    /// The congruence facet.
    pub class: Congruence,
    /// The finite-set facet.
    pub finite: FiniteSet<i64>,
}

impl Domain {
    /// The facts `ints` alone.
    pub fn ints(ints: IntervalSet) -> Self {
        Domain {
            ints,
            class: Congruence::top(),
            finite: FiniteSet::Top,
        }
    }

    /// Whether `v` is admitted by all three facts.
    pub fn contains(&self, v: i64) -> bool {
        self.ints.contains(v)
            && self.class.contains(v)
            && match &self.finite {
                FiniteSet::Top => true,
                FiniteSet::Set(vs) => vs.contains(&v),
            }
    }

    /// The normal form of the facts. It admits the same integers, and two facts admitting
    /// the same integers have the same normal form.
    pub fn normal(&self) -> Self {
        // The finite set met into the interval, then the endpoints moved onto the class.
        let ints = reduce_finite(&self.ints, &self.finite).0;
        let (ints, class) = reduce_congruence(&ints, &self.class);
        if ints.is_empty() || class == Congruence::Bottom {
            return Domain {
                ints: IntervalSet::empty(),
                class: Congruence::Bottom,
                finite: FiniteSet::Top,
            };
        }
        // A piece holding two members holds two that differ by the modulus, so the class is
        // already the least one; when every piece is one point the least class is the join of
        // the points.
        let points: Option<Vec<&Num>> = ints
            .pieces()
            .iter()
            .map(|p| match p {
                (End::Fin(a), End::Fin(b)) if a == b => Some(a),
                _ => None,
            })
            .collect();
        let class = match points {
            Some(vs) => least_class(&vs),
            None => class,
        };
        Domain {
            ints: runs(&ints, &class),
            class,
            finite: FiniteSet::Top,
        }
    }

    /// The rank of the domain rule: 1 while the facts are not in normal form.
    pub fn rank(&self) -> u64 {
        u64::from(self.normal() != *self)
    }
}

/// The least class holding each of `points`, one or more: `v mod g` for the first point `v`
/// and the greatest common divisor `g` of the differences. A class's modulus and residue are
/// `i64`, so when that class does not fit, it is every integer; it is still a function of the
/// points alone, so the normal form stays unique, and the points themselves are exact.
fn least_class(points: &[&Num]) -> Congruence {
    let first = points[0];
    let g = points[1..]
        .iter()
        .fold(Num::ZERO, |g, &v| g.gcd(&(v - first)));
    let (modulus, residue) = if g.is_zero() {
        (Some(0), first.to_i64())
    } else {
        (g.to_i64(), first.mod_floor(&g).to_i64())
    };
    match (modulus, residue) {
        (Some(m), Some(r)) => Congruence::new(m as u64, r),
        _ => Congruence::top(),
    }
}

/// The pieces of `ints`, whose finite endpoints are members of `class`, joined wherever the
/// gap between two pieces holds no member: the next member after a piece's upper endpoint is
/// the following piece's lower endpoint.
fn runs(ints: &IntervalSet, class: &Congruence) -> IntervalSet {
    let Congruence::Class { modulus, .. } = *class else {
        return IntervalSet::empty();
    };
    let modulus = Num::from(modulus as i128);
    let mut out: Vec<(End, End)> = Vec::new();
    for (lo, hi) in ints.pieces() {
        match out.last_mut() {
            Some((_, last)) if !modulus.is_zero() && joins(last, lo, &modulus) => {
                *last = hi.clone()
            }
            _ => out.push((lo.clone(), hi.clone())),
        }
    }
    IntervalSet::from_pieces(out)
}

fn joins(hi: &End, lo: &End, modulus: &Num) -> bool {
    match (hi, lo) {
        (End::Fin(b), End::Fin(c)) => &(c - b) == modulus,
        _ => false,
    }
}
