//! Domain normal forms: the integer facts of a declaration (its interval, congruence and
//! finite-set facets) rewritten to the one representation of the set of integers they admit.
//!
//! The set admitted is the meet of the three facts. Its normal form is an interval and a
//! congruence and no finite set: the congruence is the least class holding every member, and
//! the interval's pieces are the maximal runs of class members, each with both endpoints
//! members. A finite set is always expressible this way, so `int[0..=10]` with `1 mod 4`,
//! `int[1..=9]` with `1 mod 4` and the set `{1, 5, 9}` share one normal form.

use crate::store::interval::{End, IntervalSet};
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
        let points: Option<Vec<i64>> = ints
            .pieces()
            .iter()
            .map(|&p| match p {
                (End::Fin(a), End::Fin(b)) if a == b => Some(a),
                _ => None,
            })
            .collect();
        let class = match points {
            Some(vs) => vs
                .iter()
                .fold(Congruence::bottom(), |c, &v| c.join(&Congruence::single(v))),
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

/// The pieces of `ints`, whose finite endpoints are members of `class`, joined wherever the
/// gap between two pieces holds no member: the next member after a piece's upper endpoint is
/// the following piece's lower endpoint.
fn runs(ints: &IntervalSet, class: &Congruence) -> IntervalSet {
    let Congruence::Class { modulus, .. } = *class else {
        return IntervalSet::empty();
    };
    let mut out: Vec<(End, End)> = Vec::new();
    for &(lo, hi) in ints.pieces() {
        match out.last_mut() {
            Some((_, last)) if modulus > 0 && joins(*last, lo, modulus) => *last = hi,
            _ => out.push((lo, hi)),
        }
    }
    IntervalSet::from_pieces(out)
}

fn joins(hi: End, lo: End, modulus: u64) -> bool {
    match (hi, lo) {
        (End::Fin(b), End::Fin(c)) => (c as i128) - (b as i128) == modulus as i128,
        _ => false,
    }
}
