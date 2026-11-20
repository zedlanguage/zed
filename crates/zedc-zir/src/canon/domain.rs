//! Domain normal forms: the integer facts of a declaration (its interval, congruence and
//! finite-set facets) rewritten to the one representation of the set of integers they admit.
//!
//! The set admitted is the meet of the three facts. Its normal form is an interval and a
//! congruence and no finite set: the congruence is the least class holding every member, and
//! the interval's pieces are the maximal runs of class members, each with both endpoints
//! members. A finite set is always expressible this way, so `int[0..=10]` with `1 mod 4`,
//! `int[1..=9]` with `1 mod 4` and the set `{1, 5, 9}` share one normal form.

use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::{Congruence, FiniteSet, Lattice};
use zedc_lattice::revision::{reduce_congruence, reduce_finite};

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
            && self.class.contains(&Num::from(v))
            && match &self.finite {
                FiniteSet::Top => true,
                FiniteSet::Set(vs) => vs.contains(&v),
            }
    }

    /// The normal form of the facts. It admits the same integers, and two facts admitting
    /// the same integers have the same normal form.
    ///
    /// Proof (DOC-proofs-in-comments-audit-rest). Let `S` be the set the facts admit: the
    /// integers of `ints` that are in `class` and in `finite`.
    /// 1. Same integers. `reduce_finite` meets `ints` with the points of the finite set (or
    ///    keeps it for `Top`), and `reduce_congruence` moves each endpoint inward to the
    ///    nearest member of the class (or meets with the one point for modulus 0), so the
    ///    interval they return holds exactly `S`, and each finite endpoint is a member of
    ///    `class`. If it is empty, `S` is empty and the empty form below admits nothing. Else
    ///    every point of `ints` is in `S`, and the class put out holds `S` (step 2), so the
    ///    form admits `S`; `runs` only joins two pieces across a gap with no member of the
    ///    class (step 3), so the integers it adds to the interval are all outside the class
    ///    and the form still admits exactly `S`.
    /// 2. The class is the least class holding `S`, a function of `S` alone. When every piece
    ///    is one point, `least_class` gives `v mod g`, with `g` the gcd of the differences,
    ///    the least class holding those points. Otherwise some piece `[a, b]` has `a < b`
    ///    (or an infinite end), both finite ends members of `m`'s class, so `a` and `a + m`
    ///    are both in `S`; a class holding them has a modulus dividing `m`, and every
    ///    difference in `S` is a multiple of `m`, so `m` is the gcd and the class is least.
    ///    The class is built by `Congruence::new`, which takes the modulus by its magnitude
    ///    and the residue modulo it, so one class has one representation even when the
    ///    facet was built with its fields directly (they are public).
    /// 3. The interval is the maximal runs of class members in `S`, a function of `S` and the
    ///    class. Two neighboring pieces `[_, b]` and `[c, _]`, `b < c`, both ends members, have
    ///    no member strictly between them exactly when `c - b` is the modulus, the test of
    ///    `joins`; an infinite end joins nothing, and modulus 0 means one point.
    ///
    /// So the result is a function of `S`, and since it admits `S` (step 1),
    /// `normal(normal(d)) == normal(d)`: the domain rule applies at most once
    /// ([`super::canonicalize`] relies on it). Test (m0_07_canonicalization):
    /// `alpha::the_normal_form_is_the_rules_applied_one_step_at_a_time`.
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
            .map(|p| match p {
                (End::Fin(a), End::Fin(b)) if a == b => Some(a),
                _ => None,
            })
            .collect();
        let class = match (points, class) {
            (Some(vs), _) => least_class(&vs),
            // Normalized, so that one class has one representation (step 2 above).
            (None, Congruence::Class { modulus, residue }) => Congruence::new(modulus, residue),
            (None, Congruence::Bottom) => unreachable!("an empty domain returned above"),
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
/// and the greatest common divisor `g` of the differences. It is exact at every size, a
/// function of the points alone, so the normal form stays unique.
fn least_class(points: &[&Num]) -> Congruence {
    let first = points[0];
    let g = points[1..]
        .iter()
        .fold(Num::ZERO, |g, &v| g.gcd(&(v - first)));
    Congruence::new(g, first.clone())
}

/// The pieces of `ints`, whose finite endpoints are members of `class`, joined wherever the
/// gap between two pieces holds no member: the next member after a piece's upper endpoint is
/// the following piece's lower endpoint.
fn runs(ints: &IntervalSet, class: &Congruence) -> IntervalSet {
    let Congruence::Class { modulus, .. } = class else {
        return IntervalSet::empty();
    };
    let mut out: Vec<(End, End)> = Vec::new();
    for (lo, hi) in ints.pieces() {
        match out.last_mut() {
            Some((_, last)) if !modulus.is_zero() && joins(last, lo, modulus) => *last = hi.clone(),
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
