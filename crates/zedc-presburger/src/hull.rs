//! The affine hull of a set of integer points (Karr's join, step L1.39), over this crate's
//! terms: [`zedc_affine::hull::Hull`] of [`Lin`], and the reduction of a constraint by it. The
//! hull, its join and the citation of Karr's paper are at `zedc_affine::hull`, where they moved
//! from this file (plan row DRY-affine-crate-2026-11-26).

use std::collections::BTreeMap;

use super::presburger::{Atom, Con, Formula, Lin, Rel};
use zedc_affine::hull::Form;
use zedc_int::int::Int;

/// The affine hull of a set of points, as the equalities that hold on it.
pub type Hull = zedc_affine::hull::Hull<Lin>;

impl Form for Lin {
    type Atom = Atom;
    fn terms(&self) -> &BTreeMap<Atom, Int> {
        &self.terms
    }
    fn constant(&self) -> &Int {
        &self.constant
    }
    fn parts_mut(&mut self) -> (&mut BTreeMap<Atom, Int>, &mut Int) {
        (&mut self.terms, &mut self.constant)
    }
}

/// A constraint that holds at the same points of `hull` as `c`, with each row's pivot replaced
/// by the rest of its row ([`zedc_affine::hull::Hull::reduce_form`]). The result's coefficients
/// have no common factor: a `>=` constant is rounded down, and an equality whose constant the
/// factor does not divide is `false`.
pub fn reduce(hull: &Hull, c: &Con) -> Formula {
    let mut lin = hull.reduce_form(&c.lin);
    if lin.terms.is_empty() {
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
    // The proof that the division keeps the integer points is at
    // `zedc_affine::row_divisor`.
    match zedc_affine::row_divisor(lin.terms.values(), &lin.constant, c.rel == Rel::Eq) {
        zedc_affine::Divisor::Keep => {}
        zedc_affine::Divisor::Infeasible => return Formula::bottom(),
        zedc_affine::Divisor::By(g) => {
            zedc_affine::divide_row(&mut lin.terms, &mut lin.constant, &g)
        }
    }
    Formula::Con(Con { lin, rel: c.rel })
}
