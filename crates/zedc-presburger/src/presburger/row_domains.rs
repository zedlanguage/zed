//! The answer of one equation over atoms each confined to a finite union of ranges, when its
//! residue or its ends settle it (PRES-disj-cost-xr).
//!
//! A formula such as `(y[i] == 0 || y[i] == w[i])` for each i, with `Σ y[i] == t`, is a subset
//! sum. The solver searches its disjunctions; when the answer is that there is no point, or one
//! point at an end, the search costs O(k²) or more in its k disjunctions, while two sums over the
//! atoms' values settle it:
//! - every value of an atom differs from its least value `r` by a multiple of the gcd of the
//!   offsets of its values from `r` (of 1, when it has a range of more than one value). So every
//!   value of the row lies in `R + g·Z`, `R` the row at the least values and `g` the gcd of the
//!   offsets times their coefficients; a `g` that does not divide `R` leaves no point;
//! - the row's least value over the atoms' values is a sum of one end per term. When it is
//!   above zero, or the greatest below zero, there is no point. When the least is zero, every
//!   atom that moves from the end that gives it makes the row positive, so the one point is
//!   that corner; the same for the greatest. Each end is a value of its atom, so the corner is a
//!   point;
//! - anything else is left to the solver, with its answer and its cost.
//!
//! Every answer here is exact for the whole formula: no point, or one point.
//!
//! The formula is recognized as: one equation of two or more atoms; and, for each of exactly
//! its atoms, one conjunct that is a disjunction of arms, each a conjunction of bounds on that
//! atom with both ends finite (or one such arm alone). Any other conjunct, or a second
//! constraint on one atom, leaves the formula to the solver.

use std::collections::{BTreeMap, HashMap};

use zedc_int::int::Int;

use super::formula::{Atom, Con, Conjuncts, Formula, Id, Model, Rel, one_bound};

/// What the residue or the ends of the row settle.
pub(super) enum Settled {
    Empty,
    Point(Model),
}

/// The ends of a range of one atom.
type Range = (Int, Int);

/// The answer of a formula, given as its top-level conjuncts (`Formula::conjunct_list`), when it is
/// one equation over atoms confined to finite ranges and its residue or its ends settle it;
/// `None` otherwise.
// Complexity tradeoff: the solver's search over the k disjunctions of such a formula asks O(k)
// questions of the whole row and more when no point is found, O(k²) or worse (subset sum with
// odd target and even weights: k^2.7 in instructions). Here each conjunct is read once into an
// ordered map, O(n log n) in the size n of the formula; a shared arm is read once by its id,
// so a formula that reuses one arm in many places is not read once per use, which would cost
// O(n²) in the size of its shared form. Test:
// `l01_38_presburger::one_row::residue_and_ends_of_a_row_scale`. COMPLEXITY.md row
// PRES-disj-cost.
pub(super) fn settle(conjuncts: &Conjuncts) -> Option<Settled> {
    // The shape is first checked by counting, with no conjunct read past its top: one
    // equation of two or more atoms, and one other conjunct for each of its atoms. Most
    // formulas the callers ask (two equations, a bound beside a disjunction) fail here, in
    // O(c) for c conjuncts, before any arm is read into a map. The read below also answers
    // `Settled::Empty` early for a conjunct that is `false` or that confines its atom to no
    // value; where the counts do not match, such a formula is now left to the callers' other
    // methods (the forced propagator where it has a first step, else the solver), which give
    // the same answer at their own cost.
    let mut rows = conjuncts.iter().filter_map(|g| match g {
        Formula::Con(c) if c.rel == Rel::Eq && c.lin.terms.len() > 1 => Some(c),
        _ => None,
    });
    match (rows.next(), rows.next()) {
        (Some(c), None) if c.lin.terms.len() + 1 == conjuncts.len() => {}
        _ => return None,
    }
    let mut domains: BTreeMap<Atom, Vec<Range>> = BTreeMap::new();
    let mut row: Option<&Con> = None;
    let mut arms_read: HashMap<Id, (Atom, Int, Int)> = HashMap::new();
    for g in conjuncts.iter() {
        if let Formula::Con(c) = g
            && c.rel == Rel::Eq
            && c.lin.terms.len() > 1
        {
            if row.is_some() {
                return None;
            }
            row = Some(c);
            continue;
        }
        let arms: Vec<&Formula> = match g {
            Formula::Or(ds) => ds.iter().collect(),
            _ => vec![g],
        };
        if arms.is_empty() {
            // `false`.
            return Some(Settled::Empty);
        }
        let mut atom: Option<Atom> = None;
        let mut ranges = Vec::new();
        for arm in arms {
            let key = matches!(arm, Formula::And(_)).then(|| Id::any(arm));
            let (a, l, h) = match key.and_then(|key| arms_read.get(&key).cloned()) {
                Some(read) => read,
                None => {
                    let read = range(arm)?;
                    if let Some(key) = key {
                        arms_read.insert(key, read.clone());
                    }
                    read
                }
            };
            if atom.as_ref().is_some_and(|b| *b != a) {
                return None;
            }
            atom = Some(a);
            if l <= h {
                ranges.push((l, h));
            }
        }
        let a = atom?;
        if domains.contains_key(&a) {
            return None;
        }
        if ranges.is_empty() {
            return Some(Settled::Empty);
        }
        domains.insert(a, ranges);
    }
    let row = row?;
    if row.lin.terms.len() != domains.len() {
        return None;
    }
    // `residue`: the row at each atom's least value; `step`: the gcd of the moves from it.
    let k = &row.lin.constant;
    let (mut least, mut most, mut residue, mut step) = (k.clone(), k.clone(), k.clone(), Int::ZERO);
    let (mut at_least, mut at_most) = (Model::new(), Model::new());
    for (a, c) in &row.lin.terms {
        let ranges = domains.get(a)?;
        let l = ranges.iter().map(|(l, _)| l).min()?.clone();
        let h = ranges.iter().map(|(_, h)| h).max()?.clone();
        residue = &residue + &(c * &l);
        for (rl, rh) in ranges {
            step = step.gcd(&(c * &(rl - &l)));
            if rl != rh {
                step = step.gcd(c);
            }
        }
        let (vl, vh) = if c.is_positive() { (l, h) } else { (h, l) };
        least = &least + &(c * &vl);
        most = &most + &(c * &vh);
        at_least.insert(a.clone(), vl);
        at_most.insert(a.clone(), vh);
    }
    let off_lattice = if step.is_zero() {
        !residue.is_zero()
    } else {
        !residue.mod_floor(&step).is_zero()
    };
    if off_lattice || least.is_positive() || most.is_negative() {
        return Some(Settled::Empty);
    }
    if least.is_zero() {
        return Some(Settled::Point(at_least));
    }
    if most.is_zero() {
        return Some(Settled::Point(at_most));
    }
    None
}

/// The atom of `arm`, a constraint or a conjunction of constraints on one atom other than a
/// product, with its least and greatest value; `None` for any other arm, or one with an end
/// unbounded.
pub(super) fn range(arm: &Formula) -> Option<(Atom, Int, Int)> {
    let parts: &[Formula] = match arm {
        Formula::Con(_) => std::slice::from_ref(arm),
        Formula::And(gs) => gs,
        Formula::Or(_) | Formula::Not(_) => return None,
    };
    let (mut lo, mut hi): (Option<Int>, Option<Int>) = (None, None);
    let mut atom: Option<&Atom> = None;
    for part in parts {
        let Formula::Con(c) = part else {
            return None;
        };
        let (a, l, h) = one_bound(c)?;
        if matches!(a, Atom::Product(..)) || atom.is_some_and(|b| b != a) {
            return None;
        }
        atom = Some(a);
        if let Some(l) = l
            && lo.as_ref().is_none_or(|v| l > *v)
        {
            lo = Some(l);
        }
        if let Some(h) = h
            && hi.as_ref().is_none_or(|v| h < *v)
        {
            hi = Some(h);
        }
    }
    Some((atom?.clone(), lo?, hi?))
}
