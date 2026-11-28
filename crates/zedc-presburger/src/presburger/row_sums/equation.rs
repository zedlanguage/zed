//! A formula of the class of `row_sums` whose one row is an equation over two atoms, answered
//! before the join as ranges met with a class (row PERF-cover-union-of-classes-listed, row_sums
//! part): the general solution of a linear Diophantine equation in two unknowns, by the extended
//! Euclidean algorithm (`zed_numtheory::bezout_i128`). Pugh 1991 (the crate's `lib.rs`,
//! "References") gives the gcd test of an equality in sec. 2.1 and eliminates equalities of more
//! unknowns in sec. 2.2; with two unknowns the solution below is direct, and is proved here.
//!
//! Proof. Write the row `a·u + b·v + k == 0`, `a` and `b` not 0, and `g = gcd(a, b)`. Where `g`
//! does not divide `k` there is no integer point, since `g` divides `a·u + b·v`. Otherwise, with
//! `s·a + t·b = g` (Bezout) and `q = −k / g`, the point `(u0, v0) = (s·q, t·q)` meets the row,
//! and the integer points of the row are exactly `(u0 + B·m, v0 − A·m)` for integers `m`, with
//! `A = a / g` and `B = b / g`: each such point meets it, as `a·B·m − b·A·m = 0`; and for any point
//! `(u, v)` of the row, `a·(u − u0) = −b·(v − v0)`, so `A·(u − u0) = −B·(v − v0)` with `A` and `B`
//! coprime, so `B` divides `u − u0`, and `m = (u − u0) / B` gives `v = v0 − A·m`. The map from
//! `m` to the point is one to one. So the points of the formula are those `m` whose `u` lies in
//! the ranges of `u` and whose `v` lies in the ranges of `v`, the other atoms taking any value of
//! their ranges, which are not empty (`Rows::of` marks the formula empty otherwise). For one
//! range `[lo, hi]` and `x = x0 + d·m`, `d > 0`, the `m` are `ceil((lo − x0) / d) ..=
//! floor((hi − x0) / d)`; for `d < 0` the same with `(−x0, −d)` and the range `[−hi, −lo]`. The
//! set of `m` is the meet of the two atoms' sets of `m`, and `u`'s answer is its image under
//! `m ↦ u0 + B·m`: each run `[m1, m2]` of it gives the values from `u0 + B·m1` to `u0 + B·m2`
//! modulo `|B|`, all in the class `u0 mod |B|`; likewise `v`. Each other atom's answer is its
//! ranges, or nothing where the set of `m` is empty.
//
// Complexity tradeoff: naive version, the join (`Plan::project`), which lists every interval of
// `u`'s and `v`'s sets of values, one per value for `|B| > 1` (`Plan::by_intervals`): O(w) for a
// range of width w, which stopped at `JOIN_LIMIT` on `three_cases_at` at r = 10^6 (3,000,001
// intervals listed in 64 ms, then the solver's 1 ms; 24,000,001 in 507 ms at 8·10^6, then 22.6
// ms), so the cost grew with the widths. Used: one gcd, O(log max(|a|, |b|)), and one step per
// range of each atom: O(p log p) for p ranges in all (the sort for `d < 0` and `Classed::new`),
// whatever the widths. Given up: nothing; a number past `i128` gives `None`, and the caller takes
// the join as before. Trigger: one row, an equation, of two terms. Test:
// `l01_38_omega_test::disj_groups::row_sums::one_equation_over_two_atoms_is_answered_exactly`;
// benchmark `l01_39_scope_relations::lazy::bench::three_cases_of_two_classes_scale`.

use zed_numtheory::bezout_i128;
use zedc_lattice::classed::Classed;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::Congruence;

use super::Rows;
use super::classes::domain;

/// Each atom's exact set where the rows are one equation over two atoms, as the module note
/// proves; `None` where they are not, or a number passes `i128`.
pub(super) fn answer(rows: &Rows) -> Option<Vec<Classed>> {
    let [row] = &rows.rows[..] else {
        return None;
    };
    let &[(i, a), (j, b)] = &row.terms[..] else {
        return None;
    };
    if !row.eq || i == j || a == 0 || b == 0 {
        return None;
    }
    let none = || vec![Classed::plain(IntervalSet::empty()); rows.atoms.len()];
    let (g, s, t) = bezout_i128(a, b)?;
    if row.k % g != 0 {
        return Some(none());
    }
    let q = (row.k / g).checked_neg()?;
    let (u0, v0) = (s.checked_mul(q)?, t.checked_mul(q)?);
    let (du, dv) = (b / g, (a / g).checked_neg()?);
    let m = meet(
        &steps(&rows.domains[i], u0, du)?,
        &steps(&rows.domains[j], v0, dv)?,
    );
    if m.is_empty() {
        return Some(none());
    }
    let image = |x0: i128, d: i128| -> Option<Classed> {
        let mut pieces = Vec::with_capacity(m.len());
        for &(m1, m2) in &m {
            let (x1, x2) = (
                x0.checked_add(d.checked_mul(m1)?)?,
                x0.checked_add(d.checked_mul(m2)?)?,
            );
            let fin = |x: i128| End::Fin(Num::from(x));
            pieces.push((fin(x1.min(x2)), fin(x1.max(x2))));
        }
        let class = Congruence::new(Num::from(d.checked_abs()?), Num::from(x0));
        Some(Classed::new(IntervalSet::from_pieces(pieces), class))
    };
    let mut sets: Vec<Classed> = (rows.domains.iter())
        .map(|d| Classed::plain(domain(d)))
        .collect();
    sets[i] = image(u0, du)?;
    sets[j] = image(v0, dv)?;
    Some(sets)
}

/// The integers `m` with `x0 + d·m` in `ranges` (sorted, disjoint), `d` not 0, as sorted runs,
/// disjoint and not adjacent; `None` where a number passes `i128`.
fn steps(ranges: &[(i128, i128)], x0: i128, d: i128) -> Option<Vec<(i128, i128)>> {
    let mut runs = Vec::with_capacity(ranges.len());
    for &(lo, hi) in ranges {
        // `lo <= x0 + d·m <= hi`, written with a positive step: for `d < 0`, `−hi <= −x0 + |d|·m
        // <= −lo`.
        let (lo, hi, x0, d) = if d > 0 {
            (lo, hi, x0, d)
        } else {
            (
                hi.checked_neg()?,
                lo.checked_neg()?,
                x0.checked_neg()?,
                d.checked_neg()?,
            )
        };
        let (l, h) = (lo.checked_sub(x0)?, hi.checked_sub(x0)?);
        // `ceil(l / d)` and `floor(h / d)`, `d > 0`.
        let m1 = l.div_euclid(d) + i128::from(l.rem_euclid(d) != 0);
        let m2 = h.div_euclid(d);
        if m1 <= m2 {
            runs.push((m1, m2));
        }
    }
    if d < 0 {
        runs.reverse();
    }
    // Runs from ranges that are not adjacent can be: `{0, 2}` with `d = 2` gives `m` in `{0}`
    // and `{1}`. Merged, so that two runs of the meet's image are more than one step apart.
    let mut merged: Vec<(i128, i128)> = Vec::with_capacity(runs.len());
    for (m1, m2) in runs {
        match merged.last_mut() {
            Some(last) if m1 <= last.1.saturating_add(1) => last.1 = last.1.max(m2),
            _ => merged.push((m1, m2)),
        }
    }
    Some(merged)
}

/// The meet of two sets of sorted runs, disjoint and not adjacent: the same form, as two
/// adjacent integers of the meet lie in one run of each set.
fn meet(x: &[(i128, i128)], y: &[(i128, i128)]) -> Vec<(i128, i128)> {
    let (mut p, mut q, mut out) = (0, 0, Vec::new());
    while p < x.len() && q < y.len() {
        let (lo, hi) = (x[p].0.max(y[q].0), x[p].1.min(y[q].1));
        if lo <= hi {
            out.push((lo, hi));
        }
        if x[p].1 < y[q].1 {
            p += 1;
        } else {
            q += 1;
        }
    }
    out
}
