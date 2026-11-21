//! Formulas of the class of `row_sums` that are answered exactly where the join does not
//! answer: past its work limit ([`super::JOIN_LIMIT`]) or with no plan (a key past
//! [`super::LIMIT`]). Row PRES-overlap-sums-exact-subclasses, author 2026-11-19: "find a fast
//! inexact solution that is exact in the largest possible subset of problem cases, and gives
//! refusals when it cannot be proved that the solution is exact".
//!
//! Two reductions, each proved below, run in `O(t log t)` for `t` terms; then, where they changed
//! the rows, the join once more on the reduced rows, with the same limit:
//! - forced atoms ([`force`]): in an equation, a term `c·y` whose `|c|` is greater than the
//!   width of the values the other terms can take is the same at every point, so `y` has one
//!   value or none. Each atom so fixed is put into its other rows, which may force more. Rows
//!   whose terms each outweigh all the lighter ones together (superincreasing, such as
//!   `y0 + 10m·y1 + 100m²·y2 == t` with ranges of width `m`) are solved down from the
//!   heaviest term, so the projection is one point or empty;
//! - scaled atoms ([`scaled`]): an atom whose values are single points `l, l + d·z1, ...` with
//!   `d` the gcd of their distances from the least is written `y = l + d·z`, and each row is
//!   divided by the gcd of its coefficients. An equation whose constant that gcd does not
//!   divide has no point. Keys past [`super::LIMIT`] (each value times `10^15`) fall below it.
//!
//! The answer, where given, is exact: no point, each atom's value where every row is met by
//! forced atoms (the atoms in no open row take every value of their ranges), or the join's
//! exact sets over the reduced rows, mapped back. Where none of these answers, the caller
//! takes the path it took before this module (the solver with the cover, or the refusal). The
//! answer's reason is left in [`REDUCED`].
//!
//! The classes the brief named, each scored (0, discard, to 10) and taken or not:
//!
//! | class | score | taken | why |
//! | --- | --- | --- | --- |
//! | forced atoms (superincreasing rows, one-term rows, and any term heavier than the rest of its row) | 9 | yes | `O(t log t)`, proved below; answers `sparse(k, m)` past the limit, where the join stops |
//! | scaled atoms (gcd of the values, gcd of a row's coefficients) | 7 | yes | `O(t log t)`; answers a family whose keys pass `2^62` (no plan) and shrinks the join's keys by the gcd |
//! | the join once more on the reduced rows | 7 | yes | exact by the join's own proof; at most a second limit of work, and only where a reduction changed the rows |
//! | disjoint components | 3 | no | the join's work is already the sum over components (bucket elimination, module note); only the residue after forcing is joined |
//! | totally unimodular rows (network flow) | 2 | no | an atom's union of ranges is a disjunction, which is not a linear system; ranges that touch are merged into one, which the join's intervals already answer in `O(1)` per operation |
//! | complete sequences (each weight at most 1 + the sum of the lighter ones: every sum in between is met) | 2 | no | the join's sets of intervals answer those sums in a few intervals per step, the same answer |
//! | strided sets of sums (intervals with a step) | 4 | no | a sum of strided sets is not strided in general, and the case that is (superincreasing) is the forced class |
//! | dense subset sum (Bringmann and Wellnitz, below) | 1 | no | its constants need thousands of atoms of one row before it applies, where the join's tables are a few intervals already |
//! | the structure of `overlap_rows(k)` | 0 | no | three groups in a chain, distinct weights in [1000, 1990] with gcd 1: neither forced, scaled nor dense; one row of it is subset sum, NP-complete, so no exact method is polynomial in the bits of the weights unless P = NP. The join answers it at every measured k (`overlap_rows` k = 1,024 in 3.4M units, a sixth of the limit); past the limit (set to 0) the solver with the cover refuses it whole at k = 8, 12, 16 and 24, with `Questions`, in 36 to 130 ms (2026-11-19, two runs at load 15 and 30) |
//!
//! Literature (allpapers, 2026-11-19, keyword and semantic searches on dense subset sum,
//! Frobenius numbers and long arithmetic progressions in subset sums, totally unimodular
//! systems, Presburger projection, and structure in subset sums). The one precise theorem
//! found for dense sums: K. Bringmann and P. Wellnitz, "On near-linear-time algorithms for
//! dense subset sum", SODA 2021 (arXiv 2010.09096), Theorem 4.2 (structural part, formal
//! version): "Let X be a multi-set and set C_δ := 1699200 · log(2n) log²(2μ(X)), C_α := 42480 ·
//! log(2μ(X)), C_λ := 169920 · log(2μ(X)). If X is C_δ-dense and has no C_α-almost divisor, then
//! for λ_X := C_λ · μ(X) mx(X) Σ(X) / |X|² we have [λ_X .. Σ(X) − λ_X] ⊆ S(X)", where C_δ-dense
//! means `|X|² ≥ C_δ · μ(X) · mx(X)`. For a set of n distinct weights (μ = 1) of at most w, it
//! needs n² ≥ 1699200 · log(2n) · w, about n ≥ 4,700 at w = 13 and more for larger w: a row
//! of thousands of atoms, which the join answers in `O(1)` operations per atom since its sums
//! are then a few intervals. Z. Galil and O. Margalit, "An almost linear-time algorithm for the
//! dense subset-sum problem", SIAM J. Comput. 20(6), 1991, pp. 1157-1189, doi:10.1137/0220072,
//! read 2026-11-21 in the publisher's PDF (Sci-Hub mirror; copy kept outside the repository):
//! its introduction states the conditions with `≪`, but its Theorem 5.1 has explicit
//! constants: for a set `A` of `m` distinct numbers in `(0, ℓ]` with `m > 100 ℓ^0.5 log₂ ℓ`,
//! every target in `(L, S_A − L)`, `L = S_A/6 + 2ℓ^1.5`, is solved after O(ℓ log ℓ + m log² ℓ)
//! preprocessing. Its sec. 3 says what the sums there are: with `d0` the least common multiple
//! of the small almost-divisors (Theorem 3.4), an interval where `d0 = 1`, else progressions of
//! step `d0`, one per residue in `A* mod d0`. For `overlap_rows`' weights, `ℓ = 1990`, the
//! condition needs `m > 48,900` atoms, far past the measured `k`, so neither theorem explains
//! the measured density there; it is measured, not proved. No result found answers subset sum
//! exactly in polynomial time
//! on a class wider than these.

use std::cell::Cell;

use zed_numtheory::gcd_u128 as gcd;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::rows::{Row, Rows};

/// Why a projection was answered here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReducedBy {
    /// No point: a forced atom has no value in its ranges, a row of forced atoms alone is not
    /// met, or the gcd of an equation's coefficients does not divide its constant.
    NoPoint,
    /// Every row is met by forced atoms: each forced atom has its one value, every other atom
    /// each value of its ranges.
    Forced,
    /// The join of the reduced rows answered, in these units.
    Joined(u64),
}

/// The reductions of the last projection answered here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reduced {
    /// Atoms forced to one value.
    pub forced: usize,
    /// Atoms written `l + d·z` with `d > 1`; 0 where the answer came before the scaling ended
    /// (forced, or no point).
    pub scaled: usize,
    /// What gave the answer.
    pub by: ReducedBy,
}

thread_local! {
    /// The reductions and the class of the last projection of `row_sums` answered here on
    /// this thread; `None` where the last one asked was not answered here.
    pub static REDUCED: Cell<Option<Reduced>> = const { Cell::new(None) };
}

/// Where the join did not answer: `at_limit`, it stopped at its limit; else it has no plan.
/// The join runs again only where a reduction can change its work: at the limit, where an atom
/// was forced or a row's coefficients gained a common factor (its keys shrink by it); with no
/// plan, where an atom was forced or scaled (its keys may fall below `LIMIT`).
// Complexity tradeoff: the reductions cost `O(t log t)` for `t` terms (a sort of each row's
// terms, a binary search over the ranges of each forced atom, a gcd per value of each atom),
// against the join's work up to its limit, which the caller has spent already; a second join,
// up to the same limit, runs only where the rows changed. Naive version: the solver after the
// join, up to `meter::EXACT_LIMIT`, or a refusal, on the families answered here. Given up: up
// to twice the join's limit before the solver on a formula that the reductions change and the
// second join still cannot answer. Test:
// `l01_38_omega_test::disj_groups::row_sums::classes`, benchmark
// `l01_38_omega_test::bench::disj_groups::classes`; COMPLEXITY.md row
// PRES-overlap-sums-exact-subclasses.
//
// `at_limit`: the join stopped at its limit (else it had no plan). `join`: the join of
// `row_sums` on the reduced rows, which puts them in its order first, with the units it spent,
// or `None` where it gives no answer; passed in so that this module names nothing of its
// parent's (no import cycle, `s_01f_import_graph`).
pub(super) fn project(
    rows: &Rows,
    want: &[bool],
    at_limit: bool,
    join: impl FnOnce(Rows) -> Option<(Vec<Option<IntervalSet>>, u64)>,
) -> Option<Vec<Option<IntervalSet>>> {
    REDUCED.with(|r| r.set(None));
    let wanted = |set: &dyn Fn(usize) -> IntervalSet| -> Vec<Option<IntervalSet>> {
        (0..rows.atoms.len())
            .map(|j| want[j].then(|| set(j)))
            .collect()
    };
    let answered = |forced, scaled, by| {
        REDUCED.with(|r| r.set(Some(Reduced { forced, scaled, by })));
    };
    let Some(forcing) = force(rows)? else {
        answered(0, 0, ReducedBy::NoPoint);
        return Some(wanted(&|_| IntervalSet::empty()));
    };
    let forced = forcing.fixed.iter().flatten().count();
    if forcing.open.iter().all(|&o| o == 0) {
        answered(forced, 0, ReducedBy::Forced);
        return Some(wanted(&|j| match forcing.fixed[j] {
            Some(v) => IntervalSet::point(Num::from(v)),
            None => domain(&rows.domains[j]),
        }));
    }
    let Some(reduced) = scaled(rows, &forcing)? else {
        answered(forced, 0, ReducedBy::NoPoint);
        return Some(wanted(&|_| IntervalSet::empty()));
    };
    let scaled_atoms = reduced.scale.iter().flatten().count();
    let worth = forced > 0
        || if at_limit {
            reduced.shrunk
        } else {
            scaled_atoms > 0
        };
    if !worth {
        return None;
    }
    let (mut sets, units) = join(reduced.rows)?;
    for (j, scale) in reduced.scale.iter().enumerate() {
        if let (Some((l, d)), Some(set)) = (scale, &sets[j]) {
            // The values `v = l + d·z` of the atom whose `z` the join keeps.
            let kept: Vec<(End, End)> = (rows.domains[j].iter())
                .filter(|&&(v, _)| set.contains_end(&End::Fin(Num::from((v - l) / d))))
                .map(|&(v, _)| (End::Fin(Num::from(v)), End::Fin(Num::from(v))))
                .collect();
            sets[j] = Some(IntervalSet::from_pieces(kept));
        }
    }
    answered(forced, scaled_atoms, ReducedBy::Joined(units));
    Some(sets)
}

/// The integers of `ranges`.
pub(super) fn domain(ranges: &[(i128, i128)]) -> IntervalSet {
    let fin = |v: i128| End::Fin(Num::from(v));
    IntervalSet::from_pieces(ranges.iter().map(|&(l, h)| (fin(l), fin(h))).collect())
}

/// The rows after [`force`]: each atom's forced value, each row's terms (merged by atom, none
/// 0), its constant with the forced atoms put in, and its count of terms not forced.
struct Forcing {
    fixed: Vec<Option<i128>>,
    terms: Vec<Vec<(usize, i128)>>,
    k: Vec<i128>,
    open: Vec<usize>,
}

/// The atoms each equation forces, and the atoms that forces in turn, to a fixed point:
/// `Some(None)` where they show there is no point, `None` where a number passes `i128`.
///
/// Proof. Write a row `Σ c_j·y_j + k == 0`, with each `y_j` in its ranges, whose hull is
/// `[lo_j, hi_j]`, and let `w_j = |c_j|·(hi_j − lo_j)`, the width of the values of `c_j·y_j`, and
/// `W = Σ w_j`. Take a term `i` with `|c_i| > W − w_i`. At every point, the other terms' sum `s`
/// lies in an interval `[a, a + W − w_i]` (each term between its least and greatest value on its
/// hull), so `c_i·y_i = −k − s` lies in an interval of width `W − w_i < |c_i|`, which holds at
/// most one multiple of `c_i`. So `y_i` takes one value `v` at every point; where no multiple
/// lies in that interval, or `v` is not in the ranges of `y_i`, there is no point. Putting
/// `y_i = v` into every row keeps the same points, so the step repeats on the rows so reduced,
/// and a row whose terms are all forced is met or not by those values alone. Only the term of
/// greatest `|c_i| + w_i` of a row need be tried: where any term meets the condition, it does.
/// A superincreasing row (each `|c|` greater than the sum of the widths of the lighter terms)
/// meets it at its heaviest term, and again on what remains, so it is solved to one point.
// Complexity tradeoff: each row's terms are sorted once by `|c| + w` (`O(t log t)`), and a
// pointer per row passes each term once, since a term forced or passed stays so: `W` only
// falls as atoms are forced, but the term at the pointer is the heaviest left, so a row is
// tried again only when an atom of it is forced, at `O(1)` plus the terms the pointer passes.
// Forcing an atom updates each of its rows in `O(1)` and searches its ranges in `O(log r)`.
// Naive version: each row tried again in full after every atom forced, `O(t²)` where atoms of
// one long row are forced one by one by other rows.
fn force(rows: &Rows) -> Option<Option<Forcing>> {
    let n = rows.atoms.len();
    let terms: Vec<Vec<(usize, i128)>> = rows.rows.iter().map(merged).collect::<Option<_>>()?;
    // A term's least value and its width over the hull of the atom's ranges.
    let reach = |j: usize, c: i128| -> Option<(i128, i128)> {
        let d = &rows.domains[j];
        let (a, b) = (c.checked_mul(d[0].0)?, c.checked_mul(d[d.len() - 1].1)?);
        Some((a.min(b), a.max(b).checked_sub(a.min(b))?))
    };
    let m = terms.len();
    let (mut least, mut width) = (vec![0i128; m], vec![0i128; m]);
    let mut by_weight: Vec<Vec<(i128, usize, i128)>> = Vec::with_capacity(m);
    let mut uses: Vec<Vec<(usize, i128)>> = vec![Vec::new(); n];
    for (r, ts) in terms.iter().enumerate() {
        let mut order = Vec::with_capacity(ts.len());
        for &(j, c) in ts {
            let (a, w) = reach(j, c)?;
            least[r] = least[r].checked_add(a)?;
            width[r] = width[r].checked_add(w)?;
            order.push((c.checked_abs()?.checked_add(w)?, j, c));
            uses[j].push((r, c));
        }
        order.sort_unstable_by_key(|t| std::cmp::Reverse(t.0));
        by_weight.push(order);
    }
    let mut k: Vec<i128> = rows.rows.iter().map(|r| r.k).collect();
    let mut open: Vec<usize> = terms.iter().map(Vec::len).collect();
    let met = |row: &Row, k: i128| if row.eq { k == 0 } else { k >= 0 };
    if (0..m).any(|r| open[r] == 0 && !met(&rows.rows[r], k[r])) {
        return Some(None);
    }
    let mut fixed: Vec<Option<i128>> = vec![None; n];
    let mut at = vec![0usize; m];
    let mut queue: Vec<usize> = (0..m).filter(|&r| rows.rows[r].eq).collect();
    let mut queued: Vec<bool> = rows.rows.iter().map(|r| r.eq).collect();
    while let Some(r) = queue.pop() {
        queued[r] = false;
        while let Some(&(weight, j, c)) = by_weight[r].get(at[r]) {
            if fixed[j].is_some() {
                at[r] += 1;
                continue;
            }
            if weight <= width[r] {
                break;
            }
            // The other terms' sum lies in `[low, low + width[r] − w]`, so `c·y` lies in
            // `[−k − high, −k − low]`.
            let (a, w) = reach(j, c)?;
            let low = least[r].checked_sub(a)?;
            let high = low.checked_add(width[r].checked_sub(w)?)?;
            let (from, to) = (
                k[r].checked_add(high)?.checked_neg()?,
                k[r].checked_add(low)?.checked_neg()?,
            );
            let Some(v) = multiple_in(c, from, to)? else {
                return Some(None);
            };
            if !in_ranges(&rows.domains[j], v) {
                return Some(None);
            }
            fixed[j] = Some(v);
            for &(r2, c2) in &uses[j] {
                let (a2, w2) = reach(j, c2)?;
                least[r2] = least[r2].checked_sub(a2)?;
                width[r2] = width[r2].checked_sub(w2)?;
                k[r2] = k[r2].checked_add(c2.checked_mul(v)?)?;
                open[r2] -= 1;
                if open[r2] == 0 {
                    if !met(&rows.rows[r2], k[r2]) {
                        return Some(None);
                    }
                } else if rows.rows[r2].eq && !queued[r2] && r2 != r {
                    queued[r2] = true;
                    queue.push(r2);
                }
            }
        }
    }
    Some(Some(Forcing {
        fixed,
        terms,
        k,
        open,
    }))
}

/// A row's terms with one term per atom, in the order of the atoms, and none with
/// coefficient 0; `None` where a sum passes `i128`.
fn merged(row: &Row) -> Option<Vec<(usize, i128)>> {
    let mut terms = row.terms.clone();
    terms.sort_unstable_by_key(|t| t.0);
    let mut out: Vec<(usize, i128)> = Vec::with_capacity(terms.len());
    for (j, c) in terms {
        match out.last_mut() {
            Some(last) if last.0 == j => last.1 = last.1.checked_add(c)?,
            _ => out.push((j, c)),
        }
    }
    out.retain(|t| t.1 != 0);
    Some(out)
}

/// The one `y` with `c·y` in `[from, to]`: `Some(None)` where there is none, `None` where there
/// are two or more (the caller's proof rules this out: the interval is narrower than `|c|`) or
/// a number passes `i128`. `c` is not 0.
fn multiple_in(c: i128, from: i128, to: i128) -> Option<Option<i128>> {
    let (c, from, to) = if c < 0 {
        (c.checked_neg()?, to.checked_neg()?, from.checked_neg()?)
    } else {
        (c, from, to)
    };
    // The least `y` with `c·y >= from` and the greatest with `c·y <= to`.
    let lo = from.checked_neg()?.div_euclid(c).checked_neg()?;
    let hi = to.div_euclid(c);
    match hi.checked_sub(lo)? {
        d if d < 0 => Some(None),
        0 => Some(Some(lo)),
        _ => None,
    }
}

/// Whether `v` lies in one of `ranges` (sorted and disjoint): `O(log r)`.
fn in_ranges(ranges: &[(i128, i128)], v: i128) -> bool {
    let i = ranges.partition_point(|&(_, h)| h < v);
    ranges.get(i).is_some_and(|&(l, _)| l <= v)
}

/// The rows left open by [`force`], with each atom of them whose ranges are single points
/// written `l + d·z` (`scale`, `(l, d)` where `d > 1`), and `shrunk` where a row's coefficients
/// so gained a common factor.
struct Scaled {
    rows: Rows,
    scale: Vec<Option<(i128, i128)>>,
    shrunk: bool,
}

/// The rows open after `forcing`, the forced atoms put in, each atom whose values are single
/// points `l < v1 < ...` written `y = l + d·z` with `d` the gcd of `v − l`, and each row divided
/// by the gcd `g` of its coefficients: `Some(None)` where an equation's constant is not a
/// multiple of `g`, `None` where a number passes `i128`.
///
/// Proof. The map `z ↦ l + d·z` takes the values `(v − l)/d`, integers since `d` divides each
/// `v − l`, one to one onto the atom's values, so the points of the new rows are those of the
/// old under it, and the join's set of `z` maps back to the atom's set. A row `Σ c·y + k`, with
/// `y = l + d·z`, is `Σ (c·d)·z + (k + Σ c·l)`. With `g` dividing each coefficient, the sum
/// `Σ c'·z` is a multiple of `g`: an equation `Σ c'·z + k' == 0` has a point only where `g`
/// divides `k'`, and is then `Σ (c'/g)·z + k'/g == 0`; an inequality `Σ c'·z >= −k'` holds
/// exactly where `Σ (c'/g)·z >= ⌈−k'/g⌉ = −⌊k'/g⌋`.
// Complexity tradeoff: a gcd over the values of each atom of an open row and over the
// coefficients of each row, `O(t + p)` gcds for `p` values, each `O(log V)`; the caller's
// `join` puts the rows in the join's order (`along_shared_atoms`, `O(t log t)`) once more,
// since forced atoms leave them.
fn scaled(rows: &Rows, forcing: &Forcing) -> Option<Option<Scaled>> {
    let n = rows.atoms.len();
    let mut in_open = vec![false; n];
    for (r, ts) in forcing.terms.iter().enumerate() {
        if forcing.open[r] > 0 {
            for &(j, _) in ts {
                in_open[j] |= forcing.fixed[j].is_none();
            }
        }
    }
    let mut scale: Vec<Option<(i128, i128)>> = vec![None; n];
    let mut domains = Vec::with_capacity(n);
    for j in 0..n {
        let ranges = &rows.domains[j];
        if let Some(v) = forcing.fixed[j] {
            domains.push(vec![(v, v)]);
            continue;
        }
        let l = ranges[0].0;
        let mut d = 0u128;
        if in_open[j] && ranges.iter().all(|&(a, b)| a == b) {
            for &(v, _) in ranges {
                d = gcd(d, v.checked_sub(l)?.unsigned_abs());
            }
        }
        if d > 1 {
            let d = i128::try_from(d).ok()?;
            scale[j] = Some((l, d));
            // Consecutive values of `z` join into one range.
            let mut zs: Vec<(i128, i128)> = Vec::with_capacity(ranges.len());
            for &(v, _) in ranges {
                let z = (v - l) / d;
                match zs.last_mut() {
                    Some(last) if last.1.checked_add(1)? == z => last.1 = z,
                    _ => zs.push((z, z)),
                }
            }
            domains.push(zs);
        } else {
            domains.push(ranges.clone());
        }
    }
    let mut out = Vec::new();
    let mut shrunk = false;
    for (r, ts) in forcing.terms.iter().enumerate() {
        if forcing.open[r] == 0 {
            continue;
        }
        let (mut k, mut g, mut g_before) = (forcing.k[r], 0u128, 0u128);
        let mut terms = Vec::with_capacity(forcing.open[r]);
        for &(j, c) in ts {
            if forcing.fixed[j].is_some() {
                continue;
            }
            g_before = gcd(g_before, c.unsigned_abs());
            let c = match scale[j] {
                Some((l, d)) => {
                    k = k.checked_add(c.checked_mul(l)?)?;
                    c.checked_mul(d)?
                }
                None => c,
            };
            g = gcd(g, c.unsigned_abs());
            terms.push((j, c));
        }
        let eq = rows.rows[r].eq;
        if g > 1 {
            let g = i128::try_from(g).ok()?;
            if eq && k % g != 0 {
                return Some(None);
            }
            k = k.div_euclid(g);
            for t in &mut terms {
                t.1 /= g;
            }
        }
        shrunk |= g > g_before;
        out.push(Row { terms, k, eq });
    }
    let rows = Rows {
        atoms: rows.atoms.clone(),
        domains,
        rows: out,
        empty: false,
    };
    Some(Some(Scaled {
        rows,
        scale,
        shrunk,
    }))
}
