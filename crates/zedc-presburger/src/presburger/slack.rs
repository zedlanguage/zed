//! Exact wide-row slack summaries, laminar subset-equation reduction, and persistent-tree
//! jumping-knapsack witness search for coupled unary disjunctions (PRES-disj-cost-xr).
//!
//! Three operations in [`super`] were quadratic or worse on `k` unary disjunctions coupled by
//! one or more wide unit-coefficient equations (or nested prefix equations as in `two_rows`):
//! - [`super::by_halves`], [`super::settle_as_sets`], [`super::project_parts`], and
//!   [`super::point_of`] eliminated variables one at a time through `shadow` or solved the full
//!   `k`-variable component for each of `2k` disjuncts, costing `O(k^2)` term copies;
//! - [`super::probe_kept`] ran a full `settle` and `point_with` (`pick_by`) per unheld disjunct,
//!   costing `O(k^2 log k)` when row slack left every disjunct individually feasible;
//! - [`super::settle_tied`] refused satisfiable tied subset-sum instances (`sat_half` and
//!   `two_rows` at `k = 512`) even when canonical color-grouped subset sums hit the target.
//!
//! Here laminar unit-coefficient equations are first reduced to pairwise atom-disjoint rows by
//! exact integer row subtraction ([`reduce_subset_wide_eqs`]); [`DisjointWide`] generalizes
//! [`super::one_row::OneRow`] to any number of pairwise atom-disjoint rows (unit-coefficient
//! equations and arbitrary-coefficient inequalities) with unary bounds, giving `O(1)` per-atom
//! projections and `O(|K| log k)` multi-atom projections; [`super::SlackIndex`] certifies in `O(1)` per
//! disjunct when fixing a disjunct either refutes its row or leaves every other variable's
//! projected interval unchanged (`SlackStatus::Immune`); and [`FastGreedy`] uses a weight-sorted
//! persistent segment tree so every greedy walk over `k` arbitrary weights runs in strict
//! worst-case `O(log W log k)` time (`O(k log k log W)` across all `2k` probes, both untied and
//! canonical-color-grouped). Every step is exact, deterministic, invariant under atom renaming,
//! and free of size switches, step caps, or thresholds.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::BuildHasherDefault;

use rustc_hash::FxHasher;

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::formula::{Atom, Con, Lin, Model, Rel};

thread_local! {
    /// Test control: retain full global-order scans in the two I23 row paths.
    pub static ROW_ORDER_SCAN: Cell<bool> = const { Cell::new(false) };
}

pub(super) fn has_product_con(c: &Con) -> bool {
    c.lin.terms.keys().any(|a| matches!(a, Atom::Product(..)))
}

/// Exact integer equivalence-preserving laminar subset elimination on unit-coefficient equations.
///
/// Whenever `E_1 : sum_{a in S_1} c_a a + k_1 == 0` (`c_a in {-1, +1}`, `|S_1| >= 2`) has its
/// support `S_1` contained in a strictly wider unit-coefficient equation `E_2` with uniform ratio
/// `s in {-1, +1}` (`coef_2(a) == s * coef_1(a)` for all `a in S_1`), replacing `E_2` by
/// `E_2 - s * E_1` preserves the exact set of integer solutions (`E_1 && E_2 <=> E_1 && (E_2 - s E_1)`).
///
/// Complexity tradeoff: naive pairwise elimination checks all `O(m^2)` pairs of equations. Here
/// equations are processed in non-decreasing support size and an `owner` map points each atom to
/// the reduced equation currently holding it; each successful subtraction removes `|S_1|` terms
/// from `E_2` and updates `owner` only on the residual disjoint atoms, running in `O(T log T)`
/// time for total input terms `T` on laminar hierarchies (`two_rows`), and leaving non-laminar
/// overlapping equations equivalent and intact. Test:
/// `l01_38_presburger::slack_scale::two_rows_scales`.
pub(super) fn try_reduce_subset_wide_eqs_refs(cons: &[&Con]) -> Option<Vec<Con>> {
    // The equations of two or more terms, by their lengths alone, with no term read: the
    // equations of unit coefficients and no product are among them, so fewer than two, or all
    // of one length, leave nothing to reduce. O(c) for c constraints, where the test below
    // walks every term of each such equation twice.
    let (mut eqs, mut shortest, mut longest) = (0usize, usize::MAX, 0usize);
    for c in cons {
        let len = c.lin.terms.len();
        if c.rel == Rel::Eq && len >= 2 {
            eqs += 1;
            shortest = shortest.min(len);
            longest = longest.max(len);
        }
    }
    if eqs < 2 || shortest == longest {
        return None;
    }
    let mut total_wide = 0usize;
    let mut min_len = usize::MAX;
    let mut max_len = 0usize;
    for &c in cons {
        let len = c.lin.terms.len();
        if c.rel == Rel::Eq
            && len >= 2
            && !has_product_con(c)
            && c.lin.terms.values().all(Int::is_unit)
        {
            total_wide += 1;
            min_len = min_len.min(len);
            max_len = max_len.max(len);
        }
    }
    if total_wide < 2 || min_len == max_len {
        return None;
    }
    let mut buckets: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut out: Vec<Con> = Vec::with_capacity(cons.len());
    for &c in cons {
        if c.rel == Rel::Eq
            && c.lin.terms.len() >= 2
            && !has_product_con(c)
            && c.lin.terms.values().all(Int::is_unit)
        {
            buckets
                .entry(c.lin.terms.len())
                .or_default()
                .push(out.len());
        }
        out.push(c.clone());
    }

    let mut any_reduced = false;
    let mut owner: HashMap<Atom, usize> = HashMap::new();
    while let Some((len, idxs)) = buckets.pop_first() {
        let mut stayed: Vec<usize> = Vec::new();
        for orig_i in idxs {
            let mut cur = out[orig_i].clone();
            let mut cands: Vec<usize> = cur
                .lin
                .terms
                .keys()
                .filter_map(|a| owner.get(a).copied())
                .collect();
            cands.sort_unstable();
            cands.dedup();
            for p in cands {
                let sub = &out[p];
                if sub.lin.terms.is_empty() || sub.lin.terms.len() >= cur.lin.terms.len() {
                    continue;
                }
                let mut scale: Option<Int> = None;
                let mut ok = true;
                for (a, sc) in &sub.lin.terms {
                    let Some(cc) = cur.lin.terms.get(a) else {
                        ok = false;
                        break;
                    };
                    let ratio = if cc == sc {
                        Int::ONE
                    } else if *cc == -sc {
                        -&Int::ONE
                    } else {
                        ok = false;
                        break;
                    };
                    match &scale {
                        None => scale = Some(ratio),
                        Some(prev) if *prev == ratio => {}
                        Some(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                let s = scale.expect("non-empty sub");
                for a in sub.lin.terms.keys() {
                    cur.lin.terms.remove(a);
                }
                cur.lin.constant = &cur.lin.constant - &(&s * &sub.lin.constant);
            }
            let new_len = cur.lin.terms.len();
            out[orig_i] = cur;
            if new_len < len {
                any_reduced = true;
                if new_len >= 2 {
                    buckets.entry(new_len).or_default().push(orig_i);
                }
            } else {
                stayed.push(orig_i);
            }
        }
        if stayed.is_empty() {
            continue;
        }
        let mut freq: HashMap<&Atom, usize> = HashMap::new();
        for &i in &stayed {
            for a in out[i].lin.terms.keys() {
                *freq.entry(a).or_default() += 1;
            }
        }
        for i in stayed {
            if out[i]
                .lin
                .terms
                .keys()
                .all(|a| !owner.contains_key(a) && freq.get(a) == Some(&1))
            {
                let atoms: Vec<Atom> = out[i].lin.terms.keys().cloned().collect();
                for a in atoms {
                    owner.insert(a, i);
                }
            }
        }
    }
    any_reduced.then_some(out)
}

pub(super) fn try_reduce_subset_wide_eqs(cons: &[Con]) -> Option<Vec<Con>> {
    let mut total_wide = 0usize;
    let mut min_len = usize::MAX;
    let mut max_len = 0usize;
    for c in cons {
        let len = c.lin.terms.len();
        if c.rel == Rel::Eq
            && len >= 2
            && !has_product_con(c)
            && c.lin.terms.values().all(Int::is_unit)
        {
            total_wide += 1;
            min_len = min_len.min(len);
            max_len = max_len.max(len);
        }
    }
    if total_wide < 2 || min_len == max_len {
        return None;
    }
    let refs: Vec<&Con> = cons.iter().collect();
    try_reduce_subset_wide_eqs_refs(&refs)
}

pub(super) fn reduce_subset_wide_eqs(cons: &[Con]) -> Vec<Con> {
    try_reduce_subset_wide_eqs(cons).unwrap_or_else(|| cons.to_vec())
}

#[derive(Clone, Default)]
pub(super) struct Sum {
    pub(super) finite: Int,
    pub(super) open: usize,
}

impl Sum {
    pub(super) fn add(&mut self, v: Option<&Int>) {
        match v {
            Some(v) => self.finite = &self.finite + v,
            None => self.open += 1,
        }
    }

    pub(super) fn remove(&mut self, v: Option<&Int>) {
        match v {
            Some(v) => self.finite = &self.finite - v,
            None => self.open -= 1,
        }
    }

    fn value(&self) -> Option<Int> {
        (self.open == 0).then(|| self.finite.clone())
    }

    fn without(&self, v: Option<&Int>) -> Option<Int> {
        match v {
            Some(v) if self.open == 0 => Some(&self.finite - v),
            None if self.open == 1 => Some(self.finite.clone()),
            _ => None,
        }
    }
}

type Ends = (Option<Int>, Option<Int>);

pub(super) fn signed_ends(e: &Ends, coef: &Int) -> Ends {
    let mul = |x: &Option<Int>| x.as_ref().map(|v| coef * v);
    if coef.is_positive() {
        (mul(&e.0), mul(&e.1))
    } else {
        (mul(&e.1), mul(&e.0))
    }
}

pub(super) fn unary_bound(c: &Con) -> Option<(Option<Atom>, Ends, bool)> {
    let mut terms = c.lin.terms.iter();
    let k = &c.lin.constant;
    match (terms.next(), terms.next()) {
        (None, _) => {
            let bad = k.is_negative() || (c.rel == Rel::Eq && !k.is_zero());
            Some((None, (None, None), bad))
        }
        (Some((a, coef)), None) => {
            if matches!(a, Atom::Product(..)) {
                return None;
            }
            match c.rel {
                Rel::Eq => {
                    let bad = !k.mod_floor(coef).is_zero();
                    let v = -&k.div_floor(coef);
                    Some((Some(a.clone()), (Some(v.clone()), Some(v)), bad))
                }
                Rel::Ge if coef.is_positive() => {
                    Some((Some(a.clone()), (Some(-&k.div_floor(coef)), None), false))
                }
                Rel::Ge => Some((Some(a.clone()), (None, Some(k.div_floor(&-coef))), false)),
            }
        }
        _ => None,
    }
}

pub(super) fn meet_ends(cur: &mut Ends, add: Ends) -> bool {
    if let Some(lo) = add.0
        && cur.0.as_ref().is_none_or(|v| lo > *v)
    {
        cur.0 = Some(lo);
    }
    if let Some(hi) = add.1
        && cur.1.as_ref().is_none_or(|v| hi < *v)
    {
        cur.1 = Some(hi);
    }
    matches!((&cur.0, &cur.1), (Some(l), Some(h)) if l > h)
}

#[derive(Clone)]
pub(super) struct WideRow {
    pub(super) con: Con,
    pub(super) least: Sum,
    pub(super) most: Sum,
}

impl WideRow {
    fn is_empty(&self) -> bool {
        (self.most.open == 0 && self.most.finite.is_negative())
            || (self.con.rel == Rel::Eq && self.least.open == 0 && self.least.finite.is_positive())
    }
}

/// A conjunction of unary bounds and any number of pairwise atom-disjoint wide rows (where wide
/// equations have unit coefficients `+-1`), with no product atoms.
#[derive(Clone)]
pub(super) struct DisjointWide {
    pub(super) ends: BTreeMap<Atom, Ends>,
    pub(super) atom_row: HashMap<Atom, usize>,
    pub(super) rows: Vec<WideRow>,
    empty: bool,
}

impl DisjointWide {
    // Complexity tradeoff: naive projection and disjunct feasibility over `m` disjoint or laminar
    // wide unit-coefficient rows copies or eliminates `k` variables one by one (`O(k^2)`). Here
    // laminar equations are reduced once via `reduce_subset_wide_eqs` and each disjoint row keeps
    // its finite corner sums and open-side counts (`O(T log T)` build, `O(|K| log k)` per query);
    // systems with product atoms, non-unit wide equations, or overlapping wide rows return `None`
    // and use the general solver unchanged. Test:
    // `l01_38_presburger::slack_scale::two_rows_scales`.
    pub(super) fn of_cons(cons: &[Con]) -> Option<DisjointWide> {
        if cons.iter().any(has_product_con) {
            return None;
        }
        if let Some(reduced) = try_reduce_subset_wide_eqs(cons) {
            Self::of_reduced(&reduced)
        } else {
            Self::of_reduced(cons)
        }
    }

    pub(super) fn of_refs(cons: &[&Con]) -> Option<DisjointWide> {
        if let Some(reduced) = try_reduce_subset_wide_eqs_refs(cons) {
            Self::of_reduced(&reduced)
        } else {
            Self::of_reduced(cons)
        }
    }

    pub(super) fn of_reduced<C: std::borrow::Borrow<Con>>(cons: &[C]) -> Option<DisjointWide> {
        // Complexity tradeoff: the rows that make this `None` (a product, a wide equation with
        // a coefficient other than ±1, two wide rows sharing an atom) were found while the
        // bounds and the row of each atom were built, so a system refused here paid for maps
        // it then dropped. They are now found first, in one pass over the T terms that borrows
        // each atom into a set hashed by `FxHasher`, sized once (keys are atoms of one system,
        // which no one chooses to collide; nothing iterates the set): O(T), with no clone and
        // no ordered map. The build below runs only for a system it accepts.
        let wide_terms = (cons.iter().map(|c| c.borrow().lin.terms.len()))
            .filter(|n| *n > 1)
            .sum();
        let mut wide_atoms: HashSet<&Atom, BuildHasherDefault<FxHasher>> =
            HashSet::with_capacity_and_hasher(wide_terms, BuildHasherDefault::default());
        for c in cons {
            let c = c.borrow();
            if has_product_con(c) {
                return None;
            }
            if c.lin.terms.len() < 2 {
                continue;
            }
            if c.rel == Rel::Eq && !c.lin.terms.values().all(Int::is_unit) {
                return None;
            }
            if !c.lin.terms.keys().all(|a| wide_atoms.insert(a)) {
                return None;
            }
        }
        let mut ends: BTreeMap<Atom, Ends> = BTreeMap::new();
        let mut atom_row: HashMap<Atom, usize> = HashMap::new();
        let mut wide_cons: Vec<Con> = Vec::new();
        let mut empty = false;

        for c in cons {
            let c = c.borrow();
            if let Some((atom, b, bad)) = unary_bound(c) {
                empty |= bad;
                if let Some(a) = atom {
                    empty |= meet_ends(ends.entry(a).or_default(), b);
                }
                continue;
            }
            let r_idx = wide_cons.len();
            for a in c.lin.terms.keys() {
                atom_row.insert(a.clone(), r_idx);
            }
            wide_cons.push(c.clone());
        }

        let mut rows = Vec::with_capacity(wide_cons.len());
        for con in wide_cons {
            let mut least = Sum {
                finite: con.lin.constant.clone(),
                open: 0,
            };
            let mut most = Sum {
                finite: con.lin.constant.clone(),
                open: 0,
            };
            for (a, coef) in &con.lin.terms {
                let (l, h) = signed_ends(ends.entry(a.clone()).or_default(), coef);
                least.add(l.as_ref());
                most.add(h.as_ref());
            }
            let wr = WideRow { con, least, most };
            empty |= wr.is_empty();
            rows.push(wr);
        }

        Some(DisjointWide {
            ends,
            atom_row,
            rows,
            empty,
        })
    }

    pub(super) fn empty(&self) -> bool {
        self.empty
    }

    fn projected_ends(&self, a: &Atom) -> Option<Ends> {
        if self.empty {
            return None;
        }
        let Some(e) = self.ends.get(a) else {
            return Some((None, None));
        };
        let (mut lo, mut hi) = e.clone();
        if let Some(&r_idx) = self.atom_row.get(a) {
            let wr = &self.rows[r_idx];
            let coef = &wr.con.lin.terms[a];
            let (l, h) = signed_ends(e, coef);
            let below = wr.most.without(h.as_ref()).map(|v| -&v);
            let above = match wr.con.rel {
                Rel::Eq => wr.least.without(l.as_ref()).map(|v| -&v),
                Rel::Ge => None,
            };
            let up = |v: Int| -&(-&v).div_floor(coef);
            let down = |v: Int| v.div_floor(coef);
            let (nl, nh) = if coef.is_positive() {
                (below.map(up), above.map(down))
            } else {
                (above.map(up), below.map(down))
            };
            if meet_ends(&mut (lo.clone(), hi.clone()), (nl.clone(), nh.clone())) {
                return None;
            }
            if let Some(nl) = nl
                && lo.as_ref().is_none_or(|v| nl > *v)
            {
                lo = Some(nl);
            }
            if let Some(nh) = nh
                && hi.as_ref().is_none_or(|v| nh < *v)
            {
                hi = Some(nh);
            }
        }
        Some((lo, hi))
    }

    pub(super) fn project(&self, a: &Atom) -> IntervalSet {
        let Some((lo, hi)) = self.projected_ends(a) else {
            return IntervalSet::empty();
        };
        IntervalSet::range(
            lo.map_or(End::NegInf, |v| End::Fin(Num::from(&v))),
            hi.map_or(End::PosInf, |v| End::Fin(Num::from(&v))),
        )
    }

    pub(super) fn all_hulls(&self) -> HashMap<Atom, IntervalSet> {
        self.ends
            .keys()
            .map(|a| (a.clone(), self.project(a)))
            .collect()
    }

    /// Exact integer feasibility of `self && d_cons` when `d_cons` is a conjunction of 0-ary or
    /// unary constraints on at most one atom (no products). Returns `None` if `d_cons` is outside
    /// that fragment.
    pub(super) fn holds_unary(&self, d_cons: &[Con]) -> Option<bool> {
        if self.empty {
            return Some(false);
        }
        let mut target_atom: Option<Atom> = None;
        let mut add_ends: Ends = (None, None);
        for c in d_cons {
            let (atom, b, bad) = unary_bound(c)?;
            if bad {
                return Some(false);
            }
            if let Some(a) = atom {
                match &target_atom {
                    None => target_atom = Some(a),
                    Some(prev) if *prev == a => {}
                    Some(_) => return None,
                }
                if meet_ends(&mut add_ends, b) {
                    return Some(false);
                }
            }
        }
        let Some(a) = target_atom else {
            return Some(true);
        };
        let Some(mut base_e) = self.projected_ends(&a) else {
            return Some(false);
        };
        Some(!meet_ends(&mut base_e, add_ends))
    }

    /// Tightens `self` in place with unary constraints `added`. Returns `false` (leaving `self`
    /// untouched) if any constraint in `added` is multi-variable or contains a product atom.
    pub(super) fn tighten_unary(&mut self, added: &[Con]) -> bool {
        let mut parsed = Vec::with_capacity(added.len());
        for c in added {
            let Some(u) = unary_bound(c) else {
                return false;
            };
            parsed.push(u);
        }
        for (atom, b, bad) in parsed {
            if bad {
                self.empty = true;
                return true;
            }
            let Some(a) = atom else {
                continue;
            };
            let old_e = self.ends.get(&a).cloned().unwrap_or((None, None));
            let mut new_e = old_e.clone();
            if meet_ends(&mut new_e, b) {
                self.ends.insert(a, new_e);
                self.empty = true;
                return true;
            }
            if new_e == old_e {
                self.ends.entry(a).or_insert(new_e);
                continue;
            }
            if let Some(&r_idx) = self.atom_row.get(&a) {
                let wr = &mut self.rows[r_idx];
                let coef = &wr.con.lin.terms[&a];
                let (ol, oh) = signed_ends(&old_e, coef);
                let (nl, nh) = signed_ends(&new_e, coef);
                wr.least.remove(ol.as_ref());
                wr.most.remove(oh.as_ref());
                wr.least.add(nl.as_ref());
                wr.most.add(nh.as_ref());
                if wr.is_empty() {
                    self.empty = true;
                }
            }
            self.ends.insert(a, new_e);
        }
        true
    }

    /// Materializes `self` back into a flat `Vec<Con>` (for seamless fallback in `by_halves` if a
    /// leaf ever returns a multi-variable constraint).
    pub(super) fn to_cons(&self) -> Vec<Con> {
        if self.empty {
            return vec![Con::ge(&Lin::constant(-1), &Lin::constant(0))];
        }
        let mut out = Vec::new();
        for (a, (lo, hi)) in &self.ends {
            let x = Lin::atom(a.clone());
            match (lo, hi) {
                (Some(l), Some(h)) if l == h => {
                    out.push(Con::eq(&x, &Lin::constant(l.clone())));
                }
                _ => {
                    if let Some(l) = lo {
                        out.push(Con::ge(&x, &Lin::constant(l.clone())));
                    }
                    if let Some(h) = hi {
                        out.push(Con::ge(&Lin::constant(h.clone()), &x));
                    }
                }
            }
        }
        for wr in &self.rows {
            out.push(wr.con.clone());
        }
        out
    }

    /// Exact integer projection of `self` onto `keep_atoms`, matching `shadow` + `linked_to` in
    /// `O(|keep_atoms| log k)` time.
    pub(super) fn project_keep(&self, keep_atoms: &BTreeSet<Atom>) -> Option<Vec<Con>> {
        if self.empty {
            return None;
        }
        let mut by_row: BTreeMap<usize, Vec<&Atom>> = BTreeMap::new();
        let mut out: Vec<Con> = Vec::new();

        let push_bounds = |a: &Atom, (lo, hi): &Ends, out: &mut Vec<Con>| match (lo, hi) {
            (Some(l), Some(h)) if l == h => {
                out.push(Con::eq(&Lin::atom(a.clone()), &Lin::constant(l.clone())));
            }
            _ => {
                if let Some(l) = lo {
                    out.push(Con::ge(&Lin::atom(a.clone()), &Lin::constant(l.clone())));
                }
                if let Some(h) = hi {
                    out.push(Con::ge(&Lin::constant(h.clone()), &Lin::atom(a.clone())));
                }
            }
        };

        for a in keep_atoms {
            if let Some(&r_idx) = self.atom_row.get(a) {
                by_row.entry(r_idx).or_default().push(a);
            } else if let Some(e) = self.ends.get(a) {
                push_bounds(a, e, &mut out);
            }
        }

        for (r_idx, kept) in by_row {
            if kept.len() == 1 {
                let a = kept[0];
                let e = self.projected_ends(a)?;
                push_bounds(a, &e, &mut out);
                continue;
            }
            let wr = &self.rows[r_idx];
            let mut rem_least = wr.least.clone();
            let mut rem_most = wr.most.clone();
            let mut kept_terms: BTreeMap<Atom, Int> = BTreeMap::new();
            for &a in &kept {
                if let Some(e) = self.ends.get(a) {
                    push_bounds(a, e, &mut out);
                }
                let coef = &wr.con.lin.terms[a];
                let default_e = (None, None);
                let e = self.ends.get(a).unwrap_or(&default_e);
                let (l, h) = signed_ends(e, coef);
                rem_least.remove(l.as_ref());
                rem_most.remove(h.as_ref());
                kept_terms.insert(a.clone(), coef.clone());
            }
            let l_val = rem_least.value();
            let m_val = rem_most.value();
            match wr.con.rel {
                Rel::Ge => {
                    if let Some(m_e) = m_val {
                        out.push(Con {
                            lin: Lin {
                                terms: kept_terms,
                                constant: m_e,
                            },
                            rel: Rel::Ge,
                        });
                    }
                }
                Rel::Eq => {
                    if let (Some(l_e), Some(m_e)) = (&l_val, &m_val)
                        && l_e == m_e
                    {
                        out.push(Con {
                            lin: Lin {
                                terms: kept_terms,
                                constant: l_e.clone(),
                            },
                            rel: Rel::Eq,
                        });
                    } else {
                        if let Some(m_e) = m_val {
                            out.push(Con {
                                lin: Lin {
                                    terms: kept_terms.clone(),
                                    constant: m_e,
                                },
                                rel: Rel::Ge,
                            });
                        }
                        if let Some(l_e) = l_val {
                            let neg_terms = kept_terms.into_iter().map(|(a, c)| (a, -&c)).collect();
                            out.push(Con {
                                lin: Lin {
                                    terms: neg_terms,
                                    constant: -&l_e,
                                },
                                rel: Rel::Ge,
                            });
                        }
                    }
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        Some(out)
    }

    /// Lexicographically extreme integer point (`greatest` or least, matching `point_of`) in
    /// `O(T log k)` time.
    pub(super) fn point_of(&self, greatest: bool) -> Option<Model> {
        if self.empty {
            return None;
        }
        let mut model = Model::new();
        for (a, (lo, hi)) in &self.ends {
            if self.atom_row.contains_key(a) {
                continue;
            }
            let v = match (lo, hi) {
                (_, Some(h)) if greatest => h.clone(),
                (Some(l), _) => l.clone(),
                (None, Some(h)) => h.clone(),
                (None, None) => Int::ZERO,
            };
            model.insert(a.clone(), v);
        }

        for wr in &self.rows {
            let terms: Vec<(&Atom, &Int)> = wr.con.lin.terms.iter().collect();
            let m = terms.len();
            let mut pref_least: Vec<Sum> = Vec::with_capacity(m + 1);
            let mut pref_most: Vec<Sum> = Vec::with_capacity(m + 1);
            pref_least.push(Sum {
                finite: wr.con.lin.constant.clone(),
                open: 0,
            });
            pref_most.push(Sum {
                finite: wr.con.lin.constant.clone(),
                open: 0,
            });
            let default_e = (None, None);
            for &(a, coef) in &terms {
                let e = self.ends.get(a).unwrap_or(&default_e);
                let (l, h) = signed_ends(e, coef);
                let mut nl = pref_least.last().expect("non-empty").clone();
                let mut nm = pref_most.last().expect("non-empty").clone();
                nl.add(l.as_ref());
                nm.add(h.as_ref());
                pref_least.push(nl);
                pref_most.push(nm);
            }
            let mut suffix_sum = Int::ZERO;
            for idx in (0..m).rev() {
                let (a, coef) = terms[idx];
                let (mut lo, mut hi) = self.ends.get(a).cloned().unwrap_or((None, None));
                let below = pref_most[idx].value().map(|v| -&(&v + &suffix_sum));
                let above = match wr.con.rel {
                    Rel::Eq => pref_least[idx].value().map(|v| -&(&v + &suffix_sum)),
                    Rel::Ge => None,
                };
                let up = |v: Int| -&(-&v).div_floor(coef);
                let down = |v: Int| v.div_floor(coef);
                let (nl, nh) = if coef.is_positive() {
                    (below.map(up), above.map(down))
                } else {
                    (above.map(up), below.map(down))
                };
                if meet_ends(&mut (lo.clone(), hi.clone()), (nl.clone(), nh.clone())) {
                    return None;
                }
                if let Some(nl) = nl
                    && lo.as_ref().is_none_or(|v| nl > *v)
                {
                    lo = Some(nl);
                }
                if let Some(nh) = nh
                    && hi.as_ref().is_none_or(|v| nh < *v)
                {
                    hi = Some(nh);
                }
                let v = match (lo, hi) {
                    (_, Some(h)) if greatest => h,
                    (Some(l), _) => l,
                    (None, Some(h)) => h,
                    (None, None) => Int::ZERO,
                };
                suffix_sum = &suffix_sum + &(coef * &v);
                model.insert(a.clone(), v);
            }
        }
        Some(model)
    }
}
#[derive(Clone)]
struct SumNode {
    left: u32,
    right: u32,
    sum: Int,
}

#[derive(Clone)]
struct MinNode {
    left: u32,
    right: u32,
    add: Int,
    min_val: Option<Int>,
}

fn min_opt(a: &Option<Int>, b: &Option<Int>) -> Option<Int> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y).clone()),
        (Some(x), None) => Some(x.clone()),
        (None, Some(y)) => Some(y.clone()),
        (None, None) => None,
    }
}

/// Persistent weight-partitioned segment tree simulating an exact left-to-right greedy knapsack
/// pass `for j in l..r { if j != skip && w[j] <= cur { cur -= w[j]; } }` in strict worst-case
/// `O(log W log n)` time per query (`O(n log n)` build).
pub(super) struct FastGreedy {
    n: usize,
    sorted_w: Vec<Int>,
    sum_nodes: Vec<SumNode>,
    sum_roots: Vec<u32>,
    min_nodes: Vec<MinNode>,
    min_roots: Vec<u32>,
    w: Vec<Int>,
}

impl FastGreedy {
    // Complexity tradeoff: a plain `(min_w, sum_w)` segment tree visits `Theta(n)` nodes per
    // greedy walk on alternating `[1, n, 1, n, ...]` weights (`Theta(n^2)` across `2n` probes).
    // Here version `ver` (indexed by `H = floor(cur / 2)`) activates light weights `w_i <= H` in a
    // persistent `SumNode` tree and stores `P_light(j) + w_j` for heavy weights `w_j > H` in a
    // persistent range-add `MinNode` tree (`O(n log n)` build). Each iteration either finishes the
    // range or strictly halves `cur` (`< ceil(cur / 2)`), bounding every query to at most
    // `floor(log2 W) + 2` steps of `O(log n)` each: `O(log W log n)` worst-case, bit-for-bit
    // identical to the linear greedy loop. Test:
    // `l01_38_presburger::slack_scale::alternating_weights_greedy_scales`.
    pub(super) fn new(w: &[Int]) -> FastGreedy {
        let n = w.len();
        let mut sum_nodes = vec![SumNode {
            left: 0,
            right: 0,
            sum: Int::ZERO,
        }];
        let mut min_nodes = vec![MinNode {
            left: 0,
            right: 0,
            add: Int::ZERO,
            min_val: None,
        }];
        if n == 0 {
            return FastGreedy {
                n: 0,
                sorted_w: Vec::new(),
                sum_nodes,
                sum_roots: vec![0],
                min_nodes,
                min_roots: vec![0],
                w: Vec::new(),
            };
        }

        fn build_min(nodes: &mut Vec<MinNode>, w: &[Int], nl: usize, nr: usize) -> u32 {
            if nl == nr {
                let id = nodes.len() as u32;
                nodes.push(MinNode {
                    left: 0,
                    right: 0,
                    add: Int::ZERO,
                    min_val: Some(w[nl].clone()),
                });
                return id;
            }
            let mid = (nl + nr) / 2;
            let l = build_min(nodes, w, nl, mid);
            let r = build_min(nodes, w, mid + 1, nr);
            let mv = min_opt(&nodes[l as usize].min_val, &nodes[r as usize].min_val);
            let id = nodes.len() as u32;
            nodes.push(MinNode {
                left: l,
                right: r,
                add: Int::ZERO,
                min_val: mv,
            });
            id
        }

        fn sum_add(
            nodes: &mut Vec<SumNode>,
            root: u32,
            nl: usize,
            nr: usize,
            idx: usize,
            val: &Int,
        ) -> u32 {
            let cur = nodes[root as usize].clone();
            if nl == nr {
                let id = nodes.len() as u32;
                nodes.push(SumNode {
                    left: 0,
                    right: 0,
                    sum: &cur.sum + val,
                });
                return id;
            }
            let mid = (nl + nr) / 2;
            let (nl_id, nr_id) = if idx <= mid {
                (sum_add(nodes, cur.left, nl, mid, idx, val), cur.right)
            } else {
                (cur.left, sum_add(nodes, cur.right, mid + 1, nr, idx, val))
            };
            let id = nodes.len() as u32;
            nodes.push(SumNode {
                left: nl_id,
                right: nr_id,
                sum: &cur.sum + val,
            });
            id
        }

        fn min_set_none(
            nodes: &mut Vec<MinNode>,
            root: u32,
            nl: usize,
            nr: usize,
            idx: usize,
        ) -> u32 {
            let cur = nodes[root as usize].clone();
            if nl == nr {
                let id = nodes.len() as u32;
                nodes.push(MinNode {
                    left: 0,
                    right: 0,
                    add: Int::ZERO,
                    min_val: None,
                });
                return id;
            }
            let mid = (nl + nr) / 2;
            let (nl_id, nr_id) = if idx <= mid {
                (min_set_none(nodes, cur.left, nl, mid, idx), cur.right)
            } else {
                (cur.left, min_set_none(nodes, cur.right, mid + 1, nr, idx))
            };
            let mv = min_opt(
                &nodes[nl_id as usize].min_val,
                &nodes[nr_id as usize].min_val,
            )
            .map(|m| &m + &cur.add);
            let id = nodes.len() as u32;
            nodes.push(MinNode {
                left: nl_id,
                right: nr_id,
                add: cur.add,
                min_val: mv,
            });
            id
        }

        fn min_range_add(
            nodes: &mut Vec<MinNode>,
            root: u32,
            nl: usize,
            nr: usize,
            ql: usize,
            qr: usize,
            delta: &Int,
        ) -> u32 {
            if qr < nl || ql > nr || root == 0 {
                return root;
            }
            let mut cur = nodes[root as usize].clone();
            if ql <= nl && nr <= qr {
                cur.add = &cur.add + delta;
                cur.min_val = cur.min_val.map(|m| &m + delta);
                let id = nodes.len() as u32;
                nodes.push(cur);
                return id;
            }
            let mid = (nl + nr) / 2;
            let nl_id = min_range_add(nodes, cur.left, nl, mid, ql, qr, delta);
            let nr_id = min_range_add(nodes, cur.right, mid + 1, nr, ql, qr, delta);
            let mv = min_opt(
                &nodes[nl_id as usize].min_val,
                &nodes[nr_id as usize].min_val,
            )
            .map(|m| &m + &cur.add);
            let id = nodes.len() as u32;
            nodes.push(MinNode {
                left: nl_id,
                right: nr_id,
                add: cur.add,
                min_val: mv,
            });
            id
        }

        let mut ord: Vec<usize> = (0..n).collect();
        ord.sort_by(|&i, &j| w[i].cmp(&w[j]).then_with(|| i.cmp(&j)));
        let sorted_w: Vec<Int> = ord.iter().map(|&i| w[i].clone()).collect();

        let mut sum_roots = Vec::with_capacity(n + 1);
        let mut min_roots = Vec::with_capacity(n + 1);
        sum_roots.push(0);
        let m0 = build_min(&mut min_nodes, w, 0, n - 1);
        min_roots.push(m0);

        for &i in &ord {
            let wi = &w[i];
            let next_s = sum_add(&mut sum_nodes, *sum_roots.last().unwrap(), 0, n - 1, i, wi);
            sum_roots.push(next_s);

            let m_prev = *min_roots.last().unwrap();
            let m_deactivated = min_set_none(&mut min_nodes, m_prev, 0, n - 1, i);
            let next_m = if i + 1 < n {
                min_range_add(&mut min_nodes, m_deactivated, 0, n - 1, i + 1, n - 1, wi)
            } else {
                m_deactivated
            };
            min_roots.push(next_m);
        }

        FastGreedy {
            n,
            sorted_w,
            sum_nodes,
            sum_roots,
            min_nodes,
            min_roots,
            w: w.to_vec(),
        }
    }

    fn sum_query(&self, root: u32, nl: usize, nr: usize, ql: usize, qr: usize) -> Int {
        if root == 0 || ql > qr || qr < nl || ql > nr {
            return Int::ZERO;
        }
        if ql <= nl && nr <= qr {
            return self.sum_nodes[root as usize].sum.clone();
        }
        let mid = (nl + nr) / 2;
        let node = &self.sum_nodes[root as usize];
        let mut res = Int::ZERO;
        if ql <= mid {
            res = &res + &self.sum_query(node.left, nl, mid, ql, qr);
        }
        if qr > mid {
            res = &res + &self.sum_query(node.right, mid + 1, nr, ql, qr);
        }
        res
    }

    fn sum_prefix_fit(
        &self,
        root: u32,
        nl: usize,
        nr: usize,
        ql: usize,
        qr: usize,
        budget: &mut Int,
    ) -> Option<usize> {
        if root == 0 || ql > qr || qr < nl || ql > nr {
            return None;
        }
        let node = &self.sum_nodes[root as usize];
        if node.sum.is_zero() {
            return None;
        }
        if ql <= nl && nr <= qr {
            if node.sum <= *budget {
                *budget = &*budget - &node.sum;
                return None;
            }
            if nl == nr {
                return Some(nl);
            }
        }
        let mid = (nl + nr) / 2;
        if ql <= mid
            && let Some(hit) = self.sum_prefix_fit(node.left, nl, mid, ql, qr, budget)
        {
            return Some(hit);
        }
        if qr > mid {
            return self.sum_prefix_fit(node.right, mid + 1, nr, ql, qr, budget);
        }
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn min_first_le(
        &self,
        root: u32,
        nl: usize,
        nr: usize,
        ql: usize,
        qr: usize,
        acc_add: &Int,
        rhs: &Int,
    ) -> Option<usize> {
        if root == 0 || ql > qr || qr < nl || ql > nr {
            return None;
        }
        let node = &self.min_nodes[root as usize];
        let m = node.min_val.as_ref()?;
        if &(m + acc_add) > rhs {
            return None;
        }
        if nl == nr {
            return Some(nl);
        }
        let next_add = acc_add + &node.add;
        let mid = (nl + nr) / 2;
        if ql <= mid
            && let Some(hit) = self.min_first_le(node.left, nl, mid, ql, qr, &next_add, rhs)
        {
            return Some(hit);
        }
        if qr > mid {
            return self.min_first_le(node.right, mid + 1, nr, ql, qr, &next_add, rhs);
        }
        None
    }

    fn run_contig(&self, mut pos: usize, end: usize, mut cur: Int) -> Int {
        let two = Int::from(2);
        while pos < end && cur.is_positive() {
            let half = cur.div_floor(&two);
            let ver = self.sorted_w.partition_point(|u| *u <= half);
            let s_root = self.sum_roots[ver];
            let m_root = self.min_roots[ver];

            let p_pos = if pos > 0 {
                self.sum_query(s_root, 0, self.n - 1, 0, pos - 1)
            } else {
                Int::ZERO
            };
            let rhs = &cur + &p_pos;
            let j_heavy = self.min_first_le(m_root, 0, self.n - 1, pos, end - 1, &Int::ZERO, &rhs);
            let limit = j_heavy.unwrap_or(end);
            if pos < limit
                && let Some(j_fail) =
                    self.sum_prefix_fit(s_root, 0, self.n - 1, pos, limit - 1, &mut cur)
            {
                pos = j_fail + 1;
                continue;
            }
            match j_heavy {
                Some(jh) => {
                    cur = &cur - &self.w[jh];
                    pos = jh + 1;
                }
                None => break,
            }
        }
        cur
    }

    /// Exact residual after scanning `l..r` left-to-right (skipping `skip_i`).
    pub(super) fn rem_after(&self, l: usize, r: usize, mut cur: Int, skip_i: usize) -> Int {
        if self.n == 0 || l >= r || !cur.is_positive() {
            return cur;
        }
        let r = r.min(self.n);
        if l < skip_i && skip_i < r {
            cur = self.run_contig(l, skip_i, cur);
            self.run_contig(skip_i + 1, r, cur)
        } else if skip_i == l {
            self.run_contig(l + 1, r, cur)
        } else {
            self.run_contig(l, r, cur)
        }
    }
}

#[derive(Clone)]
pub(super) enum HitKind {
    None,
    Exact {
        split: usize,
    },
    FwdPick {
        split: usize,
        x_star: usize,
        b_rem: Int,
        loc: usize,
    },
    BwdPick {
        split: usize,
        x_star: usize,
        b_rem: Int,
        loc: usize,
    },
    UnboundedFast {
        gmax: usize,
        rem: Int,
        at_gmax: bool,
    },
    UnboundedSlow {
        rem: Int,
    },
}

pub(super) struct DisjInfo {
    pub(super) disj_idx: usize,
    pub(super) atom: Atom,
    pub(super) low_arm: usize,
    pub(super) high_arm: usize,
    pub(super) low_val: Int,
    pub(super) high_val: Int,
    pub(super) weight: Int,
}

// Complexity tradeoff: filtering all K globally ordered atoms separately for R rows costs
// O(R*K) lookups, even for R disjoint constant-width rows (I23). Index the global ranks
// once in O(K), then sort only each row's m disjunct indices, O(m log m). Total O(K+M log M)
// work and O(K+M) storage for M disjuncts; the exact ordered subsequence is unchanged.
pub(super) fn row_order(
    disjs: &[DisjInfo],
    ord_atoms: &[Atom],
    ranks: &HashMap<&Atom, usize>,
) -> Vec<usize> {
    if ROW_ORDER_SCAN.with(Cell::get) {
        let locs: HashMap<&Atom, usize> = disjs
            .iter()
            .enumerate()
            .map(|(i, d)| (&d.atom, i))
            .collect();
        return ord_atoms
            .iter()
            .filter_map(|a| locs.get(a).copied())
            .collect();
    }
    let mut out: Vec<usize> = (0..disjs.len())
        .filter(|&i| ranks.contains_key(&disjs[i].atom))
        .collect();
    out.sort_unstable_by_key(|&i| ranks[&disjs[i].atom]);
    out
}

pub(super) struct RowPlan {
    pub(super) disjs: Vec<DisjInfo>,
    solve_ord: Vec<usize>,
    pub(super) hit_table: Vec<[HitKind; 2]>,
    pub(super) any_hit: Option<(usize, usize)>,
}

// Complexity tradeoff: naive `probe_kept` runs a separate `point_with` (`pick_by(..., true)` and
// `pick_by(..., false)`) per unheld disjunct, costing `Theta(k_r^2 log k_r)` per bounded unit row.
// Here `sweep_row` exploits Hopcroft color-order invariance (`Rel::Ge < Rel::Eq` in `Linked::meet`
// keeps `-a_i + w_i >= 0` intact when `a_z == v_z` is added, so `solve_ord` is invariant across all
// `2 k_r` probes), simulating the initial LP split via a Fenwick tree and all greedy walks via
// `FastGreedy` in `O(k_r log k_r log W)` total time. What is given up: searches outside single-axis
// greedy walks (general subset sum, NP-complete). Test:
// `l01_38_presburger::slack_scale::sat_half_decide_scales`.
pub(super) fn sweep_row(
    disjs: Vec<DisjInfo>,
    solve_ord: Vec<usize>,
    target: Int,
) -> Option<RowPlan> {
    let k_r = disjs.len();
    if k_r < 2 || solve_ord.len() != k_r {
        return None;
    }
    let mut solve_pos = vec![0usize; k_r];
    for (pos, &loc) in solve_ord.iter().enumerate() {
        solve_pos[loc] = pos;
    }
    let w_of: Vec<Int> = disjs.iter().map(|d| d.weight.clone()).collect();
    let mut solve_psum: Vec<Int> = Vec::with_capacity(k_r + 1);
    solve_psum.push(Int::ZERO);
    for &loc in &solve_ord {
        let next = solve_psum.last().unwrap() + &w_of[loc];
        solve_psum.push(next);
    }
    let total_w = solve_psum[k_r].clone();
    if target.is_negative() || target > total_w {
        return None;
    }

    let w_rev: Vec<Int> = (0..k_r).map(|i| w_of[k_r - 1 - i].clone()).collect();
    let fg_fwd = FastGreedy::new(&w_of);
    let fg_bwd = FastGreedy::new(&w_rev);

    let mut hit_table: Vec<[HitKind; 2]> = vec![[HitKind::None, HitKind::None]; k_r];
    let mut probes: Vec<(usize, usize, usize, Int)> = Vec::with_capacity(2 * k_r);

    for loc in 0..k_r {
        for arm_role in 0..2 {
            // `arm_role == 0` -> `low_arm` (weight 0), `arm_role == 1` -> `high_arm` (weight w).
            let arm_idx = if arm_role == 0 {
                disjs[loc].low_arm
            } else {
                disjs[loc].high_arm
            };
            let val_i = if arm_role == 1 {
                &w_of[loc]
            } else {
                &Int::ZERO
            };
            let rem = &target - val_i;
            let max_rem = &total_w - &w_of[loc];
            if rem.is_negative() || rem > max_rem {
                continue;
            }
            if rem.is_zero() {
                hit_table[loc][arm_idx] = HitKind::Exact { split: 0 };
                continue;
            }
            if rem == max_rem {
                hit_table[loc][arm_idx] = HitKind::Exact { split: k_r };
                continue;
            }
            let mut lo = 0usize;
            let mut hi = k_r - 1;
            while lo < hi {
                let mid = (lo + hi) / 2;
                let s = if solve_pos[loc] <= mid {
                    &solve_psum[mid + 1] - &w_of[loc]
                } else {
                    solve_psum[mid + 1].clone()
                };
                if s <= rem {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }
            let mut split = lo;
            if solve_ord[split] == loc {
                split += 1;
            }
            let s_before = if solve_pos[loc] < split {
                &solve_psum[split] - &w_of[loc]
            } else {
                solve_psum[split].clone()
            };
            let val_star = &rem - &s_before;
            probes.push((split, loc, arm_idx, val_star));
        }
    }

    probes.sort_unstable_by_key(|&(split, loc, arm_idx, _)| (split, loc, arm_idx));

    let mut bit: Vec<Int> = vec![Int::ZERO; k_r + 1];
    let bit_add = |bit: &mut [Int], mut idx: usize, val: &Int| {
        idx += 1;
        while idx <= k_r {
            bit[idx] = &bit[idx] + val;
            idx += idx.isolate_lowest_one();
        }
    };
    let bit_sum = |bit: &[Int], mut idx: usize| -> Int {
        let mut s = Int::ZERO;
        while idx > 0 {
            s = &s + &bit[idx];
            idx -= idx.isolate_lowest_one();
        }
        s
    };

    let mut cur_split = 0usize;
    let mut full_sum = Int::ZERO;
    for (split, loc, arm_idx, val_star) in probes {
        while cur_split < split {
            let x = solve_ord[cur_split];
            bit_add(&mut bit, x, &w_of[x]);
            full_sum = &full_sum + &w_of[x];
            cur_split += 1;
        }
        if val_star.is_zero() {
            hit_table[loc][arm_idx] = HitKind::Exact { split };
            continue;
        }
        let x_star = solve_ord[split];
        if val_star == w_of[x_star] {
            hit_table[loc][arm_idx] = HitKind::Exact { split: split + 1 };
            continue;
        }

        // Forward `pick_by` walk (`x_star` down to `0`, which is `k_r - 1 - x_star .. k_r` on `w_rev`).
        let mut sum_below = bit_sum(&bit, x_star);
        if loc < x_star && solve_pos[loc] < split {
            sum_below = &sum_below - &w_of[loc];
        }
        let b_rem_fwd = &val_star + &sum_below;
        let rev_start = k_r - 1 - x_star;
        let rev_skip = k_r - 1 - loc;
        if fg_bwd
            .rem_after(rev_start, k_r, b_rem_fwd.clone(), rev_skip)
            .is_zero()
        {
            hit_table[loc][arm_idx] = HitKind::FwdPick {
                split,
                x_star,
                b_rem: b_rem_fwd,
                loc,
            };
            continue;
        }

        // Backward `pick_by` walk (`x_star .. k_r` on `w_of`).
        let sum_le = bit_sum(&bit, x_star + 1);
        let mut sum_above = &full_sum - &sum_le;
        if loc > x_star && solve_pos[loc] < split {
            sum_above = &sum_above - &w_of[loc];
        }
        let b_rem_bwd = &val_star + &sum_above;
        if fg_fwd
            .rem_after(x_star, k_r, b_rem_bwd.clone(), loc)
            .is_zero()
        {
            hit_table[loc][arm_idx] = HitKind::BwdPick {
                split,
                x_star,
                b_rem: b_rem_bwd,
                loc,
            };
        }
    }

    let mut any_hit = None;
    'find_any: for (loc, arms) in hit_table.iter().enumerate() {
        for (arm_idx, hk) in arms.iter().enumerate() {
            if !matches!(hk, HitKind::None) {
                any_hit = Some((loc, arm_idx));
                break 'find_any;
            }
        }
    }

    Some(RowPlan {
        disjs,
        solve_ord,
        hit_table,
        any_hit,
    })
}

// Complexity tradeoff: on an unbounded single-color unit equation (`decide_kept`'s second pass
// without `disjunction_hulls`), naive `point_with` runs `pick_by` `2 k_r` times, costing
// `Theta(k_r^2)`. Because `quotient` unpacks the residual sum onto the lexicographically greatest
// active `Atom`, partitioning `0..k_r` by the right-to-left suffix maxima `main_m` produces
// disjoint exposed sub-chains `exposed[q]` with `sum_q |exposed[q]| <= k_r`, simulating all `2 k_r`
// fast and slow probes exactly in `O(k_r log k_r)` time at every `k_r >= 2` with zero size switch.
// Test: `l01_38_presburger::slack_scale::sat_half_decide_scales`.
// `use_fast` is `!old_path()` of the parent module, which the caller reads.
pub(super) fn sweep_row_unbounded(disjs: Vec<DisjInfo>, target: Int, use_fast: bool) -> RowPlan {
    let k_r = disjs.len();
    let arm0_val: Vec<Int> = disjs
        .iter()
        .map(|d| {
            if d.high_arm == 0 {
                d.weight.clone()
            } else {
                Int::ZERO
            }
        })
        .collect();
    let mut arm0_psum: Vec<Int> = Vec::with_capacity(k_r + 1);
    arm0_psum.push(Int::ZERO);
    for v in &arm0_val {
        let next = arm0_psum.last().unwrap() + v;
        arm0_psum.push(next);
    }

    // Two greatest-`Atom` indices in `0..k_r` for `quotient` unpacking when `!old_path()` runs
    // `pick_by(..., fast = true)`.
    let mut ord_by_atom: Vec<usize> = (0..k_r).collect();
    ord_by_atom.sort_by(|&a, &b| disjs[b].atom.cmp(&disjs[a].atom));
    let gmax1 = ord_by_atom[0];
    let gmax2 = ord_by_atom[1];

    // Right-to-left suffix maxima `main_m[0] > main_m[1] > ... > main_m[r - 1] == 0` of
    // `disjs[u].atom` (the exact sequence of `quotient` unpack targets along `pick_by(..., false)`),
    // plus the disjoint exposed sub-chains `exposed[q]` inside `(main_m[q + 1], main_m[q])` when
    // `loc == main_m[q]` is removed (`sum_q |exposed[q]| <= k_r - r <= k_r`).
    let mut inc_m: Vec<usize> = Vec::new();
    for u in 0..k_r {
        if inc_m
            .last()
            .is_none_or(|&prev| disjs[u].atom > disjs[prev].atom)
        {
            inc_m.push(u);
        }
    }
    inc_m.reverse();
    let main_m = inc_m;
    let r = main_m.len();
    let mut pos_in_main: Vec<Option<usize>> = vec![None; k_r];
    for (q, &m_idx) in main_m.iter().enumerate() {
        pos_in_main[m_idx] = Some(q);
    }

    let mut main_pref: Vec<Int> = Vec::with_capacity(r + 1);
    main_pref.push(Int::ZERO);
    let mut hit_map: HashMap<Int, Vec<usize>> = HashMap::with_capacity(2 * r);
    for (q, &m_idx) in main_m.iter().enumerate() {
        let p0 = main_pref[q].clone();
        let p1 = &p0 + &disjs[m_idx].weight;
        hit_map.entry(p0.clone()).or_default().push(q);
        hit_map.entry(p1).or_default().push(q);
        let next = &p0 + &arm0_val[m_idx];
        main_pref.push(next);
    }

    let mut exposed: Vec<Vec<usize>> = Vec::with_capacity(r);
    for q in 0..r {
        let low_u = if q + 1 < r { main_m[q + 1] + 1 } else { 0 };
        let high_u = main_m[q];
        let mut sub_inc: Vec<usize> = Vec::new();
        let mut floor_atom: Option<&Atom> = if q + 1 < r {
            Some(&disjs[main_m[q + 1]].atom)
        } else {
            None
        };
        for (u, d) in disjs.iter().enumerate().take(high_u).skip(low_u) {
            if floor_atom.is_none_or(|fa| d.atom > *fa) {
                sub_inc.push(u);
                floor_atom = Some(&d.atom);
            }
        }
        sub_inc.reverse();
        exposed.push(sub_inc);
    }

    let mut hit_table = vec![[HitKind::None, HitKind::None]; k_r];
    let mut any_hit = None;

    for loc in 0..k_r {
        let gm = if loc == gmax1 { gmax2 } else { gmax1 };
        let xl = if loc == 0 { 1 } else { 0 };
        for (arm_idx, hit) in hit_table[loc].iter_mut().enumerate() {
            let v_loc = if arm_idx == disjs[loc].high_arm {
                &disjs[loc].weight
            } else {
                &Int::ZERO
            };
            let rem = &target - v_loc;
            if rem.is_negative() {
                continue;
            }
            if rem.is_zero() {
                *hit = HitKind::Exact { split: 0 };
                if any_hit.is_none() {
                    any_hit = Some((loc, arm_idx));
                }
                continue;
            }
            if use_fast {
                if rem == disjs[gm].weight {
                    *hit = HitKind::UnboundedFast {
                        gmax: gm,
                        rem: rem.clone(),
                        at_gmax: true,
                    };
                    if any_hit.is_none() {
                        any_hit = Some((loc, arm_idx));
                    }
                    continue;
                }
                if gm > xl {
                    let mut s = &arm0_psum[gm + 1] - &arm0_psum[xl + 1];
                    if xl < loc && loc <= gm {
                        s = &s - &arm0_val[loc];
                    }
                    let rem_xl = &rem - &s;
                    if rem_xl.is_zero() || rem_xl == disjs[xl].weight {
                        *hit = HitKind::UnboundedFast {
                            gmax: gm,
                            rem: rem.clone(),
                            at_gmax: false,
                        };
                        if any_hit.is_none() {
                            any_hit = Some((loc, arm_idx));
                        }
                        continue;
                    }
                }
            }

            let slow_hit = match pos_in_main[loc] {
                None => hit_map.contains_key(&rem),
                Some(q) => {
                    if hit_map
                        .get(&rem)
                        .and_then(|v| v.first())
                        .is_some_and(|&t| t < q)
                    {
                        true
                    } else {
                        let mut cur = &rem - &main_pref[q];
                        let mut sub_hit = false;
                        for &u in &exposed[q] {
                            if cur.is_zero() || cur == disjs[u].weight {
                                sub_hit = true;
                                break;
                            }
                            cur = &cur - &arm0_val[u];
                        }
                        if sub_hit {
                            true
                        } else if q + 1 < r && !cur.is_negative() {
                            let shifted = &cur + &main_pref[q + 1];
                            hit_map.get(&shifted).is_some_and(|v| {
                                let idx = v.partition_point(|&t| t < q + 1);
                                idx < v.len()
                            })
                        } else {
                            false
                        }
                    }
                }
            };
            if slow_hit {
                *hit = HitKind::UnboundedSlow { rem };
                if any_hit.is_none() {
                    any_hit = Some((loc, arm_idx));
                }
            }
        }
    }

    let solve_ord: Vec<usize> = (0..k_r).collect();
    RowPlan {
        disjs,
        solve_ord,
        hit_table,
        any_hit,
    }
}

pub(super) fn fill_row_model(plan: &RowPlan, loc: usize, arm_idx: usize, m: &mut Model) -> bool {
    let hk = &plan.hit_table[loc][arm_idx];
    if matches!(hk, HitKind::None) {
        return false;
    }
    let k_r = plan.disjs.len();
    let mut take_high = vec![false; k_r];
    match hk {
        HitKind::None => unreachable!(),
        HitKind::Exact { split } => {
            for &x in &plan.solve_ord[..*split] {
                if x != loc {
                    take_high[x] = true;
                }
            }
            take_high[loc] = arm_idx == plan.disjs[loc].high_arm;
        }
        HitKind::FwdPick {
            split,
            x_star,
            b_rem,
            loc: l,
        } => {
            for &x in &plan.solve_ord[..*split] {
                if x > *x_star && x != *l {
                    take_high[x] = true;
                }
            }
            take_high[*l] = arm_idx == plan.disjs[*l].high_arm;
            let mut cur = b_rem.clone();
            for x in (0..=*x_star).rev() {
                if x == *l {
                    continue;
                }
                let w = &plan.disjs[x].weight;
                if *w <= cur {
                    cur = &cur - w;
                    take_high[x] = true;
                }
            }
            if !cur.is_zero() {
                return false;
            }
        }
        HitKind::BwdPick {
            split,
            x_star,
            b_rem,
            loc: l,
        } => {
            for &x in &plan.solve_ord[..*split] {
                if x < *x_star && x != *l {
                    take_high[x] = true;
                }
            }
            take_high[*l] = arm_idx == plan.disjs[*l].high_arm;
            let mut cur = b_rem.clone();
            for (x, d) in plan.disjs.iter().enumerate().take(k_r).skip(*x_star) {
                if x == *l {
                    continue;
                }
                let w = &d.weight;
                if *w <= cur {
                    cur = &cur - w;
                    take_high[x] = true;
                }
            }
            if !cur.is_zero() {
                return false;
            }
        }
        HitKind::UnboundedFast { gmax, rem, at_gmax } => {
            take_high[loc] = arm_idx == plan.disjs[loc].high_arm;
            if *at_gmax {
                if *rem == plan.disjs[*gmax].weight {
                    take_high[*gmax] = true;
                } else if !rem.is_zero() {
                    return false;
                }
            } else {
                let xl = if loc == 0 { 1 } else { 0 };
                let mut cur = rem.clone();
                for (x, d) in plan.disjs.iter().enumerate().take(*gmax + 1).skip(xl + 1) {
                    if x == loc {
                        continue;
                    }
                    if d.high_arm == 0 {
                        take_high[x] = true;
                        cur = &cur - &d.weight;
                    }
                }
                if cur == plan.disjs[xl].weight {
                    take_high[xl] = true;
                } else if !cur.is_zero() {
                    return false;
                }
            }
        }
        HitKind::UnboundedSlow { rem } => {
            take_high[loc] = arm_idx == plan.disjs[loc].high_arm;
            let mut chain: Vec<usize> = Vec::new();
            for u in 0..k_r {
                if u == loc {
                    continue;
                }
                if chain
                    .last()
                    .is_none_or(|&prev| plan.disjs[u].atom > plan.disjs[prev].atom)
                {
                    chain.push(u);
                }
            }
            chain.reverse();
            let mut cur = rem.clone();
            for u in chain {
                if cur.is_zero() {
                    break;
                }
                if cur == plan.disjs[u].weight {
                    take_high[u] = true;
                    cur = Int::ZERO;
                    break;
                }
                if plan.disjs[u].high_arm == 0 {
                    take_high[u] = true;
                    cur = &cur - &plan.disjs[u].weight;
                }
            }
            if !cur.is_zero() {
                return false;
            }
        }
    }
    for (idx, d) in plan.disjs.iter().enumerate() {
        let v = if take_high[idx] {
            d.high_val.clone()
        } else {
            d.low_val.clone()
        };
        m.insert(d.atom.clone(), v);
    }
    true
}

struct WideRowSlack {
    row_val: Int,
    up_slack: BTreeSet<(Int, Atom)>,
    up_map: HashMap<Atom, Int>,
    open_up: BTreeSet<Atom>,
    down_slack: BTreeSet<(Int, Atom)>,
    down_map: HashMap<Atom, Int>,
    open_down: BTreeSet<Atom>,
}

/// Incremental witness and feasibility maintainer for [`DisjointWide`] rows with unit (`±1`)
/// coefficients during `settle`'s unit-disjunction absorption.
pub(super) struct WidePointRepairer {
    dw: DisjointWide,
    row_slacks: Vec<WideRowSlack>,
}

impl WidePointRepairer {
    // Complexity tradeoff: inside `settle`, when `r` 2-way disjunctions on a `k`-variable sum row
    // shrink to 1 disjunct (`live.len() == 1`), `local_repair` holds non-seed variables fixed and
    // returns `None` on every equality where `pt[y_i] != v_i`, falling back to `r` full `O(k)`
    // `solve(&base.cons, true)` calls (`O(k^2)` on `ss_untied` at `k >= 256`). Maintaining per-row
    // ordered slack sets (`up_slack`, `down_slack`) over unit-coefficient `DisjointWide` rows
    // checks feasibility in `O(1)` and repairs `pt` by popping the largest opposite slack in
    // `O(log k)` amortized time (`O(k log k)` across an entire `settle` pass), falling back to
    // `solve` on any non-unary or non-unit-coefficient system. Test:
    // `l01_38_presburger::slack_scale::ss_decide_scales`.
    pub(super) fn of_cons(cons: &[Con], pt: &Model) -> Option<Self> {
        if !cons.iter().any(|c| c.lin.terms.len() > 2) {
            return None;
        }
        let dw = DisjointWide::of_cons(cons)?;
        if dw.empty() {
            return None;
        }
        for (a, (lo, hi)) in &dw.ends {
            let z = Int::ZERO;
            let v = pt.get(a).unwrap_or(&z);
            if lo.as_ref().is_some_and(|l| v < l) || hi.as_ref().is_some_and(|h| v > h) {
                return None;
            }
        }
        let mut row_slacks = Vec::with_capacity(dw.rows.len());
        for wr in &dw.rows {
            if !wr.con.lin.terms.values().all(|c| c.abs() == Int::ONE) {
                return None;
            }
            let mut row_val = wr.con.lin.constant.clone();
            let z = Int::ZERO;
            for (a, coef) in &wr.con.lin.terms {
                let v = pt.get(a).unwrap_or(&z);
                row_val = &row_val + &(coef * v);
            }
            if (wr.con.rel == Rel::Eq && !row_val.is_zero())
                || (wr.con.rel == Rel::Ge && row_val.is_negative())
            {
                return None;
            }
            row_slacks.push(WideRowSlack {
                row_val,
                up_slack: BTreeSet::new(),
                up_map: HashMap::new(),
                open_up: BTreeSet::new(),
                down_slack: BTreeSet::new(),
                down_map: HashMap::new(),
                open_down: BTreeSet::new(),
            });
        }
        let mut out = WidePointRepairer { dw, row_slacks };
        let z = Int::ZERO;
        for r_idx in 0..out.dw.rows.len() {
            let atoms: Vec<Atom> = out.dw.rows[r_idx].con.lin.terms.keys().cloned().collect();
            for a in atoms {
                let v = pt.get(&a).unwrap_or(&z).clone();
                out.refresh_atom(r_idx, &a, &v);
            }
        }
        Some(out)
    }

    fn refresh_atom(&mut self, r_idx: usize, a: &Atom, val: &Int) {
        let rs = &mut self.row_slacks[r_idx];
        if let Some(old_u) = rs.up_map.remove(a) {
            rs.up_slack.remove(&(old_u, a.clone()));
        }
        rs.open_up.remove(a);
        if let Some(old_d) = rs.down_map.remove(a) {
            rs.down_slack.remove(&(old_d, a.clone()));
        }
        rs.open_down.remove(a);

        let default_e = (None, None);
        let e = self.dw.ends.get(a).unwrap_or(&default_e);
        let coef = &self.dw.rows[r_idx].con.lin.terms[a];
        let (sl, sh) = signed_ends(e, coef);
        let cur = coef * val;
        match sh {
            Some(hi_s) => {
                let s_up = &hi_s - &cur;
                if s_up.is_positive() {
                    rs.up_slack.insert((s_up.clone(), a.clone()));
                    rs.up_map.insert(a.clone(), s_up);
                }
            }
            None => {
                rs.open_up.insert(a.clone());
            }
        }
        match sl {
            Some(lo_s) => {
                let s_dn = &cur - &lo_s;
                if s_dn.is_positive() {
                    rs.down_slack.insert((s_dn.clone(), a.clone()));
                    rs.down_map.insert(a.clone(), s_dn);
                }
            }
            None => {
                rs.open_down.insert(a.clone());
            }
        }
    }

    pub(super) fn repair_unary(&mut self, pt: &mut Model, added: &[Con]) -> Option<Result<(), ()>> {
        let mut updates: BTreeMap<Atom, Ends> = BTreeMap::new();
        for c in added {
            let (atom, b, bad) = unary_bound(c)?;
            if bad {
                self.dw.empty = true;
                return Some(Err(()));
            }
            if let Some(a) = atom {
                let entry = updates.entry(a).or_insert((None, None));
                if meet_ends(entry, b) {
                    self.dw.empty = true;
                    return Some(Err(()));
                }
            }
        }

        let mut touched_rows: BTreeSet<usize> = BTreeSet::new();
        for (a, add_e) in updates {
            let old_e = self.dw.ends.get(&a).cloned().unwrap_or((None, None));
            let mut new_e = old_e.clone();
            if meet_ends(&mut new_e, add_e) {
                self.dw.empty = true;
                return Some(Err(()));
            }
            let old_v = pt.get(&a).cloned().unwrap_or(Int::ZERO);
            let mut new_v = old_v.clone();
            if let Some(l) = &new_e.0
                && new_v < *l
            {
                new_v = l.clone();
            }
            if let Some(h) = &new_e.1
                && new_v > *h
            {
                new_v = h.clone();
            }
            let r_opt = self.dw.atom_row.get(&a).copied();
            if new_e != old_e {
                if let Some(r_idx) = r_opt {
                    let wr = &mut self.dw.rows[r_idx];
                    let coef = &wr.con.lin.terms[&a];
                    let (ol, oh) = signed_ends(&old_e, coef);
                    let (nl, nh) = signed_ends(&new_e, coef);
                    wr.least.remove(ol.as_ref());
                    wr.most.remove(oh.as_ref());
                    wr.least.add(nl.as_ref());
                    wr.most.add(nh.as_ref());
                    if wr.is_empty() {
                        self.dw.empty = true;
                        return Some(Err(()));
                    }
                }
                self.dw.ends.insert(a.clone(), new_e.clone());
            }
            if new_v != old_v {
                pt.insert(a.clone(), new_v.clone());
                if let Some(r_idx) = r_opt {
                    let delta = &self.dw.rows[r_idx].con.lin.terms[&a] * &(&new_v - &old_v);
                    self.row_slacks[r_idx].row_val = &self.row_slacks[r_idx].row_val + &delta;
                    touched_rows.insert(r_idx);
                }
            } else if !pt.contains_key(&a) && !new_v.is_zero() {
                pt.insert(a.clone(), new_v.clone());
            }
            if let Some(r_idx) = r_opt
                && (new_e != old_e || new_v != old_v)
            {
                self.refresh_atom(r_idx, &a, &new_v);
            }
        }

        for r_idx in touched_rows {
            let rel = self.dw.rows[r_idx].con.rel;
            while self.row_slacks[r_idx].row_val.is_negative() {
                let need = -&self.row_slacks[r_idx].row_val;
                if let Some(b) = self.row_slacks[r_idx].open_up.iter().next().cloned() {
                    let coef = self.dw.rows[r_idx].con.lin.terms[&b].clone();
                    let old_b = pt.get(&b).cloned().unwrap_or(Int::ZERO);
                    let new_b = &old_b + &(&coef * &need);
                    pt.insert(b.clone(), new_b.clone());
                    self.row_slacks[r_idx].row_val = Int::ZERO;
                    self.refresh_atom(r_idx, &b, &new_b);
                } else if let Some((s_b, b)) = self.row_slacks[r_idx].up_slack.last().cloned() {
                    let take_amt = (&need).min(&s_b).clone();
                    let coef = self.dw.rows[r_idx].con.lin.terms[&b].clone();
                    let old_b = pt.get(&b).cloned().unwrap_or(Int::ZERO);
                    let new_b = &old_b + &(&coef * &take_amt);
                    pt.insert(b.clone(), new_b.clone());
                    self.row_slacks[r_idx].row_val = &self.row_slacks[r_idx].row_val + &take_amt;
                    self.refresh_atom(r_idx, &b, &new_b);
                } else {
                    return None;
                }
            }
            if rel == Rel::Eq {
                while self.row_slacks[r_idx].row_val.is_positive() {
                    let need = self.row_slacks[r_idx].row_val.clone();
                    if let Some(b) = self.row_slacks[r_idx].open_down.iter().next().cloned() {
                        let coef = self.dw.rows[r_idx].con.lin.terms[&b].clone();
                        let old_b = pt.get(&b).cloned().unwrap_or(Int::ZERO);
                        let new_b = &old_b - &(&coef * &need);
                        pt.insert(b.clone(), new_b.clone());
                        self.row_slacks[r_idx].row_val = Int::ZERO;
                        self.refresh_atom(r_idx, &b, &new_b);
                    } else if let Some((s_b, b)) = self.row_slacks[r_idx].down_slack.last().cloned()
                    {
                        let take_amt = (&need).min(&s_b).clone();
                        let coef = self.dw.rows[r_idx].con.lin.terms[&b].clone();
                        let old_b = pt.get(&b).cloned().unwrap_or(Int::ZERO);
                        let new_b = &old_b - &(&coef * &take_amt);
                        pt.insert(b.clone(), new_b.clone());
                        self.row_slacks[r_idx].row_val =
                            &self.row_slacks[r_idx].row_val - &take_amt;
                        self.refresh_atom(r_idx, &b, &new_b);
                    } else {
                        return None;
                    }
                }
            }
        }

        Some(Ok(()))
    }
}

#[cfg(test)]
mod r6_row_order_tests {
    use super::*;
    use crate::scaling;
    use std::hint::black_box;

    #[test]
    fn disjoint_row_orders_scale_and_match() {
        let red = std::env::var_os("PDCX_RED").is_some();
        let (mut counts, mut unit) = (Vec::new(), "");
        for n in [64, 512, 4096] {
            let atoms: Vec<Atom> = (0..4 * n)
                .map(|i| Atom::Sym(format!("a{i}").into()))
                .collect();
            let rank: HashMap<&Atom, usize> =
                atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
            let rows: Vec<Vec<DisjInfo>> = (0..n)
                .map(|r| {
                    (0..4)
                        .rev()
                        .map(|j| DisjInfo {
                            disj_idx: 4 * r + j,
                            atom: atoms[4 * r + j].clone(),
                            low_arm: 0,
                            high_arm: 1,
                            low_val: Int::ZERO,
                            high_val: Int::ONE,
                            weight: Int::ONE,
                        })
                        .collect()
                })
                .collect();
            if n == 64 {
                for row in &rows {
                    super::ROW_ORDER_SCAN.with(|c| c.set(false));
                    let fast = row_order(row, &atoms, &rank);
                    super::ROW_ORDER_SCAN.with(|c| c.set(true));
                    let slow = row_order(row, &atoms, &rank);
                    assert_eq!(fast, slow);
                    assert_eq!(fast, vec![3, 2, 1, 0]);
                }
            }
            super::ROW_ORDER_SCAN.with(|c| c.set(red));
            let mut meter = scaling::Meter::new();
            unit = meter.unit();
            let w = meter.work(|| {
                for row in &rows {
                    black_box(row_order(row, &atoms, &rank));
                }
            });
            super::ROW_ORDER_SCAN.with(|c| c.set(false));
            println!("R6ORDER n={n} red={red} work={}", w.units);
            counts.push(w.units);
        }
        for (i, n) in [64, 512].into_iter().enumerate() {
            let what = format!("row orders, red {red}: n = {n} and {}", 8 * n);
            let ratio = scaling::hold(&what, unit, counts[i], counts[i + 1], 1);
            println!("R6ORDER ratio={ratio}");
        }
    }
}
