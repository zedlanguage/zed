//! One-variable modular Presburger formulas decided by regime decomposition, Chinese Remainder
//! Theorem reduction, short-period hole cutting, and forbidden-box share analysis.
//!
//! After eliminating top-level constant equalities, two-term unit equalities (`x_i = ±x + d_i`),
//! and three-term Euclidean division remainder equalities (`r = ±x + c - m * q`), a formula over
//! a single primary integer variable `x` and its Euclidean or existential congruence quotients
//! reduces to a boolean combination of interval bounds on `x` and residue constraints
//! `x mod m in S`.

mod brooks;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use zedc_int::int::Int;

use super::formula::{Atom, Con, Formula, Id, Lin, Model, Rel};

/// A sorted list of disjoint, non-adjacent closed residue intervals `[lo, hi]` in `0..m`.
type ResidueSet = Vec<(Int, Int)>;

/// A closed interval `[lo, hi]` on the integers, where `None` is unbounded (`-inf` or `+inf`).
type Span = (Option<Int>, Option<Int>);

/// A sorted list of disjoint, non-adjacent closed intervals on the integers.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Domain {
    pieces: Vec<Span>,
}

impl Domain {
    fn empty() -> Self {
        Domain { pieces: Vec::new() }
    }

    fn all() -> Self {
        Domain {
            pieces: vec![(None, None)],
        }
    }

    fn single(v: Int) -> Self {
        Domain {
            pieces: vec![(Some(v.clone()), Some(v))],
        }
    }

    fn ge(lo: Int) -> Self {
        Domain {
            pieces: vec![(Some(lo), None)],
        }
    }

    fn le(hi: Int) -> Self {
        Domain {
            pieces: vec![(None, Some(hi))],
        }
    }

    fn range(lo: Int, hi: Int) -> Self {
        if lo > hi {
            Self::empty()
        } else {
            Domain {
                pieces: vec![(Some(lo), Some(hi))],
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.pieces.is_empty()
    }

    fn is_all(&self) -> bool {
        matches!(self.pieces.as_slice(), [(None, None)])
    }

    fn from_pieces(mut pieces: Vec<Span>) -> Self {
        pieces.retain(|(lo, hi)| match (lo, hi) {
            (Some(l), Some(h)) => l <= h,
            _ => true,
        });
        pieces.sort_by(|a, b| cmp_lo(&a.0, &b.0));
        let mut merged: Vec<Span> = Vec::with_capacity(pieces.len());
        for (lo, hi) in pieces {
            if let Some((_, last_hi)) = merged.last_mut() {
                let joins = match (&*last_hi, &lo) {
                    (None, _) | (_, None) => true,
                    (Some(h), Some(l)) => *l <= h + &Int::ONE,
                };
                if joins {
                    *last_hi = max_hi(last_hi.take(), hi);
                    continue;
                }
            }
            merged.push((lo, hi));
        }
        Domain { pieces: merged }
    }

    fn union(&self, other: &Self) -> Self {
        let mut pieces = Vec::with_capacity(self.pieces.len() + other.pieces.len());
        pieces.extend(self.pieces.iter().cloned());
        pieces.extend(other.pieces.iter().cloned());
        Self::from_pieces(pieces)
    }

    fn complement(&self) -> Self {
        if self.pieces.is_empty() {
            return Self::all();
        }
        let mut out = Vec::with_capacity(self.pieces.len() + 1);
        let mut cur_lo: Option<Int> = None;
        for (lo, hi) in &self.pieces {
            match lo {
                None => {}
                Some(l) => {
                    let prev_hi = l - &Int::ONE;
                    let valid = cur_lo.as_ref().is_none_or(|c| *c <= prev_hi);
                    if valid {
                        out.push((cur_lo, Some(prev_hi)));
                    }
                }
            }
            match hi {
                None => return Domain { pieces: out },
                Some(h) => cur_lo = Some(h + &Int::ONE),
            }
        }
        out.push((cur_lo, None));
        Domain { pieces: out }
    }

    fn intersect(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        let (mut i, mut j) = (0, 0);
        while i < self.pieces.len() && j < other.pieces.len() {
            let (l1, h1) = &self.pieces[i];
            let (l2, h2) = &other.pieces[j];
            let lo = max_lo(l1.clone(), l2.clone());
            let hi = min_hi(h1.clone(), h2.clone());
            let valid = match (&lo, &hi) {
                (Some(l), Some(h)) => l <= h,
                _ => true,
            };
            if valid {
                out.push((lo, hi));
            }
            let adv_i = match (h1, h2) {
                (None, _) => false,
                (_, None) => true,
                (Some(a), Some(b)) => a <= b,
            };
            if adv_i {
                i += 1;
            } else {
                j += 1;
            }
        }
        Domain { pieces: out }
    }

    fn contains_span(&self, lo: &Option<Int>, hi: &Option<Int>) -> bool {
        // Complexity tradeoff: scanning s disjoint intervals for each point
        // costs O(s) per lookup. Their sorted starts locate the only possible
        // containing interval in O(log s) comparisons. Nothing is given up for
        // the nonempty spans callers pass. Tests: pncx_domain_membership_scale
        // (the scan fails) and pncx_domain_membership_matches_scan.
        let end = self.pieces.partition_point(|(l, _)| !cmp_lo(l, lo).is_gt());
        let Some((_, h)) = end.checked_sub(1).and_then(|i| self.pieces.get(i)) else {
            return false;
        };
        match (h, hi) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(a), Some(b)) => a >= b,
        }
    }
}

fn cmp_lo(a: &Option<Int>, b: &Option<Int>) -> std::cmp::Ordering {
    match (a, b) {
        (None, None) => std::cmp::Ordering::Equal,
        (None, Some(_)) => std::cmp::Ordering::Less,
        (Some(_), None) => std::cmp::Ordering::Greater,
        (Some(x), Some(y)) => x.cmp(y),
    }
}

fn max_lo(a: Option<Int>, b: Option<Int>) -> Option<Int> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(x), Some(y)) => Some(x.max(y)),
    }
}

fn min_hi(a: Option<Int>, b: Option<Int>) -> Option<Int> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(x), Some(y)) => Some(x.min(y)),
    }
}

fn max_hi(a: Option<Int>, b: Option<Int>) -> Option<Int> {
    match (a, b) {
        (None, _) | (_, None) => None,
        (Some(x), Some(y)) => Some(x.max(y)),
    }
}

/// Normalizes a collection of closed intervals in `0..m` into a sorted, disjoint, non-adjacent
/// `ResidueSet`.
fn res_normalize(mut intervals: Vec<(Int, Int)>, m: &Int) -> ResidueSet {
    let max_r = m - &Int::ONE;
    intervals.retain(|(l, h)| *l <= *h && *h >= Int::ZERO && *l <= max_r);
    for (l, h) in &mut intervals {
        if *l < Int::ZERO {
            *l = Int::ZERO;
        }
        if *h > max_r {
            *h = max_r.clone();
        }
    }
    intervals.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out: ResidueSet = Vec::with_capacity(intervals.len());
    for (lo, hi) in intervals {
        if let Some((_, last_hi)) = out.last_mut()
            && lo <= &*last_hi + &Int::ONE
        {
            if hi > *last_hi {
                *last_hi = hi;
            }
            continue;
        }
        out.push((lo, hi));
    }
    out
}

fn res_complement(s: &[(Int, Int)], m: &Int) -> ResidueSet {
    let max_r = m - &Int::ONE;
    if s.is_empty() {
        return vec![(Int::ZERO, max_r)];
    }
    let mut out = Vec::with_capacity(s.len() + 1);
    let mut cur = Int::ZERO;
    for (lo, hi) in s {
        if cur < *lo {
            out.push((cur, lo - &Int::ONE));
        }
        cur = hi + &Int::ONE;
    }
    if cur <= max_r {
        out.push((cur, max_r));
    }
    out
}

fn res_union(a: &[(Int, Int)], b: &[(Int, Int)], m: &Int) -> ResidueSet {
    let mut v = Vec::with_capacity(a.len() + b.len());
    v.extend_from_slice(a);
    v.extend_from_slice(b);
    res_normalize(v, m)
}

fn res_intersect(a: &[(Int, Int)], b: &[(Int, Int)]) -> ResidueSet {
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let lo = (&a[i].0).max(&b[j].0);
        let hi = (&a[i].1).min(&b[j].1);
        if lo <= hi {
            out.push((lo.clone(), hi.clone()));
        }
        if a[i].1 <= b[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

fn res_diff(a: &[(Int, Int)], b: &[(Int, Int)], m: &Int) -> ResidueSet {
    let comp = res_complement(b, m);
    res_intersect(a, &comp)
}

fn res_is_full(s: &[(Int, Int)], m: &Int) -> bool {
    matches!(s, [(lo, hi)] if lo.is_zero() && *hi == m - &Int::ONE)
}

fn res_count(s: &[(Int, Int)]) -> Int {
    let mut total = Int::ZERO;
    for (lo, hi) in s {
        total = &total + &(&(hi - lo) + &Int::ONE);
    }
    total
}

fn res_contains(s: &[(Int, Int)], r: &Int) -> bool {
    let idx = s.partition_point(|(_, hi)| hi < r);
    idx < s.len() && s[idx].0 <= *r
}

/// Maps the residue interval `[a, b]` of `rem = (s_x * x + c_lo) mod m` (where `0 <= a <= b < m`
/// and `s_x` is `1` or `-1`) to a `ResidueSet` for `x mod m`.
fn shift_residue_interval(a: &Int, b: &Int, s_x: i8, c_lo: &Int, m: &Int) -> ResidueSet {
    if a > b {
        return Vec::new();
    }
    let width = b - a;
    if width >= m - &Int::ONE {
        return vec![(Int::ZERO, m - &Int::ONE)];
    }
    // If s_x == 1: (x + c_lo) mod m in [a, b]  <=>  x mod m in [a - c_lo, b - c_lo] mod m.
    // If s_x == -1: (-x + c_lo) mod m in [a, b] <=>  x mod m in [c_lo - b, c_lo - a] mod m.
    let (start, end) = if s_x > 0 {
        ((a - c_lo).mod_floor_wide(m), (b - c_lo).mod_floor_wide(m))
    } else {
        ((c_lo - b).mod_floor_wide(m), (c_lo - a).mod_floor_wide(m))
    };
    if start <= end {
        vec![(start, end)]
    } else {
        vec![(Int::ZERO, end), (start, m - &Int::ONE)]
    }
}

/// Global Euclidean quotient definition:
/// `0 <= (s_x * x + c_lo) - sigma_q * m * q <= w`, where `0 <= w <= m - 1`, `s_x in {-1, 1}`,
/// `sigma_q in {-1, 1}`, `m >= 2`.
#[derive(Clone, Debug)]
struct GlobalQuot {
    s_x: i8,
    c_lo: Int,
    sigma_q: i8,
    m: Int,
    w: Int,
}

/// Local existential quotient window:
/// `0 <= (s_x * x + c_lo) - sigma_q * m * q <= w`, where `0 <= w <= m - 1`.
#[derive(Clone, Debug)]
struct LocalWindow {
    s_x: i8,
    c_lo: Int,
    sigma_q: i8,
    m: Int,
    w: Int,
}

/// Complete three-term remainder definition including `x_root`.
#[derive(Clone, Debug)]
struct FullRemDef {
    c_r: i8,
    x_root: Atom,
    c_x: Int,
    q_root: Atom,
    c_q: Int,
    k: Int,
}

/// A flat clause over `x`: `(x in bounds) || OR_{(m, S) in mods} (x mod m in S)`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct FlatClause {
    bounds: Domain,
    mods: BTreeMap<Int, ResidueSet>,
}

impl FlatClause {
    fn falsum() -> Self {
        FlatClause {
            bounds: Domain::empty(),
            mods: BTreeMap::new(),
        }
    }

    fn verum() -> Self {
        FlatClause {
            bounds: Domain::all(),
            mods: BTreeMap::new(),
        }
    }

    fn is_true(&self) -> bool {
        self.bounds.is_all()
    }

    fn is_false(&self) -> bool {
        self.bounds.is_empty() && self.mods.is_empty()
    }

    fn or(&self, other: &Self) -> Self {
        if self.is_true() || other.is_true() {
            return Self::verum();
        }
        let bounds = self.bounds.union(&other.bounds);
        if bounds.is_all() {
            return Self::verum();
        }
        let mut mods = self.mods.clone();
        for (m, s) in &other.mods {
            let entry = mods.entry(m.clone()).or_default();
            let u = res_union(entry, s, m);
            if res_is_full(&u, m) {
                return Self::verum();
            }
            *entry = u;
        }
        FlatClause { bounds, mods }
    }
}

/// Partially built window on a local existential quotient `q` inside an effective `And`.
#[derive(Clone, PartialEq, Eq, Debug)]
struct HalfWin {
    q_root: Atom,
    s_x: i8,
    sigma_q: i8,
    m: Int,
    lo: Option<Int>,
    hi: Option<Int>,
}

/// Bottom-up node representation during `Formula::fold`.
#[derive(Clone, Debug)]
struct FoldNode {
    clauses: Vec<FlatClause>,
    half_wins: Vec<HalfWin>,
    local_quots: BTreeSet<Atom>,
}

impl FoldNode {
    fn from_clause(c: FlatClause) -> Self {
        let clauses = if c.is_true() { Vec::new() } else { vec![c] };
        FoldNode {
            clauses,
            half_wins: Vec::new(),
            local_quots: BTreeSet::new(),
        }
    }
}

/// Union-Find with potentials `atom = sign * root + offset`, `sign in {-1, 1}`.
struct UnitUf {
    parent: HashMap<Atom, (Atom, i8, Int)>,
}

impl UnitUf {
    fn new() -> Self {
        UnitUf {
            parent: HashMap::new(),
        }
    }

    fn ensure(&mut self, a: &Atom) {
        if !self.parent.contains_key(a) {
            self.parent.insert(a.clone(), (a.clone(), 1, Int::ZERO));
        }
    }

    /// The root of `a` with `a = s * root + d`, compressing the path. A loop, not recursion:
    /// the parent chain can be as long as the number of unit equalities.
    fn find(&mut self, a: &Atom) -> (Atom, i8, Int) {
        self.ensure(a);
        let mut path: Vec<Atom> = Vec::new();
        let mut cur = a.clone();
        loop {
            let p = &self.parent[&cur].0;
            if *p == cur {
                break;
            }
            let next = p.clone();
            path.push(cur);
            cur = next;
        }
        let root = cur;
        // Walk back from the atom nearest the root: each link `v = s * p + d` with `p` already
        // pointing at the root as `p = ps * root + pd` becomes `v = (s * ps) * root + (s * pd + d)`.
        let (mut rs, mut rd): (i8, Int) = (1, Int::ZERO);
        for v in path.iter().rev() {
            let (_, s, d) = self.parent[v].clone();
            let new_s = s * rs;
            let new_d = if s > 0 { &rd + &d } else { &d - &rd };
            self.parent
                .insert(v.clone(), (root.clone(), new_s, new_d.clone()));
            rs = new_s;
            rd = new_d;
        }
        if path.is_empty() {
            (root, 1, Int::ZERO)
        } else {
            (root, rs, rd)
        }
    }

    /// Points every atom straight at its root, so that each later [`UnitUf::get`] follows at
    /// most one link.
    // Complexity tradeoff: `get` takes `&self` and cannot compress, so after a chain of unions
    // written in descending name order each `get` walked the whole chain, Omega(n^2) over the
    // atoms (I6.11, `r6_tests::pncx_affine_alias_chain_scale`, 61.0 times the work for 8 times
    // the aliases). Compressing every path once after the unions costs O(n log n) amortized
    // (path compression with linking by name, Tarjan and van Leeuwen 1984), and the roots, signs
    // and offsets are the same, so no answer depends on it. Nothing is given up.
    fn flatten(&mut self) {
        let mut atoms: Vec<Atom> = self.parent.keys().cloned().collect();
        atoms.sort();
        for a in &atoms {
            self.find(a);
        }
    }

    fn get(&self, a: &Atom) -> (Atom, i8, Int) {
        let mut cur = a.clone();
        let mut s: i8 = 1;
        let mut d = Int::ZERO;
        while let Some((p, ps, pd)) = self.parent.get(&cur) {
            if p == &cur {
                return (cur, s, d);
            }
            d = if s > 0 { &d + pd } else { &d - pd };
            s *= *ps;
            cur = p.clone();
        }
        (a.clone(), 1, Int::ZERO)
    }

    /// Links `a = s * b + d`. Returns `Err(())` on contradiction, or `Ok(Some((root, val)))` when
    /// an opposite-sign cycle fixes `root` to an integer `val`.
    fn union(&mut self, a: &Atom, b: &Atom, s: i8, d: &Int) -> Result<Option<(Atom, Int)>, ()> {
        let (ra, sa, da) = self.find(a);
        let (rb, sb, db) = self.find(b);
        // sa * ra + da = s * (sb * rb + db) + d
        // sa * ra = (s * sb) * rb + (s * db + d - da)
        let s_db = if s > 0 { db } else { -&db };
        let rhs_const = &(&s_db + d) - &da;
        let rel_s = sa * s * sb;
        let rel_d = if sa > 0 { rhs_const } else { -&rhs_const };
        // Now ra = rel_s * rb + rel_d.
        if ra == rb {
            if rel_s == 1 {
                if !rel_d.is_zero() {
                    return Err(());
                }
                return Ok(None);
            } else {
                // 2 * ra = rel_d
                let two = Int::from(2);
                if !rel_d.mod_floor_wide(&two).is_zero() {
                    return Err(());
                }
                return Ok(Some((ra, rel_d.div_floor_wide(&two))));
            }
        }
        // Choose canonical root: prefer smaller Atom so order of equations doesn't matter.
        if ra > rb {
            self.parent.insert(ra, (rb, rel_s, rel_d));
        } else {
            // rb = rel_s * (ra - rel_d) = rel_s * ra - rel_s * rel_d
            let inv_d = if rel_s > 0 { -&rel_d } else { rel_d };
            self.parent.insert(rb, (ra, rel_s, inv_d));
        }
        Ok(None)
    }
}

fn rewrite_lin_full(
    lin: &Lin,
    fixed: &HashMap<Atom, Int>,
    uf: &UnitUf,
    rem_defs: &HashMap<Atom, FullRemDef>,
) -> Lin {
    let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
    let mut constant = lin.constant.clone();
    for (a, k) in &lin.terms {
        if let Some(v) = fixed.get(a) {
            constant = &constant + &(k * v);
            continue;
        }
        let (r1, s1, d1) = uf.get(a);
        if let Some(v) = fixed.get(&r1) {
            let val = if s1 > 0 { v + &d1 } else { &d1 - v };
            constant = &constant + &(k * &val);
            continue;
        }
        constant = &constant + &(k * &d1);
        let k1 = if s1 > 0 { k.clone() } else { -k };
        if let Some(rem) = rem_defs.get(&r1) {
            let factor = if rem.c_r > 0 { -&k1 } else { k1 };
            constant = &constant + &(&factor * &rem.k);
            let e_x = terms.entry(rem.x_root.clone()).or_insert(Int::ZERO);
            *e_x = &*e_x + &(&factor * &rem.c_x);
            let e_q = terms.entry(rem.q_root.clone()).or_insert(Int::ZERO);
            *e_q = &*e_q + &(&factor * &rem.c_q);
        } else {
            let e = terms.entry(r1).or_insert(Int::ZERO);
            *e = &*e + &k1;
        }
    }
    terms.retain(|_, v| !v.is_zero());
    Lin { terms, constant }
}

/// Decides `f` (and builds a `Model` when `want_model` is set) if `f` is a one-variable modular
/// formula after eliminating constant equalities, unit equalities, and Euclidean division
/// remainders. Returns `None` if `f` lies outside this scope (e.g., has products, zero moduli, or
/// two independent non-quotient variables).
// Complexity tradeoff: a conjunction `C && (D1 || ... || Dk)` is not split into `k` solves of
// `C && Di` (R5-CLAUDE-5): that split cost O(k |C|) when no part had a point, which made
// `l01_39_reduced_product::named_test::arms_of_named_limits_in_side_by_side_tiers_take_time_near_linear_in_the_depth`
// take 17.1 times the work for 8 times the depth (limit 14.2). It was added for the `fails`
// questions of pairs (I3.2), which the zero witness and the batched remainder check now answer
// near-linearly (`one_scope::the_fails_questions_of_pairs_scale`,
// `pncx_probe::pncx_pairs_scale`, `pncx_probe::pncx_disj_scale` pass without it). What is
// given up: such a formula goes to the general path whole; no answer of the 5,000-formula
// enumeration test changed (sat 4277, empty 712, refused 11 with and without the split).
pub fn solve_modular(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    // A remainder row whose two unit terms tie (`solve_modular_whole`, step 3) is read one way
    // first and, if that gives no answer, the other way: at most two runs, each exact.
    // If neither gives an answer and some row had both unit terms bounded to less than a period,
    // a last run takes the previous choice by `Atom` order (as Codex did in round 7, R7-CODEX-2):
    // without it the 5,000-formula enumeration test refused 70 formulas instead of 11. Each of
    // the at most three runs is exact; only the last reads names, and only when the others refuse.
    let mut tied = false;
    let mut both_bounded = false;
    let found = match solve_modular_whole(f, want_model, false, false, &mut tied, &mut both_bounded)
    {
        None if tied => {
            solve_modular_whole(f, want_model, true, false, &mut tied, &mut both_bounded)
        }
        found => found,
    };
    match found {
        None if both_bounded => {
            solve_modular_whole(f, want_model, false, true, &mut tied, &mut both_bounded)
        }
        found => found,
    }
}

fn solve_modular_whole(
    f: &Formula,
    want_model: bool,
    flip_ties: bool,
    by_atom_order: bool,
    tied: &mut bool,
    both_bounded: &mut bool,
) -> Option<Option<Model>> {
    // Collect top-level conjunction and verify no Product atoms exist anywhere in `f`.
    let mut top_cons: Vec<&Con> = Vec::new();
    let mut top_clauses: Vec<&Formula> = Vec::new();
    let mut seen_top: HashSet<Id> = HashSet::new();
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        match g {
            Formula::And(gs) => {
                if seen_top.insert(Id::any(g)) {
                    stack.extend(gs.iter().rev());
                }
            }
            Formula::Con(c) => top_cons.push(c),
            Formula::Or(ds) if ds.is_empty() => return Some(None),
            Formula::Or(_) | Formula::Not(_) => {
                if seen_top.insert(Id::any(g)) {
                    top_clauses.push(g);
                }
            }
        }
    }

    // Check all constraints in the DAG for products, at least one non-unit coefficient, and collect all atoms.
    // `Formula::walk` and not `Formula::cons`, which is written in presburger.rs: a call of it
    // here would close an import cycle with presburger.rs (step S.1f). The list is the same.
    let mut all_cons = Vec::new();
    f.walk(&mut |c| all_cons.push(c));
    if all_cons.is_empty() {
        return None;
    }
    let mut has_modulus = false;
    let mut all_atoms: BTreeSet<Atom> = BTreeSet::new();
    for c in &all_cons {
        for (a, k) in &c.lin.terms {
            if matches!(a, Atom::Product(..)) {
                return None;
            }
            if !k.is_unit() {
                has_modulus = true;
            }
            all_atoms.insert(a.clone());
        }
    }
    if !has_modulus {
        return None;
    }

    // A zero assignment is a direct witness, including for the negation of a
    // modular conjunction whose quotient definitions all hold at zero. Checking
    // it before extracting local quotients avoids sending that easy disjunction
    // to general elimination. One visited DAG walk, O(n) arithmetic operations;
    // no search and no conclusion if it fails. Tests: pncx_disj_scale and
    // pncx_pairs_scale; their negative control omits this witness.
    let zero = Model::new();
    if f.holds_as(&zero) {
        return Some(Some(if want_model {
            all_atoms.into_iter().map(|a| (a, Int::ZERO)).collect()
        } else {
            zero
        }));
    }

    // Step 1: Constant equalities propagation (`k * a + c == 0`) and Unit equalities (`a = ±b + d`).
    let mut fixed: HashMap<Atom, Int> = HashMap::new();
    let mut uf = UnitUf::new();
    for a in &all_atoms {
        uf.ensure(a);
    }

    // Complexity tradeoff: repeating the pass over every row until a pass fixes nothing costs
    // one pass per atom fixed in a chain (`2 a_i == 2 a_(i+1)` written so that each pass fixes
    // one more), O(n^2) rows read (R7-CLAUDE-1, `r7_tests::pncx_fixed_chain_scale`), and a pass
    // that only joined two classes stopped the loop, so a row read before the join was never
    // read again and the result followed the order of the rows. A worklist reads each row once,
    // and again only when its class is fixed (once per row) or joined with a smaller class
    // whose rows it also lists (O(log n) times per row, the smaller list moving into the larger),
    // O(n log n) row reads in all. Its result is the fixpoint of the same sound rules, the same
    // for every order of the rows. Nothing is given up.
    let mut class_rows: HashMap<Atom, Vec<usize>> = HashMap::new();
    for (i, c) in top_cons.iter().enumerate() {
        for a in c.lin.terms.keys() {
            class_rows.entry(a.clone()).or_default().push(i);
        }
    }
    let mut queued = vec![true; top_cons.len()];
    let mut queue: VecDeque<usize> = (0..top_cons.len()).collect();
    // Puts the rows of the class of `root` back in the queue.
    fn requeue(rows: Option<&Vec<usize>>, queued: &mut [bool], queue: &mut VecDeque<usize>) {
        for &i in rows.into_iter().flatten() {
            if !queued[i] {
                queued[i] = true;
                queue.push_back(i);
            }
        }
    }
    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        let c = &top_cons[i];
        // Compress the paths of this row's atoms first, so that `rewrite_lin_full`'s `get`
        // follows one link while unions are still being made (I6.11).
        for a in c.lin.terms.keys() {
            uf.find(a);
        }
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &HashMap::new());
        if lin.terms.is_empty() {
            let bad = match c.rel {
                Rel::Ge => lin.constant.is_negative(),
                Rel::Eq => !lin.constant.is_zero(),
            };
            if bad {
                return Some(None);
            }
            continue;
        }
        if c.rel == Rel::Eq && lin.terms.len() == 1 {
            let (a, k) = lin.terms.iter().next()?;
            let d = k.abs();
            if !lin.constant.mod_floor_wide(&d).is_zero() {
                return Some(None);
            }
            let val = if k.is_positive() {
                (-&lin.constant).div_floor_wide(&d)
            } else {
                lin.constant.div_floor_wide(&d)
            };
            if let Some(old) = fixed.get(a) {
                if *old != val {
                    return Some(None);
                }
            } else {
                fixed.insert(a.clone(), val);
                requeue(class_rows.get(a), &mut queued, &mut queue);
            }
        } else if c.rel == Rel::Eq && lin.terms.len() == 2 {
            let mut it = lin.terms.iter();
            let (a, ka) = it.next()?;
            let (b, kb) = it.next()?;
            if ka.is_unit() && kb.is_unit() {
                // ka * a + kb * b + constant == 0  =>  a = (-ka*kb) * b + (-ka * constant)
                let sa: i8 = if ka.is_positive() { 1 } else { -1 };
                let sb: i8 = if kb.is_positive() { 1 } else { -1 };
                let s = -(sa * sb);
                let d = if sa > 0 {
                    -&lin.constant
                } else {
                    lin.constant.clone()
                };
                // `a` and `b` are roots of two classes, neither fixed (`rewrite_lin_full`).
                let joined = uf.union(a, b, s, &d);
                let root = uf.find(a).0;
                let (small, large) = {
                    let ra = class_rows.remove(a).unwrap_or_default();
                    let rb = class_rows.remove(b).unwrap_or_default();
                    if ra.len() < rb.len() {
                        (ra, rb)
                    } else {
                        (rb, ra)
                    }
                };
                requeue(Some(&small), &mut queued, &mut queue);
                let mut large = large;
                large.extend(small);
                match joined {
                    Err(()) => return Some(None),
                    Ok(Some((fixed_root, val))) => {
                        if let Some(old) = fixed.get(&fixed_root) {
                            if *old != val {
                                return Some(None);
                            }
                        } else {
                            fixed.insert(fixed_root, val);
                            requeue(Some(&large), &mut queued, &mut queue);
                        }
                    }
                    Ok(None) => {}
                }
                class_rows.insert(root, large);
            }
        }
    }

    uf.flatten();

    // Step 2: Identify 1-term bounds on root atoms to help recognize 3-term division remainders
    // (`x_root + c - m * q_root - r_root == 0` with `0 <= r <= m - 1`).
    let empty_rems: HashMap<Atom, FullRemDef> = HashMap::new();
    let mut root_bounds: HashMap<Atom, (Option<Int>, Option<Int>)> = HashMap::new();
    for c in &top_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
        if lin.terms.len() == 1 {
            let (a, k) = lin.terms.iter().next()?;
            let d = k.abs();
            let entry = root_bounds.entry(a.clone()).or_insert((None, None));
            match c.rel {
                Rel::Ge if k.is_positive() => {
                    let lo = -&lin.constant.div_floor_wide(&d);
                    entry.0 = max_lo(entry.0.take(), Some(lo));
                }
                Rel::Ge => {
                    let hi = lin.constant.div_floor_wide(&d);
                    entry.1 = min_hi(entry.1.take(), Some(hi));
                }
                Rel::Eq => {}
            }
        }
    }
    for (lo, hi) in root_bounds.values() {
        if let (Some(l), Some(h)) = (lo, hi)
            && l > h
        {
            return Some(None);
        }
    }

    // Step 3: Recognize 3-term division remainder equalities:
    // `c_x * x_root + c_q * q_root + c_r * r_root + k == 0` where `|c_x| == 1`, `|c_r| == 1`,
    // `|c_q| = m >= 2`, and `r_root` is bounded to an interval of width `< m`.
    let mut rem_defs: HashMap<Atom, FullRemDef> = HashMap::new();
    for c in &top_cons {
        if c.rel != Rel::Eq {
            continue;
        }
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
        if lin.terms.len() != 3 {
            continue;
        }
        let terms: Vec<(&Atom, &Int)> = lin.terms.iter().collect();
        // Find the unique term with |coef| >= 2 (`q_root`), and the two unit terms.
        let mut non_unit = Vec::new();
        let mut units = Vec::new();
        for &(a, k) in &terms {
            if k.is_unit() {
                units.push((a, k));
            } else {
                non_unit.push((a, k));
            }
        }
        if non_unit.len() != 1 || units.len() != 2 {
            continue;
        }
        let (q_root, c_q) = non_unit[0];
        let m = c_q.abs();
        // Check which of `units[0]` or `units[1]` is bounded to width < m (`r_root`): its key is
        // whether its bounds span exactly one period, then the width of its bounds.
        let rem_key = |a: &Atom| -> Option<(bool, Int)> {
            if let Some((Some(lo), Some(hi))) = root_bounds.get(a)
                && lo <= hi
                && (hi - lo) < m
            {
                let width = hi - lo;
                Some((&width + &Int::ONE == m, width))
            } else {
                None
            }
        };
        let ((r_root, c_r), (x_root, c_x)) = match (rem_key(units[0].0), rem_key(units[1].0)) {
            (Some(_), None) => (units[0], units[1]),
            (None, Some(_)) => (units[1], units[0]),
            // Both are bounded to less than a period, and either reading `x = m q + r` is exact.
            // The remainder is chosen by the formula, never by a name (I6.3): the term whose
            // bounds span exactly one period, else the wider. On a tie the term whose coefficient
            // has the sign of `c_q` is taken first, the other in the second run of
            // `solve_modular`; a renaming can change these signs (the root of a class whose
            // aliases have sign -1), so a tie is name-independent only through the second run.
            // The last run of `solve_modular` (`by_atom_order`) takes the larger `Atom` as `r`.
            (Some(k0), Some(k1)) => {
                *both_bounded = true;
                let k = if by_atom_order {
                    units[0].0.cmp(units[1].0)
                } else {
                    k0.cmp(&k1)
                };
                match k {
                    std::cmp::Ordering::Greater => (units[0], units[1]),
                    std::cmp::Ordering::Less => (units[1], units[0]),
                    std::cmp::Ordering::Equal => {
                        *tied = true;
                        let first = (units[0].1.is_positive() == c_q.is_positive()) != flip_ties;
                        if first {
                            (units[0], units[1])
                        } else {
                            (units[1], units[0])
                        }
                    }
                }
            }
            (None, None) => continue,
        };
        if rem_defs.contains_key(r_root) || rem_defs.contains_key(x_root) {
            continue;
        }
        rem_defs.insert(
            r_root.clone(),
            FullRemDef {
                c_r: if c_r.is_positive() { 1 } else { -1 },
                x_root: x_root.clone(),
                c_x: c_x.clone(),
                q_root: q_root.clone(),
                c_q: c_q.clone(),
                k: lin.constant.clone(),
            },
        );
    }

    // Step 4: Determine the single primary root variable `x_root` and verify all constraints
    // mention only `x_root` and quotient roots `q_root`.
    let mut candidate_x: Option<Atom> = None;
    let mut has_modulus = false;
    for c in &all_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &rem_defs);
        if lin.terms.len() > 2 {
            return None;
        }
        if lin.terms.len() == 2 {
            let mut it = lin.terms.iter();
            let (a1, k1) = it.next()?;
            let (a2, k2) = it.next()?;
            let (x_cand, q_coef) = match (k1.is_unit(), k2.is_unit()) {
                (true, false) => (a1, k2),
                (false, true) => (a2, k1),
                _ => return None,
            };
            if q_coef.abs() >= Int::from(2) {
                has_modulus = true;
            }
            match &candidate_x {
                None => candidate_x = Some(x_cand.clone()),
                Some(x) if x == x_cand => {}
                Some(_) => return None,
            }
        }
    }
    if !has_modulus {
        return None;
    }
    let x_root = candidate_x?;

    // Step 5: Collect top-level bounds on `(x_root, q_root)` to identify GlobalQuot vs LocalQuot.
    // A constraint with terms `{x_root: c_x, q_root: c_q}` and `|c_x| == 1`, `|c_q| = m >= 2`:
    // Normalize by dividing by `|c_x|`: wait, if `|c_x| > 1` in a 1-term constraint on `q_root`,
    // `c_x == 0`. In a 2-term constraint, `|c_x| == 1` (already checked above).
    #[derive(Default)]
    struct QuotBounds {
        s_x: i8,
        sigma_q: i8,
        m: Int,
        // Bounds on `s_x * x - sigma_q * m * q`: `lo <= s_x * x - sigma_q * m * q <= hi`.
        lo: Option<Int>,
        hi: Option<Int>,
        contradiction: bool,
    }

    let mut q_top: HashMap<Atom, QuotBounds> = HashMap::new();
    for c in &top_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &rem_defs);
        if lin.terms.len() != 2 {
            continue;
        }
        let c_x = lin.terms.get(&x_root)?;
        if !c_x.is_unit() {
            return None;
        }
        let (q_root, c_q) = lin.terms.iter().find(|(a, _)| *a != &x_root)?;
        let m = c_q.abs();
        if m < Int::from(2) {
            return None;
        }
        let entry = q_top.entry(q_root.clone()).or_insert_with(|| {
            // Orient so `s_x = 1`, `sigma_q = -sgn(c_q) * sgn(c_x)`:
            // `c_x * (x - sigma_q * m * q) + constant`.
            let sx: i8 = 1;
            let sq: i8 = if c_x.is_positive() == c_q.is_negative() {
                1
            } else {
                -1
            };
            QuotBounds {
                s_x: sx,
                sigma_q: sq,
                m: m.clone(),
                lo: None,
                hi: None,
                contradiction: false,
            }
        });
        if entry.m != m {
            return None;
        }
        // Express `lin` as `t * (entry.s_x * x - entry.sigma_q * m * q) + constant`, where `t = ±1`.
        let t: i8 = if c_x.is_positive() { 1 } else { -1 };
        let expected_cq = if (-t * entry.sigma_q) > 0 {
            m.clone()
        } else {
            -&m
        };
        if *c_q != expected_cq {
            return None;
        }
        // `t * E + constant >= 0` or `== 0`, where `E = x - sigma_q * m * q`.
        match c.rel {
            Rel::Ge if t > 0 => {
                let l = -&lin.constant;
                entry.lo = max_lo(entry.lo.take(), Some(l));
            }
            Rel::Ge => {
                let h = lin.constant.clone();
                entry.hi = min_hi(entry.hi.take(), Some(h));
            }
            Rel::Eq => {
                let v = if t > 0 {
                    -&lin.constant
                } else {
                    lin.constant.clone()
                };
                entry.lo = max_lo(entry.lo.take(), Some(v.clone()));
                entry.hi = min_hi(entry.hi.take(), Some(v));
            }
        }
        if let (Some(l), Some(h)) = (&entry.lo, &entry.hi)
            && l > h
        {
            entry.contradiction = true;
        }
    }

    let mut global_quots: HashMap<Atom, GlobalQuot> = HashMap::new();
    for (q_root, qb) in q_top {
        if qb.contradiction {
            return Some(None);
        }
        if let (Some(lo), Some(hi)) = (qb.lo, qb.hi) {
            let w = &hi - &lo;
            if w < qb.m {
                // `lo <= x - sigma_q * m * q <= hi`  <=>  `0 <= (x - lo) - sigma_q * m * q <= w`.
                global_quots.insert(
                    q_root,
                    GlobalQuot {
                        s_x: qb.s_x,
                        c_lo: -&lo,
                        sigma_q: qb.sigma_q,
                        m: qb.m,
                        w,
                    },
                );
            }
        }
    }

    // Verify every 1-term constraint in `all_cons` is either on `x_root` or on a `global_quots` key.
    for c in &all_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &rem_defs);
        if lin.terms.len() == 1 {
            let a = lin.terms.keys().next()?;
            if *a != x_root && !global_quots.contains_key(a) {
                return None;
            }
        }
    }

    // Step 6: Fold the formula DAG bottom-up with polarity `negated: bool`.
    // Complexity tradeoff: folding kept conjunction prefixes copies each
    // prefix's clause vector into its parent, O(n^2) payload bytes for n
    // clauses even though the traversal visits each node once. The already
    // collected top-level conjuncts form one flat conjunction in O(n) space;
    // each payload is then combined once at this level. Nothing is given up:
    // conjunction is associative and repeated shared conjuncts are idempotent.
    // Nested conjunctions below alternatives keep the original fold. Test:
    // pncx_kept_prefix_scale; the original fold fails at 28.2x bytes.
    let flat_top = matches!(f, Formula::And(_)).then(|| {
        Formula::And(crate::presburger::Shared::new(
            top_cons
                .iter()
                .map(|c| Formula::Con((*c).clone()))
                .chain(top_clauses.iter().map(|g| (*g).clone()))
                .collect(),
        ))
    });
    let fold_input = flat_top.as_ref().unwrap_or(f);
    let mut local_windows: HashMap<Atom, Vec<LocalWindow>> = HashMap::new();
    let folded: Result<FoldNode, ()> = fold_input.fold(
        false,
        |g, negated| negated != matches!(g, Formula::Not(_)),
        |g, negated, parts: Vec<Result<FoldNode, ()>>| match g {
            Formula::Not(_) => parts.into_iter().next().unwrap_or(Err(())),
            Formula::Con(c) => fold_leaf(
                c,
                negated,
                &x_root,
                &fixed,
                &uf,
                &rem_defs,
                &global_quots,
                &mut local_windows,
            ),
            Formula::And(_) | Formula::Or(_) => {
                let is_and = matches!(g, Formula::And(_)) != negated;
                let mut nodes = Vec::with_capacity(parts.len());
                for p in parts {
                    nodes.push(p?);
                }
                if is_and {
                    fold_and(nodes, &mut local_windows)
                } else {
                    fold_or(nodes)
                }
            }
        },
    );

    let root_node = folded.ok()?;
    if !root_node.half_wins.is_empty() {
        return None;
    }

    // Step 7: Add top-level narrowed windows of `global_quots` (`w < m - 1`) as unit congruences,
    // and separate `root_node.clauses` into global bounds, global unit congruences, and clauses.
    let mut global_bounds = Domain::all();
    // Complexity tradeoff: accumulated restrictions can rebuild O(s^2) pieces.
    // As in fold_and, collect restrictions before intersecting them, so
    // several windows or collapsed clause groups cannot rebuild one growing
    // residue list quadratically. The balanced merge costs O(s log s) in the
    // input intervals; nothing is given up. pncx_pure_residues_scale
    // exercises the same operation.
    let mut unit_inputs: BTreeMap<Int, Vec<ResidueSet>> = BTreeMap::new();
    for gq in global_quots.values() {
        if gq.w < &gq.m - &Int::ONE {
            let s = shift_residue_interval(&Int::ZERO, &gq.w, gq.s_x, &gq.c_lo, &gq.m);
            unit_inputs.entry(gq.m.clone()).or_default().push(s);
        }
    }

    let mut raw_clauses: Vec<FlatClause> = Vec::new();
    for cl in root_node.clauses {
        if cl.is_true() {
            continue;
        }
        if cl.is_false() {
            return Some(None);
        }
        if cl.mods.is_empty() {
            global_bounds = global_bounds.intersect(&cl.bounds);
            if global_bounds.is_empty() {
                return Some(None);
            }
        } else if cl.bounds.is_empty() && cl.mods.len() == 1 {
            let (m, s) = cl.mods.into_iter().next()?;
            unit_inputs.entry(m).or_default().push(s);
        } else {
            raw_clauses.push(cl);
        }
    }

    // Step 8: Merge clauses sharing the same modular part `D` via `(D || B1) && (D || B2) <=> D || (B1 && B2)`.
    // Complexity tradeoff: repeated intersection scans an accumulated domain
    // O(c^2) times in the worst case. Group the uncut domains, then intersect
    // in a balanced tree, O(s log c) interval operations for s input intervals.
    // Restricting every clause to global_bounds would also multiply their
    // sizes; leave that restriction to the segment walk. Nothing is given up.
    // Tests: pncx_bound_merge_enumeration; pncx_bound_merge_scale is deferred to
    // plan row PRES-scaling-10_5 in wt/scratch/deferred-tests/PRES-scaling-10_5.rs.
    let mut by_mods: BTreeMap<BTreeMap<Int, ResidueSet>, Vec<Domain>> = BTreeMap::new();
    for cl in raw_clauses {
        by_mods.entry(cl.mods).or_default().push(cl.bounds);
    }

    let mut mixed_clauses: Vec<FlatClause> = Vec::new();
    for (mods, bounds) in by_mods {
        let bounds = intersect_domains(bounds);
        if bounds.is_empty() {
            if mods.len() == 1 {
                let (m, s) = mods.into_iter().next()?;
                unit_inputs.entry(m).or_default().push(s);
            } else {
                mixed_clauses.push(FlatClause {
                    bounds: Domain::empty(),
                    mods,
                });
            }
        } else {
            mixed_clauses.push(FlatClause { bounds, mods });
        }
    }

    let mut unit_mods = BTreeMap::new();
    for (m, sets) in unit_inputs {
        let residues = intersect_residue_sets(sets);
        if residues.is_empty() {
            return Some(None);
        }
        unit_mods.insert(m, residues);
    }

    // Complexity tradeoff: enumerating all triples costs O(c^3). The sufficient
    // three-clause implication uses O(c log c) grouping and constant work per
    // clause; it can miss implications but never removes a solution. Tested by
    // one_scope::one_variable_modular_formulas_match_enumeration and pncx_random.
    global_bounds = global_bounds.intersect(&forced_pair_bounds(&mixed_clauses));
    if global_bounds.is_empty() {
        return Some(None);
    }

    // Step 9: Partition `global_bounds` at all bound endpoints of `mixed_clauses` into
    // bound-homogeneous regimes `[lo_r, hi_r]`.
    let regimes = partition_into_regimes(&global_bounds, &mixed_clauses);
    if regimes.is_empty() {
        return Some(None);
    }

    // The coordinates for a regime with no bound (`solve_regime`, I5.3): `x = c + s * t` where
    // `t` is the alias `s * x_root + d` of least `d` among those of sign `s`, so `c = -s * d`.
    // The aliases of `x_root` are the same atoms under every name, and so are these two.
    let mut least: [Option<Int>; 2] = [None, None];
    for a in &all_atoms {
        let (root, s, d) = uf.get(a);
        let slot = &mut least[usize::from(s < 0)];
        if root == x_root && slot.as_ref().is_none_or(|l| d < *l) {
            *slot = Some(d);
        }
    }
    let [plus, minus] = least;
    let free: Vec<(i8, Int)> = plus
        .map(|d| (1, -&d))
        .into_iter()
        .chain(minus.map(|d| (-1, d)))
        .collect();
    let walked = walk_segments(&regimes, &global_bounds, &free, &unit_mods, &mixed_clauses);
    let undecided = match walked {
        RegimeOut::Found(x_val) => {
            // Complexity tradeoff: constructing every quotient in a Model can
            // write quadratic output bits. For a Boolean answer evaluate only
            // the referenced atoms in a visited DAG fold, with linear temporary
            // space. Repeated atoms still pay their arithmetic cost. Tests:
            // one_variable_modular_formulas_match_enumeration, pncx_random.
            if !want_model {
                let witness = ScalarWitness {
                    x_root: &x_root,
                    x_val: &x_val,
                    fixed: &fixed,
                    uf: &uf,
                    rem_defs: &rem_defs,
                    global_quots: &global_quots,
                    local_windows: &local_windows,
                };
                return ScalarWitness::holds(&witness, f).then(|| Some(Model::new()));
            }
            let model = build_model(
                &x_root,
                &x_val,
                &all_atoms,
                &fixed,
                &uf,
                &rem_defs,
                &global_quots,
                &local_windows,
            );
            if !f.holds_as(&model) {
                return None;
            }
            return Some(Some(if want_model { model } else { Model::new() }));
        }
        RegimeOut::Empty => false,
        RegimeOut::Undecided => true,
    };

    // Complexity tradeoff: naive version, branching over the residues of every base, exponential
    // in the number of bases (a conjunction of clauses of residues under several coprime moduli
    // encodes CNF-SAT, so no exact polynomial method is known for all of them). Used: the CRT
    // fixpoint, hole cutting on segments shorter than a modulus, the forbidden-box share bound
    // with conditional expectations, and one level of single-base splitting, each O(n log n) on
    // one segment. The segments are walked by `walk_segments`, whose cost is bounded there. What
    // is given up: nothing is refused here; a segment these
    // steps leave undecided sends the whole formula to the solver's general path, which then
    // answers, or refuses, as it did before, at its own cost. Tests:
    // `one_scope::easy_clause_systems_over_several_moduli_keep_their_answers`,
    // `one_scope::one_variable_modular_formulas_match_enumeration`,
    // `one_scope::the_questions_of_negated_residues_over_distinct_bounds_scale`.
    if undecided { None } else { Some(None) }
}

/// Solves the segments `segs` (in order along the line, as `partition_into_regimes` gives them)
/// with the unit congruences `unit_mods` and the clauses `clauses`, by a depth-first walk over a
/// segment tree. A clause applies on a segment exactly when its bounds do not hold there, which
/// is a few runs of consecutive segments (found by binary search on the segment starts); each
/// run is attached to the O(log R) tree nodes that cover it, for `R` segments. A node is solved
/// once, on the span from its first segment to its last, with the clauses attached to it and
/// to its ancestors (the path, pushed on entry and popped on exit). Every segment below the node
/// has those clauses and more, on a smaller span, so `Empty` at the node is `Empty` for all of
/// them and the subtree is skipped. A point found at a node is a witness for the formula when it
/// lies in `global_bounds` and satisfies every unit congruence and clause (checked directly, in
/// O(n)); then the walk stops. A leaf is one segment with all the clauses that apply on it, the
/// input the segments were solved with before.
///
/// Complexity tradeoff: the cost is the sum, over the nodes visited, of the clauses on the path
/// to each, plus one O(n) check per node where a point is found. It is O(n log R) per node on a
/// path, and O(n log n) in all when the walk visits O(log R) nodes, as on `regimes3` (the
/// clauses that empty the left segments sit on O(log R) nodes and prune there). It is not
/// bounded below O(R n) in general: a node that is not empty only because constraints are
/// missing that its leaves have (each leaf empty for its own reason) is descended, and a tree in
/// which every such node is descended visits all 2R nodes, each with up to n clauses. What is
/// given up: time only on such inputs (none measured; see R3-CLAUDE-2); the answers are those
/// of the leaves, as before. Stage C (one level of single-base splitting inside
/// `solve_coprime_system`) runs inside each node's solve and keeps no state across nodes, so
/// nothing is undone for it; it costs what one segment's solve costs, at each node visited.
/// Test: `one_scope::the_questions_of_clauses_over_many_segments_scale`.
fn walk_segments(
    segs: &[Span],
    global_bounds: &Domain,
    free: &[(i8, Int)],
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[FlatClause],
) -> RegimeOut {
    let r = segs.len();
    if r == 0 {
        return RegimeOut::Empty;
    }
    // Segment `j` lies inside a piece `(pl, ph)` of a clause's bounds exactly when its start
    // does (the segments are cut at every bound endpoint).
    let first_at_or_after = |pl: &Option<Int>| -> usize {
        match pl {
            None => 0,
            Some(l) => segs.partition_point(|(sl, _)| sl.as_ref().is_none_or(|v| v < l)),
        }
    };
    let past_last_at_or_before = |ph: &Option<Int>| -> usize {
        match ph {
            None => r,
            Some(h) => segs.partition_point(|(sl, _)| sl.as_ref().is_none_or(|v| v <= h)),
        }
    };
    // The tree: node `k` covers `[nodes[k].0, nodes[k].1)`; its children are `nodes[k].2 ..
    // nodes[k].3`. A node of even length is cut in two halves and one of odd length `2h + 1` in
    // `h`, 1 and `h` segments, so that the tree read from the other end is the same tree: a
    // renaming that reverses the sign of the line reverses the segments (I5.3).
    let mut nodes: Vec<(usize, usize, usize, usize)> = vec![(0, r, 0, 0)];
    let mut k = 0;
    while k < nodes.len() {
        let (lo, hi, _, _) = nodes[k];
        let (n, first) = (hi - lo, nodes.len());
        let h = n / 2;
        if n > 1 && n % 2 == 0 {
            nodes.extend([(lo, lo + h, 0, 0), (lo + h, hi, 0, 0)]);
        } else if n > 1 {
            nodes.extend([
                (lo, lo + h, 0, 0),
                (lo + h, lo + h + 1, 0, 0),
                (lo + h + 1, hi, 0, 0),
            ]);
        }
        (nodes[k].2, nodes[k].3) = (first, nodes.len());
        k += 1;
    }
    let mut lists: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    for (ci, cl) in clauses.iter().enumerate() {
        let mut start = 0;
        let mut runs: Vec<(usize, usize)> = Vec::new();
        for (pl, ph) in &cl.bounds.pieces {
            let (a, b) = (first_at_or_after(pl), past_last_at_or_before(ph));
            if a < b {
                if start < a {
                    runs.push((start, a));
                }
                start = start.max(b);
            }
        }
        if start < r {
            runs.push((start, r));
        }
        for (a, b) in runs {
            let mut stack = vec![0usize];
            while let Some(k) = stack.pop() {
                let (lo, hi, c0, c1) = nodes[k];
                if b <= lo || hi <= a {
                    continue;
                }
                if a <= lo && hi <= b {
                    lists[k].push(ci);
                    continue;
                }
                stack.extend(c0..c1);
            }
        }
    }

    let holds_everywhere = |x: &Int| -> bool {
        let at = Some(x.clone());
        global_bounds.contains_span(&at, &at)
            && unit_mods
                .iter()
                .all(|(m, s)| res_contains(s, &x.mod_floor_wide(m)))
            && clauses.iter().all(|cl| {
                (!cl.bounds.is_empty() && cl.bounds.contains_span(&at, &at))
                    || cl
                        .mods
                        .iter()
                        .any(|(m, s)| res_contains(s, &x.mod_floor_wide(m)))
            })
    };

    enum Step {
        Enter(usize),
        Exit,
    }
    let mut path: Vec<usize> = Vec::new();
    let mut todo = vec![Step::Enter(0)];
    let mut undecided = false;
    while let Some(step) = todo.pop() {
        let k = match step {
            Step::Exit => {
                path.pop();
                continue;
            }
            Step::Enter(k) => k,
        };
        let (lo, hi, c0, c1) = nodes[k];
        path.push(k);
        // The clauses on the path, as the regime loop built them for one segment.
        let mut units = unit_mods.clone();
        let mut multi: Vec<BTreeMap<Int, ResidueSet>> = Vec::new();
        let mut empty = false;
        'path: for &n in &path {
            for &ci in &lists[n] {
                let cl = &clauses[ci];
                if cl.mods.len() == 1 {
                    let Some((m, s)) = cl.mods.iter().next() else {
                        return RegimeOut::Undecided;
                    };
                    let e = units
                        .entry(m.clone())
                        .or_insert_with(|| vec![(Int::ZERO, m - &Int::ONE)]);
                    *e = res_intersect(e, s);
                    if e.is_empty() {
                        empty = true;
                        break 'path;
                    }
                } else {
                    multi.push(cl.mods.clone());
                }
            }
        }
        let (out, other) = if empty {
            (RegimeOut::Empty, None)
        } else {
            solve_regime(&segs[lo].0, &segs[hi - 1].1, free, units, multi)
        };
        let leaf = hi - lo == 1;
        match out {
            RegimeOut::Empty => {
                path.pop();
                continue;
            }
            // A point of a leaf satisfies all that applies on its segment.
            RegimeOut::Found(x) if leaf || holds_everywhere(&x) => return RegimeOut::Found(x),
            // The point of the other writing, where the regime reads the same from both ends
            // (`solve_regime`): which of the two comes first depends on the names.
            RegimeOut::Found(_) if other.as_ref().is_some_and(holds_everywhere) => {
                return other.map_or(RegimeOut::Undecided, RegimeOut::Found);
            }
            RegimeOut::Undecided if leaf => {
                undecided = true;
                path.pop();
                continue;
            }
            // A point found at an inner node that is not a witness, or an inner node left
            // undecided: its children are solved.
            _ => {}
        }
        todo.push(Step::Exit);
        todo.extend((c0..c1).rev().map(Step::Enter));
    }
    if undecided {
        RegimeOut::Undecided
    } else {
        RegimeOut::Empty
    }
}

#[allow(clippy::too_many_arguments)]
fn fold_leaf(
    c: &Con,
    negated: bool,
    x_root: &Atom,
    fixed: &HashMap<Atom, Int>,
    uf: &UnitUf,
    rem_defs: &HashMap<Atom, FullRemDef>,
    global_quots: &HashMap<Atom, GlobalQuot>,
    local_windows: &mut HashMap<Atom, Vec<LocalWindow>>,
) -> Result<FoldNode, ()> {
    let lin = rewrite_lin_full(&c.lin, fixed, uf, rem_defs);
    if lin.terms.is_empty() {
        let holds = match c.rel {
            Rel::Ge => !lin.constant.is_negative(),
            Rel::Eq => lin.constant.is_zero(),
        };
        let holds = holds != negated;
        return Ok(FoldNode::from_clause(if holds {
            FlatClause::verum()
        } else {
            FlatClause::falsum()
        }));
    }

    if lin.terms.len() == 1 {
        let Some((a, k)) = lin.terms.iter().next() else {
            return Err(());
        };
        if a == x_root {
            let dom = bound_domain_1d(k, &lin.constant, c.rel, negated);
            return Ok(FoldNode::from_clause(FlatClause {
                bounds: dom,
                mods: BTreeMap::new(),
            }));
        }
        // Pure constraint on a global quotient `q`: `k * q + constant >= 0` or `== 0`.
        let gq = global_quots.get(a).ok_or(())?;
        // `sigma_q * q = div_floor(s_x * x + c_lo, m)`.
        // So `q = sigma_q * div_floor(s_x * x + c_lo, m)`.
        let k_eff = if gq.sigma_q > 0 { k.clone() } else { -k };
        let q_dom = bound_domain_1d(&k_eff, &lin.constant, c.rel, negated);
        // Map each interval `[ql, qh]` of `div_floor(s_x * x + c_lo, m)` to `x`:
        // `ql <= floor((s_x * x + c_lo) / m) <= qh` <=> `m * ql <= s_x * x + c_lo <= m * qh + m - 1`.
        let mut x_pieces = Vec::new();
        for (ql, qh) in q_dom.pieces {
            let s_lo = ql.map(|l| &(&gq.m * &l) - &gq.c_lo);
            let s_hi = qh.map(|h| &(&(&gq.m * &h) + &(&gq.m - &Int::ONE)) - &gq.c_lo);
            if gq.s_x > 0 {
                x_pieces.push((s_lo, s_hi));
            } else {
                x_pieces.push((s_hi.map(|h| -&h), s_lo.map(|l| -&l)));
            }
        }
        return Ok(FoldNode::from_clause(FlatClause {
            bounds: Domain::from_pieces(x_pieces),
            mods: BTreeMap::new(),
        }));
    }

    if lin.terms.len() == 2 {
        let c_x = lin.terms.get(x_root).ok_or(())?;
        if !c_x.is_unit() {
            return Err(());
        }
        let Some((q_root, c_q)) = lin.terms.iter().find(|(a, _)| *a != x_root) else {
            return Err(());
        };
        let m = c_q.abs();
        if m < Int::from(2) {
            return Err(());
        }

        if let Some(gq) = global_quots.get(q_root) {
            if gq.m != m {
                return Err(());
            }
            // Check that `c_x * x + c_q * q + constant` is a function of
            // `rem = (gq.s_x * x + gq.c_lo) - gq.sigma_q * m * q`:
            // `t * rem + k_rem`, where `c_x = t * gq.s_x` and `c_q = -t * gq.sigma_q * m`.
            let t = if gq.s_x > 0 { c_x.clone() } else { -c_x };
            let expected_cq = if (-gq.sigma_q) > 0 {
                &t * &m
            } else {
                -&(&t * &m)
            };
            if *c_q != expected_cq {
                return Err(());
            }
            let k_rem = &lin.constant - &(&t * &gq.c_lo);
            let rem_dom = bound_domain_1d(&t, &k_rem, c.rel, negated);
            let full_rem = Domain::range(Int::ZERO, gq.w.clone());
            let valid_rem = rem_dom.intersect(&full_rem);
            if valid_rem.is_empty() {
                return Ok(FoldNode::from_clause(FlatClause::falsum()));
            }
            if valid_rem == full_rem {
                return Ok(FoldNode::from_clause(FlatClause::verum()));
            }
            let mut s_all = Vec::new();
            for (rl, rh) in valid_rem.pieces {
                let a = rl.unwrap_or(Int::ZERO);
                let b = rh.unwrap_or_else(|| gq.w.clone());
                s_all.extend(shift_residue_interval(&a, &b, gq.s_x, &gq.c_lo, &m));
            }
            let norm = res_normalize(s_all, &m);
            if norm.is_empty() {
                return Ok(FoldNode::from_clause(FlatClause::falsum()));
            }
            if res_is_full(&norm, &m) {
                return Ok(FoldNode::from_clause(FlatClause::verum()));
            }
            let mut mods = BTreeMap::new();
            mods.insert(m, norm);
            return Ok(FoldNode::from_clause(FlatClause {
                bounds: Domain::empty(),
                mods,
            }));
        }

        // Otherwise `q_root` is a local existential quotient!
        if negated {
            return Err(());
        }
        // Orient with `s_x = 1`: `E = x - sigma_q * m * q` where `c_x * x + c_q * q = c_x * E`.
        let sx: i8 = 1;
        let sq: i8 = if c_x.is_positive() == c_q.is_negative() {
            1
        } else {
            -1
        };
        let t: i8 = if c_x.is_positive() { 1 } else { -1 };
        match c.rel {
            Rel::Eq => {
                // `t * E + constant == 0`  <=>  `E = -t * constant`.
                let v = if t > 0 {
                    -&lin.constant
                } else {
                    lin.constant.clone()
                };
                let c_lo = -&v;
                local_windows
                    .entry(q_root.clone())
                    .or_default()
                    .push(LocalWindow {
                        s_x: sx,
                        c_lo: c_lo.clone(),
                        sigma_q: sq,
                        m: m.clone(),
                        w: Int::ZERO,
                    });
                let norm = shift_residue_interval(&Int::ZERO, &Int::ZERO, sx, &c_lo, &m);
                let mut mods = BTreeMap::new();
                mods.insert(m, norm);
                let mut local_quots = BTreeSet::new();
                local_quots.insert(q_root.clone());
                return Ok(FoldNode {
                    clauses: vec![FlatClause {
                        bounds: Domain::empty(),
                        mods,
                    }],
                    half_wins: Vec::new(),
                    local_quots,
                });
            }
            Rel::Ge => {
                let (lo, hi) = if t > 0 {
                    (Some(-&lin.constant), None)
                } else {
                    (None, Some(lin.constant.clone()))
                };
                return Ok(FoldNode {
                    clauses: Vec::new(),
                    half_wins: vec![HalfWin {
                        q_root: q_root.clone(),
                        s_x: sx,
                        sigma_q: sq,
                        m,
                        lo,
                        hi,
                    }],
                    local_quots: BTreeSet::new(),
                });
            }
        }
    }

    Err(())
}

/// Domain of integers `z` satisfying `k * z + c [>= or ==] 0` (negated if `negated`).
fn bound_domain_1d(k: &Int, c: &Int, rel: Rel, negated: bool) -> Domain {
    let d = k.abs();
    let base = match rel {
        Rel::Ge if k.is_positive() => Domain::ge(-&c.div_floor_wide(&d)),
        Rel::Ge => Domain::le(c.div_floor_wide(&d)),
        Rel::Eq => {
            if !c.mod_floor_wide(&d).is_zero() {
                Domain::empty()
            } else {
                let v = if k.is_positive() {
                    (-c).div_floor_wide(&d)
                } else {
                    c.div_floor_wide(&d)
                };
                Domain::single(v)
            }
        }
    };
    if negated { base.complement() } else { base }
}

fn fold_and(
    nodes: Vec<FoldNode>,
    local_windows: &mut HashMap<Atom, Vec<LocalWindow>>,
) -> Result<FoldNode, ()> {
    let mut clauses = Vec::new();
    let mut by_q: BTreeMap<Atom, HalfWin> = BTreeMap::new();
    let mut local_quots: BTreeSet<Atom> = BTreeSet::new();

    for node in nodes {
        for q in node.local_quots {
            if !local_quots.insert(q) {
                return Err(());
            }
        }
        clauses.extend(node.clauses);
        for hw in node.half_wins {
            if local_quots.contains(&hw.q_root) {
                return Err(());
            }
            match by_q.get_mut(&hw.q_root) {
                Some(existing) => {
                    if existing.s_x != hw.s_x
                        || existing.sigma_q != hw.sigma_q
                        || existing.m != hw.m
                    {
                        return Err(());
                    }
                    existing.lo = max_lo(existing.lo.take(), hw.lo);
                    existing.hi = min_hi(existing.hi.take(), hw.hi);
                }
                None => {
                    by_q.insert(hw.q_root.clone(), hw);
                }
            }
        }
    }

    let mut remaining_half = Vec::new();
    for (q_root, hw) in by_q {
        match (hw.lo, hw.hi) {
            (Some(lo), Some(hi)) => {
                if !local_quots.insert(q_root.clone()) {
                    return Err(());
                }
                if lo > hi {
                    clauses.push(FlatClause::falsum());
                    continue;
                }
                let w = &hi - &lo;
                if w >= &hw.m - &Int::ONE {
                    continue;
                }
                let c_lo = -&lo;
                local_windows.entry(q_root).or_default().push(LocalWindow {
                    s_x: hw.s_x,
                    c_lo: c_lo.clone(),
                    sigma_q: hw.sigma_q,
                    m: hw.m.clone(),
                    w: w.clone(),
                });
                let norm = shift_residue_interval(&Int::ZERO, &w, hw.s_x, &c_lo, &hw.m);
                let mut mods = BTreeMap::new();
                mods.insert(hw.m, norm);
                clauses.push(FlatClause {
                    bounds: Domain::empty(),
                    mods,
                });
            }
            (lo, hi) => {
                remaining_half.push(HalfWin {
                    q_root,
                    s_x: hw.s_x,
                    sigma_q: hw.sigma_q,
                    m: hw.m,
                    lo,
                    hi,
                });
            }
        }
    }

    // Simplify clauses: if any clause is falsum, collapse to `[falsum]`.
    // Also merge pure bound clauses in the conjunction so `And` inside `Or` (like `d || (r && !d)`)
    // stays compact.
    // Complexity tradeoff: intersecting one growing interval list per clause
    // can copy O(s^2) pieces for s separate holes. Group bounds and residues
    // and intersect balanced halves, O(s log s) interval operations. Nothing
    // is given up. Tests: pncx_pure_bounds_scale and pncx_pure_residues_scale;
    // both fail with the accumulated-list implementation.
    let mut bound_inputs = Vec::new();
    let mut pure_mods: BTreeMap<Int, Vec<ResidueSet>> = BTreeMap::new();
    let mut other_clauses = Vec::new();
    for cl in clauses {
        if cl.is_true() {
            continue;
        }
        if cl.is_false() {
            return Ok(FoldNode {
                clauses: vec![FlatClause::falsum()],
                half_wins: Vec::new(),
                local_quots,
            });
        }
        if cl.mods.is_empty() {
            bound_inputs.push(cl.bounds);
        } else if cl.bounds.is_empty() && cl.mods.len() == 1 {
            let Some((m, s)) = cl.mods.into_iter().next() else {
                return Err(());
            };
            pure_mods.entry(m).or_default().push(s);
        } else {
            other_clauses.push(cl);
        }
    }

    let pure_bounds = intersect_domains(bound_inputs);
    if pure_bounds.is_empty() {
        return Ok(FoldNode {
            clauses: vec![FlatClause::falsum()],
            half_wins: Vec::new(),
            local_quots,
        });
    }
    let mut out_clauses = Vec::with_capacity(other_clauses.len() + pure_mods.len() + 1);
    if !pure_bounds.is_all() {
        out_clauses.push(FlatClause {
            bounds: pure_bounds,
            mods: BTreeMap::new(),
        });
    }
    for (m, sets) in pure_mods {
        let s = intersect_residue_sets(sets);
        if s.is_empty() {
            return Ok(FoldNode {
                clauses: vec![FlatClause::falsum()],
                half_wins: Vec::new(),
                local_quots,
            });
        }
        if !res_is_full(&s, &m) {
            let mut mods = BTreeMap::new();
            mods.insert(m, s);
            out_clauses.push(FlatClause {
                bounds: Domain::empty(),
                mods,
            });
        }
    }
    out_clauses.extend(other_clauses);

    Ok(FoldNode {
        clauses: out_clauses,
        half_wins: remaining_half,
        local_quots,
    })
}

fn fold_or(nodes: Vec<FoldNode>) -> Result<FoldNode, ()> {
    let mut local_quots: BTreeSet<Atom> = BTreeSet::new();
    let mut current: Vec<FlatClause> = vec![FlatClause::falsum()];

    // A disjunction of two or more parts of which one is a conjunction of two or more clauses
    // would multiply out, 2^k clauses for k such parts, and copy the other parts into each; it
    // is left to the general path (the Complexity tradeoff comment at the end of
    // `solve_modular`), so each disjunction folds to one clause, in the size of its parts.
    let live = |n: &FoldNode| !(n.clauses.len() == 1 && n.clauses[0].is_false());
    if nodes.iter().filter(|n| live(n)).count() > 1
        && nodes.iter().any(|n| live(n) && n.clauses.len() > 1)
    {
        return Err(());
    }

    // With two or more live parts, each is one clause, and their disjunction is one clause: the
    // bound pieces of all the parts, and for each modulus the residue intervals of all the parts,
    // each normalized once (sort and merge), O(k log k) for `k` pieces and intervals in all. The
    // clause is the same as joining the parts one at a time with `FlatClause::or`, which copies
    // the clause built so far at each part, O(k^2).
    let true_node = |local_quots| {
        Ok(FoldNode {
            clauses: Vec::new(),
            half_wins: Vec::new(),
            local_quots,
        })
    };
    let mut pieces: Vec<Span> = Vec::new();
    let mut per_mod: BTreeMap<Int, Vec<(Int, Int)>> = BTreeMap::new();
    let mut any_single = false;
    let mut multi: Option<Vec<FlatClause>> = None;
    for node in nodes {
        if !node.half_wins.is_empty() {
            return Err(());
        }
        local_quots.extend(node.local_quots);
        if node.clauses.is_empty() {
            // Empty conjunction = true; `Or` with `true` is `true`.
            return true_node(local_quots);
        }
        if node.clauses.len() == 1 && node.clauses[0].is_false() {
            continue;
        }
        if node.clauses.len() == 1 {
            let Some(c) = node.clauses.into_iter().next() else {
                return Err(());
            };
            if c.is_true() {
                return true_node(local_quots);
            }
            pieces.extend(c.bounds.pieces);
            for (m, s) in c.mods {
                per_mod.entry(m).or_default().extend(s);
            }
            any_single = true;
        } else {
            // The only live part (the test above).
            multi = Some(node.clauses);
        }
    }
    if let Some(cls) = multi {
        let mut next: Vec<FlatClause> = Vec::with_capacity(cls.len());
        for c2 in &cls {
            let comb = current[0].or(c2);
            if !comb.is_true() {
                next.push(comb);
            }
        }
        next.sort();
        next.dedup();
        current = next;
    } else if any_single {
        let bounds = Domain::from_pieces(pieces);
        if bounds.is_all() {
            return true_node(local_quots);
        }
        let mut mods = BTreeMap::new();
        for (m, raw) in per_mod {
            let u = res_normalize(raw, &m);
            if res_is_full(&u, &m) {
                return true_node(local_quots);
            }
            mods.insert(m, u);
        }
        current = vec![FlatClause { bounds, mods }];
    }

    Ok(FoldNode {
        clauses: current,
        half_wins: Vec::new(),
        local_quots,
    })
}

/// Partitions `global_bounds` by all finite bound endpoints of `clauses` into elementary closed
/// intervals `Span` on which every `cl.bounds` is constant.
fn partition_into_regimes(global_bounds: &Domain, clauses: &[FlatClause]) -> Vec<Span> {
    if global_bounds.is_empty() {
        return Vec::new();
    }
    // Collect cut points: if a clause bound piece starts at `l`, cut before `l` (`l - 1` and `l`);
    // if it ends at `h`, cut after `h` (`h` and `h + 1`).
    let mut cuts: Vec<Int> = Vec::new();
    for cl in clauses {
        for (lo, hi) in &cl.bounds.pieces {
            if let Some(l) = lo {
                cuts.push(l.clone());
            }
            if let Some(h) = hi {
                cuts.push(h + &Int::ONE);
            }
        }
    }
    cuts.sort();
    cuts.dedup();

    let mut out = Vec::new();
    // Complexity tradeoff: scanning every cut for every disjoint global span
    // costs O(g c). Binary searches select only the cuts inside each span,
    // O(g log c + c) comparisons in total; disjoint spans cannot share a cut.
    // Nothing is given up. Test: r4_tests::pncx_bound_partition_scale.
    for (g_lo, g_hi) in &global_bounds.pieces {
        let mut cur_lo = g_lo.clone();
        let start = g_lo
            .as_ref()
            .map_or(0, |l| cuts.partition_point(|c| c <= l));
        let end = g_hi
            .as_ref()
            .map_or(cuts.len(), |h| cuts.partition_point(|c| c <= h));
        for c in &cuts[start..end] {
            let after_start = match &cur_lo {
                None => true,
                Some(l) => *c > *l,
            };
            let before_end = match g_hi {
                None => true,
                Some(h) => *c <= *h,
            };
            if after_start && before_end {
                out.push((cur_lo, Some(c - &Int::ONE)));
                cur_lo = Some(c.clone());
            }
        }
        let valid = match (&cur_lo, g_hi) {
            (Some(l), Some(h)) => l <= h,
            _ => true,
        };
        if valid {
            out.push((cur_lo, g_hi.clone()));
        }
    }
    out
}

enum RegimeOut {
    Found(Int),
    Empty,
    Undecided,
}

/// A segment still to be solved: its bounds, unit congruences and multi-modulus clauses.
type RegimeTask = (
    Option<Int>,
    Option<Int>,
    BTreeMap<Int, ResidueSet>,
    Vec<BTreeMap<Int, ResidueSet>>,
);

/// Solves a single bound-homogeneous regime `[lo, hi]` with unit congruences `unit_mods` and
/// multi-modulus clauses `clauses`. Cutting a short segment by the holes of its large moduli
/// makes smaller segments; they go on an explicit stack, not into recursive calls, since the
/// nesting can be as deep as the number of distinct moduli. The stack is taken from the top in
/// the order the segments lie on the line, as the recursion did.
///
/// The regime is first written in the coordinate `t = x - lo` or `t = hi - x`, so that `t >= 0`
/// and the residue sets are read from a bound: the line `x` is the coordinate of the root of
/// the affine union-find, which the names choose, and another name shifts it or reverses its
/// sign (I4.15). The steps below choose by the residue sets as they lie on `[0, m)` (which run
/// is split off first, whether a set is a single run, which residues `map_affine_mod` maps), so
/// in the coordinate `x` the same formula was answered under one name and refused under
/// another (R5-CLAUDE-1; cases 974, 3205 and 4949 of
/// `one_scope::one_variable_answers_do_not_depend_on_names`). In `t` a shift of `x` changes
/// nothing, and a sign reversal swaps the two writings; with both bounds the smaller writing is
/// used, so both names give the same one. With one bound there is one writing, the same under
/// every name. With no bound the regime is written in the coordinate of one of `free`, the
/// writings `x = c + s * t` that make `t` the least alias of `x` of each sign (built by
/// `solve_modular_whole`), and the smaller is used (I5.3): a renaming moves the root within the
/// aliases of `x` but leaves the aliases themselves, so it leaves `free` the same set of
/// coordinates.
///
/// The second value is the point the other writing gives, where two writings are equal: the
/// regime then reads the same from both ends, and which of its two mirror points is returned
/// depends on the names. `walk_segments` tries both where it checks a point against the whole
/// formula.
// Complexity tradeoff: naive version, the regime solved in `x`, whose answers depended on the
// names. Used: each residue interval is rewritten once or twice, at most two pieces each, and
// the two writings compared, O(r) integer operations for `r` intervals in all, against the
// solve that follows. What is given up: nothing that was answered under every name; a regime
// answered under one name only is now answered or refused under all. A regime with no bound is
// still solved in a coordinate that moves when `x` itself is shifted in the formula (the
// numbers change, not the names), so such a shift can change a refusal into an answer. Tests:
// `one_scope::one_variable_answers_do_not_depend_on_names`,
// the eight `one_scope::one_variable_answers_with_*_do_not_depend_on_names_*` tests.
fn solve_regime(
    lo: &Option<Int>,
    hi: &Option<Int>,
    free: &[(i8, Int)],
    unit_mods: BTreeMap<Int, ResidueSet>,
    clauses: Vec<BTreeMap<Int, ResidueSet>>,
) -> (RegimeOut, Option<Int>) {
    // `x = c + s * t`.
    let rewrite = |s: i8, c: &Int| -> (BTreeMap<Int, ResidueSet>, Vec<BTreeMap<Int, ResidueSet>>) {
        let set = |m: &Int, r: &ResidueSet| -> ResidueSet {
            let mut raw = Vec::with_capacity(2 * r.len());
            for (a, b) in r {
                raw.extend(shift_residue_interval(a, b, s, c, m));
            }
            res_normalize(raw, m)
        };
        let units = unit_mods
            .iter()
            .map(|(m, r)| (m.clone(), set(m, r)))
            .collect();
        let mut cls: Vec<BTreeMap<Int, ResidueSet>> = clauses
            .iter()
            .map(|cl| cl.iter().map(|(m, r)| (m.clone(), set(m, r))).collect())
            .collect();
        cls.sort();
        (units, cls)
    };
    let mut writings: Vec<(i8, Int)> = Vec::with_capacity(2);
    if let Some(l) = lo {
        writings.push((1, l.clone()));
    }
    if let Some(h) = hi {
        writings.push((-1, h.clone()));
    }
    if writings.is_empty() {
        writings.extend(free.iter().cloned());
    }
    let mut written: Vec<_> = writings
        .into_iter()
        .map(|(s, c)| (rewrite(s, &c), c, s))
        .collect();
    // Stable: on a tie the first writing (from `lo`, or the one of positive sign) is used, as
    // before.
    written.sort_by(|a, b| a.0.cmp(&b.0));
    let other = (written.len() > 1 && written[0].0 == written[1].0)
        .then(|| (written[1].1.clone(), written[1].2));
    let Some(((units, cls), c, s)) = written.into_iter().next() else {
        return (solve_regime_in(lo, hi, unit_mods, clauses), None);
    };
    let at = |c: &Int, s: i8, t: &Int| if s > 0 { c + t } else { c - t };
    let (t_lo, t_hi) = match (lo, hi) {
        (None, None) => (None, None),
        (Some(l), Some(h)) => (Some(Int::ZERO), Some(h - l)),
        _ => (Some(Int::ZERO), None),
    };
    match solve_regime_in(&t_lo, &t_hi, units, cls) {
        RegimeOut::Found(t) => {
            let alt = other.map(|(c2, s2)| at(&c2, s2, &t));
            (RegimeOut::Found(at(&c, s, &t)), alt)
        }
        out => (out, None),
    }
}

/// [`solve_regime`] in the coordinate it was given.
fn solve_regime_in(
    lo: &Option<Int>,
    hi: &Option<Int>,
    unit_mods: BTreeMap<Int, ResidueSet>,
    clauses: Vec<BTreeMap<Int, ResidueSet>>,
) -> RegimeOut {
    let mut stack: Vec<RegimeTask> = vec![(lo.clone(), hi.clone(), unit_mods, clauses)];
    let mut undecided = false;
    while let Some((l, h, u, c)) = stack.pop() {
        match solve_regime_step(&l, &h, u, c, &mut stack) {
            RegimeOut::Found(x) => return RegimeOut::Found(x),
            RegimeOut::Empty => {}
            RegimeOut::Undecided => undecided = true,
        }
    }
    if undecided {
        RegimeOut::Undecided
    } else {
        RegimeOut::Empty
    }
}

/// One segment of `solve_regime`. A short segment pushes its parts on `stack` and returns
/// `Empty` for itself.
fn solve_regime_step(
    lo: &Option<Int>,
    hi: &Option<Int>,
    unit_mods: BTreeMap<Int, ResidueSet>,
    clauses: Vec<BTreeMap<Int, ResidueSet>>,
    stack: &mut Vec<RegimeTask>,
) -> RegimeOut {
    // Check if `[lo, hi]` is already a single point.
    if let (Some(l), Some(h)) = (lo, hi) {
        if l > h {
            return RegimeOut::Empty;
        }
        if l == h {
            return if holds_modular_point(l, &unit_mods, &clauses) {
                RegimeOut::Found(l.clone())
            } else {
                RegimeOut::Empty
            };
        }
    }

    // No witness here may use a fixed point of the line such as x = 1: the line is the
    // coordinate of the root of the affine union-find, which the names choose, so a fixed point
    // means a different value of the program's variables under another name (I4.15). The
    // witnesses below are placed by the bounds, which move with the coordinate: shifting x by d
    // shifts them by d, and reversing its sign swaps the lower and the upper one.
    //
    // Complexity tradeoff: repeated advancement to the next permitted integer
    // can enumerate a period exponential in its written bits. Compute only the
    // necessary lower bound from each written constraint, O(n log n) interval
    // comparisons, and check that one point; likewise the necessary upper bound from `hi`.
    // Failure gives no verdict and the
    // existing exact steps continue. Tests: pncx_lower_witness_scale and the
    // bounded enumeration tests; `names::answers_do_not_depend_on_the_names_of_aliases`.
    if let Some(l) = lo
        && let Some(x) = lower_witness(l, hi, &unit_mods, &clauses)
    {
        return RegimeOut::Found(x);
    }
    if let Some(h) = hi
        && let Some(x) = upper_witness(lo, h, &unit_mods, &clauses)
    {
        return RegimeOut::Found(x);
    }

    if let Some(x) = separate_pair_witness(lo, hi, &unit_mods, &clauses) {
        return RegimeOut::Found(x);
    }

    // If `[lo, hi]` is finite and any modulus `m > hi - lo`, cut `[lo, hi]` by concrete holes in
    // `x`-space first.
    if let (Some(l), Some(h)) = (lo, hi) {
        let width = h - l;
        let has_large_unit = unit_mods.keys().any(|m| *m > width);
        let has_large_clause = clauses.iter().any(|cl| cl.keys().any(|m| *m > width));
        if has_large_unit || has_large_clause {
            return solve_short_x_interval(l, h, &unit_mods, &clauses, &width, stack);
        }
    }

    // Build the pairwise coprime base of all moduli appearing in `unit_mods` and `clauses`.
    let mut all_moduli: BTreeSet<Int> = unit_mods.keys().cloned().collect();
    for cl in &clauses {
        for m in cl.keys() {
            all_moduli.insert(m.clone());
        }
    }
    if all_moduli.is_empty() {
        return pick_in_span(lo, hi, &Int::ZERO, &Int::ONE)
            .map_or(RegimeOut::Empty, RegimeOut::Found);
    }

    // The coprime base of this segment's moduli, in increasing order. It is computed for each
    // segment and not once for the formula: a base common to all the formula's moduli can split a
    // modulus (12 into 3 and 4 when 4 is a modulus elsewhere) that this segment's own base keeps
    // whole, and a residue range over a split modulus is left to the general path
    // (`literal_to_base_cnf`); with one base for the formula, 76 of the 5,000 formulas of
    // `one_scope::one_variable_modular_formulas_match_enumeration` were refused, against 69.
    // `max_q[i]` is the largest power `bases[i]^E` that divides one of the moduli.
    let Some(mod_base) = coprime_factorization(&all_moduli) else {
        return RegimeOut::Undecided;
    };
    let mut used: BTreeSet<&Int> = BTreeSet::new();
    for fs in mod_base.values() {
        used.extend(fs.iter().map(|(b, _)| b));
    }
    let bases: Vec<Int> = used.into_iter().cloned().collect();
    let index: BTreeMap<&Int, usize> = bases.iter().enumerate().map(|(i, b)| (b, i)).collect();
    let mut max_q: Vec<Int> = bases.clone();
    let mut mod_factors: BTreeMap<Int, Vec<(usize, Int)>> = BTreeMap::new();
    for m in &all_moduli {
        let mut facs: Vec<(usize, Int)> = mod_base[m]
            .iter()
            .map(|(b, q)| (index[b], q.clone()))
            .collect();
        facs.sort();
        for (i, q) in &facs {
            if *q > max_q[*i] {
                max_q[*i] = q.clone();
            }
        }
        mod_factors.insert(m.clone(), facs);
    }

    // Decompose unit congruences and clauses onto the coprime bases `0..bases.len()`.
    let num_bases = bases.len();
    // Per base `i`: constraints at each power `q` of `bases[i]`: `BTreeMap<Int, ResidueSet>`.
    let mut base_powers: Vec<BTreeMap<Int, ResidueSet>> = vec![BTreeMap::new(); num_bases];
    for (i, q_max) in max_q.iter().enumerate() {
        base_powers[i].insert(q_max.clone(), vec![(Int::ZERO, q_max - &Int::ONE)]);
    }

    let mut norm_clauses: Vec<BTreeMap<usize, ResidueSet>> = Vec::new();
    let mut deferred_units: Vec<(&Int, &ResidueSet)> = Vec::new();

    for (m, s) in &unit_mods {
        let facs = &mod_factors[m];
        if facs.len() == 1 {
            let (i, _) = facs[0];
            let e = base_powers[i]
                .entry(m.clone())
                .or_insert_with(|| vec![(Int::ZERO, m - &Int::ONE)]);
            *e = res_intersect(e, s);
            if e.is_empty() {
                return RegimeOut::Empty;
            }
        } else if s.len() == 1 && s[0].0 == s[0].1 {
            // Single allowed residue `r` modulo composite `m`: exact CRT split!
            let r = &s[0].0;
            for (i, q) in facs {
                let rq = r.mod_floor_wide(q);
                let e = base_powers[*i]
                    .entry(q.clone())
                    .or_insert_with(|| vec![(Int::ZERO, q - &Int::ONE)]);
                *e = res_intersect(e, &[(rq.clone(), rq)]);
                if e.is_empty() {
                    return RegimeOut::Empty;
                }
            }
        } else {
            for (i, q) in facs {
                let mut raw = Vec::with_capacity(s.len() * 2);
                for (a, b) in s {
                    raw.extend(shift_residue_interval(a, b, 1, &Int::ZERO, q));
                }
                let proj_q = res_normalize(raw, q);
                let e = base_powers[*i]
                    .entry(q.clone())
                    .or_insert_with(|| vec![(Int::ZERO, q - &Int::ONE)]);
                *e = res_intersect(e, &proj_q);
                if e.is_empty() {
                    return RegimeOut::Empty;
                }
            }
            deferred_units.push((m, s));
        }
    }

    // Consolidate `base_powers[i]` into a `BaseInfo` (with stride `(u, stride)` and reduced
    // modulus `z_max_q = max_q[i] / stride`) and an allowed `ResidueSet` `allowed[i]` in
    // `[0, z_max_q - 1]`.
    let mut bases_info: Vec<BaseInfo> = Vec::with_capacity(num_bases);
    let mut allowed: Vec<ResidueSet> = Vec::with_capacity(num_bases);
    for i in 0..num_bases {
        match consolidate_prime_powers(&base_powers[i], &max_q[i]) {
            ConsolidateOut::Ok(info, a_i) => {
                if a_i.is_empty() {
                    return RegimeOut::Empty;
                }
                bases_info.push(info);
                allowed.push(a_i);
            }
            ConsolidateOut::Empty => return RegimeOut::Empty,
            ConsolidateOut::Undecided => return RegimeOut::Undecided,
        }
    }

    for (m, s) in deferred_units {
        let Some(cnf) = literal_to_base_cnf(m, s, &mod_factors[m], &bases_info, &allowed) else {
            return RegimeOut::Undecided;
        };
        for cl in cnf {
            if cl.len() == 1 {
                let Some((i, s_i)) = cl.into_iter().next() else {
                    return RegimeOut::Undecided;
                };
                allowed[i] = res_intersect(&allowed[i], &s_i);
                if allowed[i].is_empty() {
                    return RegimeOut::Empty;
                }
            } else if !cl.is_empty() {
                norm_clauses.push(cl);
            }
        }
    }

    // Convert `clauses` to `norm_clauses` over `bases_info[i].z_max_q`, distributing `||` over `&&`
    // when a composite modulus literal expands to a conjunction of prime-power clauses.
    for cl in &clauses {
        let mut dist: Vec<BTreeMap<usize, ResidueSet>> = vec![BTreeMap::new()];
        for (m, s) in cl {
            let Some(lit_cnf) = literal_to_base_cnf(m, s, &mod_factors[m], &bases_info, &allowed)
            else {
                return RegimeOut::Undecided;
            };
            // Two literals of one clause that each become a conjunction of two or more clauses
            // over the bases would multiply out; the regime is left to the general path (the
            // Complexity tradeoff comment at the end of `solve_modular`).
            if dist.len() > 1 && lit_cnf.len() > 1 {
                return RegimeOut::Undecided;
            }
            // Complexity tradeoff: the clause built so far is moved into its last product with
            // the literal's clauses and cloned only for the others. A literal giving one clause
            // (the usual case) so costs its own size, not the size of the clause built so far;
            // cloning every time made a clause of n literals cost n^2 (the disj axis, 2.95x per
            // doubling at 4096). Test: `one_scope::a_disjunction_of_many_moduli_scales`.
            let mut next_dist = Vec::with_capacity(dist.len() * lit_cnf.len());
            for c1 in dist {
                let mut c1 = Some(c1);
                for (k, c2) in lit_cnf.iter().enumerate() {
                    let Some(mut merged) = (if k + 1 == lit_cnf.len() {
                        c1.take()
                    } else {
                        c1.clone()
                    }) else {
                        break;
                    };
                    let mut taut = false;
                    for (&i, s2) in c2 {
                        let entry = merged.entry(i).or_default();
                        let u = res_union(entry, s2, &bases_info[i].z_max_q);
                        if u == allowed[i] || res_is_full(&u, &bases_info[i].z_max_q) {
                            taut = true;
                            break;
                        }
                        *entry = u;
                    }
                    if !taut {
                        next_dist.push(merged);
                    }
                }
            }
            dist = next_dist;
            if dist.is_empty() {
                break;
            }
        }
        for c in dist {
            if c.len() == 1 {
                let Some((i, s_i)) = c.into_iter().next() else {
                    return RegimeOut::Undecided;
                };
                allowed[i] = res_intersect(&allowed[i], &s_i);
                if allowed[i].is_empty() {
                    return RegimeOut::Empty;
                }
            } else if !c.is_empty() {
                norm_clauses.push(c);
            }
        }
    }

    solve_coprime_system(lo, hi, &bases_info, allowed, norm_clauses, true)
}

#[derive(Clone, Debug)]
struct BaseInfo {
    max_q: Int,
    u: Int,
    stride: Int,
    z_max_q: Int,
}

impl BaseInfo {
    fn r_from_z(&self, z: &Int) -> Int {
        &self.u + &(&self.stride * z)
    }

    fn z_from_x(&self, x: &Int) -> Option<Int> {
        let r = x.mod_floor_wide(&self.max_q);
        if r.mod_floor_wide(&self.stride) != self.u {
            return None;
        }
        Some((&r - &self.u).div_floor_wide(&self.stride))
    }
}

/// Projects a residue set `s` modulo `q` onto `z in [0, q / stride - 1]` under `r = u + stride * z`.
fn project_stride(s: &[(Int, Int)], u: &Int, stride: &Int) -> ResidueSet {
    if *stride == Int::ONE {
        return s.to_vec();
    }
    let mut out = Vec::with_capacity(s.len());
    let step_m1 = stride - &Int::ONE;
    for (a, b) in s {
        let num_a = &(a - u) + &step_m1;
        let za = num_a.div_floor_wide(stride);
        let zb = (b - u).div_floor_wide(stride);
        if za <= zb {
            out.push((za, zb));
        }
    }
    out
}

/// Projects a single constraint `(x mod q) in s_q` (where `q` is a power of `bases[i]`) onto
/// `z_i in [0, info.z_max_q - 1]` and intersects it with `allowed_i`.
fn project_and_intersect_base(
    s_q: &[(Int, Int)],
    q: &Int,
    info: &BaseInfo,
    allowed_i: &[(Int, Int)],
) -> Option<ResidueSet> {
    if *q <= info.stride {
        let rem = info.u.mod_floor_wide(q);
        return if res_contains(s_q, &rem) {
            Some(allowed_i.to_vec())
        } else {
            Some(Vec::new())
        };
    }
    let q_z = q.div_floor_wide(&info.stride);
    let proj = project_stride(s_q, &info.u, &info.stride);
    if proj.is_empty() {
        return Some(Vec::new());
    }
    intersect_mod_divisor(allowed_i, &proj, &q_z, &info.z_max_q)
}

/// Returns `Some(rq)` if `info` and `allowed_i` fix `x mod q` to a single residue `rq`.
fn single_residue_mod_q(info: &BaseInfo, allowed_i: &[(Int, Int)], q: &Int) -> Option<Int> {
    if *q <= info.stride {
        return Some(info.u.mod_floor_wide(q));
    }
    if allowed_i.is_empty() {
        return None;
    }
    let q_z = q.div_floor_wide(&info.stride);
    let first = &allowed_i.first()?.0;
    let last = &allowed_i.last()?.1;
    if last == first {
        let r = info.r_from_z(first);
        return Some(r.mod_floor_wide(q));
    }
    // Also check if all intervals in `allowed_i` are singletons with the same residue mod `q_z`.
    let z0 = first.mod_floor_wide(&q_z);
    for (a, b) in allowed_i {
        if a != b || a.mod_floor_wide(&q_z) != z0 {
            return None;
        }
    }
    Some((&info.u + &(&info.stride * &z0)).mod_floor_wide(q))
}

/// Maps `y_set` in `[0, q_rem - 1]` under `y -> (u_fixed + m_fixed * y) mod q_rem`.
fn map_affine_mod(
    y_set: &[(Int, Int)],
    m_fixed: &Int,
    u_fixed: &Int,
    q_rem: &Int,
) -> Option<ResidueSet> {
    if y_set.is_empty() {
        return Some(Vec::new());
    }
    if res_is_full(y_set, q_rem) {
        return Some(vec![(Int::ZERO, q_rem - &Int::ONE)]);
    }
    let step = m_fixed.mod_floor_wide(q_rem);
    let shift = u_fixed.mod_floor_wide(q_rem);
    if step == Int::ONE {
        // `shift_residue_interval(a, b, 1, c, m)` is `{y : (y + c) mod m in [a, b]}`, the
        // preimage; the image `[a + shift, b + shift]` is the preimage under `-shift`.
        let back = -&shift;
        let mut raw = Vec::with_capacity(y_set.len() * 2);
        for (a, b) in y_set {
            raw.extend(shift_residue_interval(a, b, 1, &back, q_rem));
        }
        return Some(res_normalize(raw, q_rem));
    }
    if &step + &Int::ONE == *q_rem {
        let mut raw = Vec::with_capacity(y_set.len() * 2);
        for (a, b) in y_set {
            raw.extend(shift_residue_interval(a, b, -1, &shift, q_rem));
        }
        return Some(res_normalize(raw, q_rem));
    }
    // A set, or its complement, of single residues is mapped one residue each; any other set is
    // left to the general path (the Complexity tradeoff comment at the end of `solve_modular`).
    if y_set.iter().all(|(a, b)| a == b) {
        let mut raw = Vec::with_capacity(y_set.len());
        for (a, b) in y_set {
            let mut y = a.clone();
            while &y <= b {
                let r = (&shift + &(&step * &y)).mod_floor_wide(q_rem);
                raw.push((r.clone(), r));
                y = &y + &Int::ONE;
            }
        }
        return Some(res_normalize(raw, q_rem));
    }
    let comp = res_complement(y_set, q_rem);
    if comp.iter().all(|(a, b)| a == b) {
        let mut raw = Vec::with_capacity(comp.len());
        for (a, b) in &comp {
            let mut y = a.clone();
            while &y <= b {
                let r = (&shift + &(&step * &y)).mod_floor_wide(q_rem);
                raw.push((r.clone(), r));
                y = &y + &Int::ONE;
            }
        }
        let norm_comp = res_normalize(raw, q_rem);
        return Some(res_complement(&norm_comp, q_rem));
    }
    None
}

/// Converts a single literal `x mod m in s` into a conjunction of clauses over `bases_info[i]`.
fn literal_to_base_cnf(
    m: &Int,
    s: &ResidueSet,
    facs: &[(usize, Int)],
    bases_info: &[BaseInfo],
    allowed: &[ResidueSet],
) -> Option<Vec<BTreeMap<usize, ResidueSet>>> {
    if facs.len() == 1 {
        let (i, ref q) = facs[0];
        let inter = project_and_intersect_base(s, q, &bases_info[i], &allowed[i])?;
        return Some(vec![BTreeMap::from([(i, inter)])]);
    }
    if s.len() == 1 && s[0].0 == s[0].1 {
        let r = &s[0].0;
        let mut out = Vec::with_capacity(facs.len());
        for &(i, ref q) in facs {
            let rq = r.mod_floor_wide(q);
            let inter =
                project_and_intersect_base(&[(rq.clone(), rq)], q, &bases_info[i], &allowed[i])?;
            out.push(BTreeMap::from([(i, inter)]));
        }
        return Some(out);
    }
    // Check if any prime-power factors `(i, q)` in `facs` are already fixed to a single residue.
    let mut m_fixed = Int::ONE;
    let mut u_fixed = Int::ZERO;
    let mut active_facs: Vec<(usize, Int)> = Vec::with_capacity(facs.len());
    for &(i, ref q) in facs {
        if let Some(rq) = single_residue_mod_q(&bases_info[i], &allowed[i], q) {
            let (u_new, m_new) = combine_crt_pair(&u_fixed, &m_fixed, &rq, q)?;
            u_fixed = u_new;
            m_fixed = m_new;
        } else {
            active_facs.push((i, q.clone()));
        }
    }
    if active_facs.is_empty() {
        return if res_contains(s, &u_fixed) {
            Some(Vec::new())
        } else {
            Some(vec![BTreeMap::new()])
        };
    }
    if active_facs.len() == 1 {
        let (i_rem, ref q_rem) = active_facs[0];
        let y_set = project_stride(s, &u_fixed, &m_fixed);
        let s_rem = map_affine_mod(&y_set, &m_fixed, &u_fixed, q_rem)?;
        let inter = project_and_intersect_base(&s_rem, q_rem, &bases_info[i_rem], &allowed[i_rem])?;
        return Some(vec![BTreeMap::from([(i_rem, inter)])]);
    }

    let comp = res_complement(s, m);
    let comp_reduced = project_stride(&comp, &u_fixed, &m_fixed);
    // One clause per excluded residue: only where each excluded run is a single residue, so the
    // clauses are no more than the runs written; otherwise the general path (the Complexity
    // tradeoff comment at the end of `solve_modular`).
    if !comp_reduced.iter().all(|(a, b)| a == b) {
        return None;
    }
    let mut out = Vec::with_capacity(comp_reduced.len());
    for (za, zb) in comp_reduced {
        let mut z = za;
        while z <= zb {
            let r = &u_fixed + &(&m_fixed * &z);
            let mut cl_r: BTreeMap<usize, ResidueSet> = BTreeMap::new();
            let mut taut = false;
            for &(i, ref q) in &active_facs {
                let rq = r.mod_floor_wide(q);
                let s_q = res_complement(&[(rq.clone(), rq)], q);
                let inter = project_and_intersect_base(&s_q, q, &bases_info[i], &allowed[i])?;
                let entry = cl_r.entry(i).or_default();
                let u = res_union(entry, &inter, &bases_info[i].z_max_q);
                if u == allowed[i] || res_is_full(&u, &bases_info[i].z_max_q) {
                    taut = true;
                    break;
                }
                *entry = u;
            }
            if !taut {
                out.push(cl_r);
            }
            z = &z + &Int::ONE;
        }
    }
    Some(out)
}

/// Solves a short interval `[l, h]` where at least one modulus `m > cut_threshold`, by cutting
/// `[l, h]` at all concrete integer holes of unit congruences with `m > cut_threshold` and at all
/// concrete cut points of clause literals with `m > cut_threshold`.
fn solve_short_x_interval(
    l: &Int,
    h: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
    cut_threshold: &Int,
    stack: &mut Vec<RegimeTask>,
) -> RegimeOut {
    let mut hole_pieces: Vec<Span> = Vec::new();
    let mut small_units = BTreeMap::new();
    for (m, s) in unit_mods {
        if *m > *cut_threshold {
            // Forbidden residue intervals of `x mod m` map to concrete holes in `[l, h]`.
            let comp = res_complement(s, m);
            for (ra, rb) in comp {
                for (hl, hh) in concrete_intervals_in_span(l, h, m, &ra, &rb) {
                    hole_pieces.push((Some(hl), Some(hh)));
                }
            }
        } else {
            small_units.insert(m.clone(), s.clone());
        }
    }

    // Also collect cut points from any clause literal with `m > cut_threshold`.
    let mut clause_domains: Vec<(Domain, BTreeMap<Int, ResidueSet>)> = Vec::new();
    for cl in clauses {
        let mut dom = Domain::empty();
        let mut small_cl = BTreeMap::new();
        for (m, s) in cl {
            if *m > *cut_threshold {
                let mut pieces = Vec::new();
                for (ra, rb) in s {
                    for (il, ih) in concrete_intervals_in_span(l, h, m, ra, rb) {
                        pieces.push((Some(il), Some(ih)));
                    }
                }
                dom = dom.union(&Domain::from_pieces(pieces));
            } else {
                small_cl.insert(m.clone(), s.clone());
            }
        }
        clause_domains.push((dom, small_cl));
    }

    let base_dom = Domain::range(l.clone(), h.clone())
        .intersect(&Domain::from_pieces(hole_pieces).complement());
    if base_dom.is_empty() {
        return RegimeOut::Empty;
    }

    let mut sub_clauses = Vec::new();
    let mut cur_dom = base_dom;
    for (dom, small_cl) in clause_domains {
        if small_cl.is_empty() {
            cur_dom = cur_dom.intersect(&dom);
            if cur_dom.is_empty() {
                return RegimeOut::Empty;
            }
        } else {
            sub_clauses.push(FlatClause {
                bounds: dom,
                mods: small_cl,
            });
        }
    }

    // The sub-regimes go on the caller's explicit stack (no recursion); they are pushed in
    // reverse so that they are solved from left to right.
    let sub_regimes = partition_into_regimes(&cur_dom, &sub_clauses);
    let mut tasks: Vec<RegimeTask> = Vec::new();
    for (sub_lo, sub_hi) in sub_regimes {
        let mut r_units = small_units.clone();
        let mut r_clauses = Vec::new();
        let mut empty = false;
        for cl in &sub_clauses {
            if !cl.bounds.is_empty() && cl.bounds.contains_span(&sub_lo, &sub_hi) {
                continue;
            }
            if cl.mods.len() == 1 {
                let Some((m, s)) = cl.mods.iter().next() else {
                    return RegimeOut::Undecided;
                };
                let e = r_units
                    .entry(m.clone())
                    .or_insert_with(|| vec![(Int::ZERO, m - &Int::ONE)]);
                *e = res_intersect(e, s);
                if e.is_empty() {
                    empty = true;
                    break;
                }
            } else {
                r_clauses.push(cl.mods.clone());
            }
        }
        if empty {
            continue;
        }
        tasks.push((sub_lo, sub_hi, r_units, r_clauses));
    }
    stack.extend(tasks.into_iter().rev());
    RegimeOut::Empty
}

/// Concrete sub-intervals `[il, ih] subseteq [l, h]` where `x mod m in [ra, rb]`.
fn concrete_intervals_in_span(l: &Int, h: &Int, m: &Int, ra: &Int, rb: &Int) -> Vec<(Int, Int)> {
    let q_l = l.div_floor_wide(m);
    let r_l = l.mod_floor_wide(m);
    let q_h = h.div_floor_wide(m);
    let r_h = h.mod_floor_wide(m);
    let mut out = Vec::new();
    let mut q = q_l.clone();
    while q <= q_h {
        let a = if q == q_l { ra.max(&r_l) } else { ra };
        let b = if q == q_h { rb.min(&r_h) } else { rb };
        if a <= b {
            let base = &q * m;
            out.push((&base + a, &base + b));
        }
        q = &q + &Int::ONE;
    }
    out
}

fn holds_modular_point(
    x: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> bool {
    for (m, s) in unit_mods {
        if !res_contains(s, &x.mod_floor_wide(m)) {
            return false;
        }
    }
    for cl in clauses {
        if !cl
            .iter()
            .any(|(m, s)| res_contains(s, &x.mod_floor_wide(m)))
        {
            return false;
        }
    }
    true
}

/// The product tree of `leaves` (nonempty), leaves first: each level holds the products of
/// adjacent pairs of the level below. O(M(N) log k) for `k` leaves of `N` bits in all.
fn product_tree(leaves: Vec<Int>) -> Vec<Vec<Int>> {
    let mut tree: Vec<Vec<Int>> = vec![leaves];
    while let Some(last) = tree.last().filter(|last| last.len() > 1) {
        let next: Vec<Int> = last
            .chunks(2)
            .map(|c| {
                if c.len() == 2 {
                    &c[0] * &c[1]
                } else {
                    c[0].clone()
                }
            })
            .collect();
        tree.push(next);
    }
    tree
}

/// `(P / m) mod m` for each leaf `m` of `tree`, where `P` is the root: the remainder tree takes
/// `P mod v^2` from each node `v` to its children (`v^2` divides the parent's square), and
/// `(P mod m^2) / m` is `(P / m) mod m`. O(M(N) log k).
fn cofactors_mod_leaves(tree: &[Vec<Int>]) -> Vec<Int> {
    let Some((root, levels)) = tree.split_last() else {
        return Vec::new();
    };
    let mut rems = root.clone();
    for level in levels.iter().rev() {
        rems = level
            .iter()
            .enumerate()
            .map(|(j, v)| rems[j / 2].mod_floor_wide(&(v * v)))
            .collect();
    }
    rems.iter()
        .zip(&tree[0])
        .map(|(r, m)| r.div_floor_wide(m))
        .collect()
}

/// Each modulus with its factors `(b, b^e)` over one set of pairwise coprime bases `b`.
type ModBase = BTreeMap<Int, Vec<(Int, Int)>>;

/// Factors every modulus in `moduli` over a pairwise coprime base. A modulus coprime to all the
/// others is its own base; these are found together by one product tree and one remainder tree
/// (`P mod m^2` for the product `P` of all moduli gives `gcd(m, P / m)`), in O(M(N) log k) for
/// `k` moduli of `N` bits in all, where `M` is the cost of multiplying numbers of `N` bits.
///
/// Complexity tradeoff: pairwise refinement and scanning each base per modulus cost
/// O(k^2) arithmetic operations. Bernstein's Algorithms 11.3, 11.4, 13.2,
/// 15.3, 16.2, 17.3, 18.1 and 21.2 use product trees and sparse factor
/// propagation instead, essentially linear in the total bits with fast
/// arithmetic (a polylogarithmic factor, not a proved O(n log n) bound).
/// No modulus or answer is given up. Tests: pncx_common_factors_reconstruct_inputs;
/// pncx_common_factor_scale and pncx_shared_formula_axis are deferred to plan row
/// PERF-negated-chain-unsolved in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
fn coprime_factorization(moduli: &BTreeSet<Int>) -> Option<ModBase> {
    let ms: Vec<Int> = moduli.iter().filter(|m| **m > Int::ONE).cloned().collect();
    // A modulus 1 (if any) has no factors.
    let mut out: ModBase = moduli
        .iter()
        .filter(|m| **m <= Int::ONE)
        .map(|m| (m.clone(), Vec::new()))
        .collect();
    if ms.is_empty() {
        return Some(out);
    }
    if let Some(complete) = common_factorization(&ms) {
        out.extend(complete);
        return Some(out);
    }
    let cof = cofactors_mod_leaves(&product_tree(ms.clone()));

    let mut rest: Vec<Int> = Vec::new();
    for (m, c) in ms.iter().zip(&cof) {
        if m.gcd_recursive(c) == Int::ONE {
            out.insert(m.clone(), vec![(m.clone(), m.clone())]);
        } else {
            rest.push(m.clone());
        }
    }
    let (bases, factors, _) = coprime_base_and_factors(rest)?;
    for (m, fs) in factors {
        out.insert(
            m,
            fs.into_iter().map(|(i, q)| (bases[i].clone(), q)).collect(),
        );
    }
    Some(out)
}

/// A shared factor with independent cofactors needs no base refinement.
// Complexity tradeoff: pairwise refinement is quadratic on g p_i. A running
// gcd, followed by one product/remainder tree on the cofactors, recognizes
// the complete factorization in O(M(B) log k). Failure gives no verdict and
// Bernstein's general method continues. Test: pncx_common_factor_scale, deferred
// to plan row PERF-negated-chain-unsolved in
// wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
fn common_factorization(ms: &[Int]) -> Option<ModBase> {
    let mut g = ms.first()?.clone();
    for m in &ms[1..] {
        g = g.gcd_recursive(m);
        if g == Int::ONE {
            return None;
        }
    }
    let qs: Vec<_> = ms.iter().map(|m| m.div_floor_wide(&g)).collect();
    if qs.iter().any(|q| q.gcd_recursive(&g) != Int::ONE) {
        return None;
    }
    let cof = cofactors_mod_leaves(&product_tree(qs.clone()));
    if !qs
        .iter()
        .zip(&cof)
        .all(|(q, c)| q.gcd_recursive(c) == Int::ONE)
    {
        return None;
    }
    Some(
        ms.iter()
            .cloned()
            .zip(qs)
            .map(|(m, q)| {
                let mut fs = vec![(g.clone(), g.clone())];
                if q > Int::ONE {
                    fs.push((q.clone(), q));
                }
                fs.sort();
                (m, fs)
            })
            .collect(),
    )
}

fn gcd_ppi_ppo(a: &Int, c: &Int) -> (Int, Int, Int) {
    let mut x = a.gcd_recursive(c);
    let gout = x.clone();
    let mut y = a.div_floor_wide(&x);
    loop {
        let g = x.gcd_recursive(&y);
        if g == Int::ONE {
            return (gout, x, y);
        }
        x = &x * &g;
        y = y.div_floor_wide(&g);
    }
}

fn ppi(a: &Int, c: &Int) -> Int {
    gcd_ppi_ppo(a, c).1
}

/// Algorithm 11.4 of Bernstein (2005): returns `(gcd(a, b), ppg(a, b), pple(a, b))`.
fn gcd_ppg_pple(a: &Int, b: &Int) -> (Int, Int, Int) {
    let mut y = a.gcd_recursive(b);
    let gout = y.clone();
    let mut x = a.div_floor_wide(&y);
    loop {
        let g = x.gcd_recursive(&y);
        if g == Int::ONE {
            return (gout, x, y);
        }
        x = &x * &g;
        y = y.div_floor_wide(&g);
    }
}

fn two_power(mut a: Int, mut n: usize) -> Int {
    while n > 0 {
        a = &a * &a;
        n -= 1;
    }
    a
}

/// Algorithm 13.2 of Bernstein (2005), iterative explicit stack: appends the natural coprime base
/// of `{a, b}` to `out`.
fn append_cb_pair(out: &mut Vec<Int>, a0: Int, b0: Int) {
    enum Task {
        Pair(Int, Int),
    }
    let mut stack = vec![Task::Pair(a0, b0)];
    while let Some(Task::Pair(a_in, b)) = stack.pop() {
        if a_in <= Int::ONE {
            if b > Int::ONE {
                out.push(b);
            }
            continue;
        }
        if b <= Int::ONE {
            out.push(a_in);
            continue;
        }
        if a_in == b {
            out.push(a_in);
            continue;
        }
        let (_, a, r) = gcd_ppi_ppo(&a_in, &b);
        if r > Int::ONE {
            out.push(r);
        }
        if a <= Int::ONE {
            out.push(b);
            continue;
        }
        let (mut g, mut h, mut c) = gcd_ppg_pple(&a, &b);
        let c0 = c.clone();
        let mut x = c0.clone();
        let mut n: usize = 1;
        let mut sub_calls: Vec<(Int, Int)> = Vec::new();
        loop {
            let g_sq = &g * &g;
            let (ng, nh, nc) = gcd_ppg_pple(&h, &g_sq);
            g = ng;
            h = nh;
            c = nc;
            let d = c.gcd_recursive(&b);
            x = &x * &d;
            let y = two_power(d.clone(), n - 1);
            sub_calls.push((c.div_floor_wide(&y), d));
            if h == Int::ONE {
                break;
            }
            n += 1;
        }
        // Push in reverse so execution order matches Bernstein's recursive order.
        stack.push(Task::Pair(b.div_floor_wide(&x), c0));
        for (sa, sb) in sub_calls.into_iter().rev() {
            stack.push(Task::Pair(sa, sb));
        }
    }
}

/// Balanced binary product; multiplication costs are included in the bit cost.
fn prod_slice(items: &[Int]) -> Int {
    if items.is_empty() {
        return Int::ONE;
    }
    let mut cur: Vec<Int> = items.to_vec();
    while cur.len() > 1 {
        let mut next = Vec::with_capacity(cur.len().div_ceil(2));
        let mut it = cur.into_iter();
        while let Some(a) = it.next() {
            if let Some(b) = it.next() {
                next.push(&a * &b);
            } else {
                next.push(a);
            }
        }
        cur = next;
    }
    cur.pop().unwrap_or(Int::ONE)
}

/// Product tree in a flat arena. Construction, traversal and destruction all
/// use explicit storage; no call stack grows with the number of inputs.
struct ProdEntry {
    prod: Int,
    tag: Option<usize>,
    children: Option<(usize, usize)>,
}
struct ProdNode {
    prod: Int,
    nodes: Vec<ProdEntry>,
}

fn build_prod_tree(items: &[(usize, Int)]) -> Option<ProdNode> {
    if items.is_empty() {
        return None;
    }
    let mut nodes: Vec<_> = items
        .iter()
        .map(|(tag, v)| ProdEntry {
            prod: v.clone(),
            tag: Some(*tag),
            children: None,
        })
        .collect();
    let mut level: Vec<usize> = (0..nodes.len()).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            if pair.len() == 1 {
                next.push(pair[0]);
                continue;
            }
            let (l, r) = (pair[0], pair[1]);
            let prod = &nodes[l].prod * &nodes[r].prod;
            next.push(nodes.len());
            nodes.push(ProdEntry {
                prod,
                tag: None,
                children: Some((l, r)),
            });
        }
        level = next;
    }
    Some(ProdNode {
        prod: nodes[level[0]].prod.clone(),
        nodes,
    })
}

/// Sparse divisibility traversal: discard a subtree as soon as its product
/// shares no prime factor with the remaining input. The output contains only
/// the nontrivial factors of that input.
// None only if `tree` is not as `build_prod_tree` makes it: no node, or a node with neither a
// tag nor children. No stop is reachable (I6.12); the caller refuses.
fn split_sparse(a: &Int, tree: &ProdNode, out: &mut Vec<(usize, Int)>) -> Option<()> {
    if *a <= Int::ONE {
        return Some(());
    }
    let mut stack = vec![(tree.nodes.len().checked_sub(1)?, a.clone())];
    while let Some((i, cur)) = stack.pop() {
        let node = &tree.nodes[i];
        let b = ppi(&cur, &node.prod);
        if b <= Int::ONE {
            continue;
        }
        if let Some(tag) = node.tag {
            out.push((tag, b));
            continue;
        }
        // build_prod_tree creates either a tagged leaf or an internal node
        // with both child indices; this branch has already excluded a leaf.
        let (l, r) = node.children?;
        stack.push((r, b.clone()));
        stack.push((l, b));
    }
    Some(())
}

/// Algorithm 16.2 of Bernstein (2005) with sparse collision filtering: `cb(P union {b})`.
fn cb_extend(p: Vec<Int>, b: Int) -> Option<Vec<Int>> {
    if b <= Int::ONE {
        return Some(p);
    }
    if p.is_empty() {
        return Some(vec![b]);
    }
    let indexed: Vec<(usize, Int)> = p.iter().cloned().enumerate().collect();
    // p.is_empty() returned above; indexed has exactly p.len() leaves.
    let tree = build_prod_tree(&indexed)?;
    let (g, a, r) = gcd_ppi_ppo(&b, &tree.prod);
    if g == Int::ONE {
        let mut out = p;
        out.push(b);
        return Some(out);
    }
    let mut hits: Vec<(usize, Int)> = Vec::new();
    split_sparse(&a, &tree, &mut hits)?;
    let mut s_by_idx: HashMap<usize, Int> = hits.into_iter().collect();

    let mut result = Vec::with_capacity(p.len() + 2);
    if r > Int::ONE {
        result.push(r);
    }
    for (idx, p_i) in p.into_iter().enumerate() {
        if let Some(s_i) = s_by_idx.remove(&idx) {
            append_cb_pair(&mut result, p_i, s_i);
        } else {
            result.push(p_i);
        }
    }
    Some(result)
}

/// Algorithm 17.3 of Bernstein (2005) enhanced with coprime fast-path and active-subset filtering:
/// merges two coprime bases `p` and `q` into `cb(p union q)`.
fn cb_merge(p: Vec<Int>, q: Vec<Int>) -> Option<Vec<Int>> {
    if p.is_empty() {
        return Some(q);
    }
    if q.is_empty() {
        return Some(p);
    }
    let p_idx: Vec<(usize, Int)> = p.iter().cloned().enumerate().collect();
    let q_idx: Vec<(usize, Int)> = q.iter().cloned().enumerate().collect();
    // Both empty-input branches returned; each indexed list has its input's length.
    let p_tree = build_prod_tree(&p_idx)?;
    let q_tree = build_prod_tree(&q_idx)?;
    let g = p_tree.prod.gcd_recursive(&q_tree.prod);
    if g == Int::ONE {
        let mut out = Vec::with_capacity(p.len() + q.len());
        out.extend(p);
        out.extend(q);
        return Some(out);
    }

    // Separate `p` and `q` into untouched coprime elements and colliding elements.
    let mut p_hits = Vec::new();
    split_sparse(&g, &p_tree, &mut p_hits)?;
    let p_hit_set: HashSet<usize> = p_hits.into_iter().map(|(i, _)| i).collect();

    let mut q_hits = Vec::new();
    split_sparse(&g, &q_tree, &mut q_hits)?;
    let q_hit_set: HashSet<usize> = q_hits.into_iter().map(|(i, _)| i).collect();

    let mut untouched = Vec::new();
    let mut s_active = Vec::new();
    for (i, v) in p.into_iter().enumerate() {
        if p_hit_set.contains(&i) {
            s_active.push(v);
        } else {
            untouched.push(v);
        }
    }
    let mut q_active = Vec::new();
    for (i, v) in q.into_iter().enumerate() {
        if q_hit_set.contains(&i) {
            q_active.push(v);
        } else {
            untouched.push(v);
        }
    }

    if q_active.len() == 1 {
        // The branch condition is q_active.len() == 1; no intervening mutation.
        let mut merged = cb_extend(s_active, q_active.pop()?)?;
        merged.extend(untouched);
        return Some(merged);
    }

    let n = q_active.len();
    let mut bits = 1usize;
    // n is the length of an allocated Vec<Int>, whose elements occupy more
    // than one byte, so its ceiling log2 is below usize::BITS.
    while (1usize << bits) < n {
        bits += 1;
    }
    for bit_i in 0..bits {
        let mut r0 = Vec::new();
        let mut r1 = Vec::new();
        for (k, v) in q_active.iter().enumerate() {
            if ((k >> bit_i) & 1) == 0 {
                r0.push(v.clone());
            } else {
                r1.push(v.clone());
            }
        }
        s_active = cb_extend(s_active, prod_slice(&r0))?;
        s_active = cb_extend(s_active, prod_slice(&r1))?;
    }
    s_active.extend(untouched);
    Some(s_active)
}

// The coprime base, each modulus as base indices with powers, and the powers of each base.
type CoprimeBase = (Vec<Int>, BTreeMap<Int, Vec<(usize, Int)>>, Vec<Vec<Int>>);
// A slice of moduli with the bases still to split over it (Algorithm 21.2).
type FactorJob<'a> = (&'a [Int], Vec<(usize, Int)>);

/// Algorithm 18.1 + 21.2 of Bernstein (2005): computes the sorted natural coprime base `bases` of
/// `moduli`, the prime-power-like factor list `mod_factors[m] = [(base_idx, q_{m, idx})]` for each
/// `m`, and `base_all_powers[base_idx]` (sorted powers dividing any `m`).
// None only where a product tree is not as built (see `split_sparse`).
fn coprime_base_and_factors(mut moduli: Vec<Int>) -> Option<CoprimeBase> {
    moduli.retain(|m| *m > Int::ONE);
    moduli.sort();
    moduli.dedup();
    if moduli.is_empty() {
        return Some((Vec::new(), BTreeMap::new(), Vec::new()));
    }

    // Bottom-up merge tree for Algorithm 18.1 (`cb`).
    let mut level: Vec<Vec<Int>> = moduli.iter().cloned().map(|m| vec![m]).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut it = level.into_iter();
        while let Some(p) = it.next() {
            if let Some(q) = it.next() {
                next.push(cb_merge(p, q)?);
            } else {
                next.push(p);
            }
        }
        level = next;
    }
    let mut bases = level.pop().unwrap_or_default();
    bases.retain(|b| *b > Int::ONE);
    bases.sort();
    bases.dedup();

    let num_bases = bases.len();
    let mut mod_factors: BTreeMap<Int, Vec<(usize, Int)>> = BTreeMap::new();
    let mut base_powers_set: Vec<BTreeSet<Int>> = vec![BTreeSet::new(); num_bases];

    // Simultaneous divide-and-conquer factorization (Algorithm 21.2).
    let initial_p: Vec<(usize, Int)> = bases.iter().cloned().enumerate().collect();
    let mut stack: Vec<FactorJob<'_>> = vec![(&moduli[..], initial_p)];

    while let Some((s_slice, p_sub)) = stack.pop() {
        if s_slice.is_empty() || p_sub.is_empty() {
            continue;
        }
        if s_slice.len() == 1 {
            let m = &s_slice[0];
            // Empty p_sub was excluded at this frame's entry.
            let p_tree = build_prod_tree(&p_sub)?;
            let mut facs = Vec::new();
            split_sparse(m, &p_tree, &mut facs)?;
            facs.sort_by_key(|&(idx, _)| idx);
            for &(idx, ref q) in &facs {
                base_powers_set[idx].insert(q.clone());
            }
            mod_factors.insert(m.clone(), facs);
            continue;
        }
        let p_tree = build_prod_tree(&p_sub)?;
        let mid = s_slice.len() / 2;
        for half in [&s_slice[mid..], &s_slice[..mid]] {
            let y = prod_slice(half);
            let z = ppi(&p_tree.prod, &y);
            let mut hits = Vec::new();
            split_sparse(&z, &p_tree, &mut hits)?;
            hits.sort_by_key(|&(idx, _)| idx);
            let q_sub: Vec<(usize, Int)> = hits
                .into_iter()
                .map(|(idx, _)| (idx, bases[idx].clone()))
                .collect();
            stack.push((half, q_sub));
        }
    }

    let base_all_powers: Vec<Vec<Int>> = base_powers_set
        .into_iter()
        .enumerate()
        .map(|(i, mut set)| {
            if set.is_empty() {
                set.insert(bases[i].clone());
            }
            set.into_iter().collect()
        })
        .collect();

    Some((bases, mod_factors, base_all_powers))
}

enum ConsolidateOut {
    Ok(BaseInfo, ResidueSet),
    Empty,
    Undecided,
}

/// Intersects a residue set `cur` modulo `max_q_z` with `{z : (z mod q_z) in s_z}`, where `q_z`
/// divides `max_q_z`.
fn intersect_mod_divisor(
    cur: &[(Int, Int)],
    s_z: &[(Int, Int)],
    q_z: &Int,
    max_q_z: &Int,
) -> Option<ResidueSet> {
    if q_z == max_q_z {
        return Some(res_intersect(cur, s_z));
    }
    if res_is_full(s_z, q_z) {
        return Some(cur.to_vec());
    }
    let mut out = Vec::new();
    for (lo, hi) in cur {
        let ql = lo.div_floor_wide(q_z);
        let qh = hi.div_floor_wide(q_z);
        if ql == qh {
            let rl = lo.mod_floor_wide(q_z);
            let rh = hi.mod_floor_wide(q_z);
            let base = &ql * q_z;
            for (sl, sh) in res_intersect(&[(rl, rh)], s_z) {
                out.push((&base + &sl, &base + &sh));
            }
        } else if qh == &ql + &Int::ONE {
            let rl = lo.mod_floor_wide(q_z);
            let base_l = &ql * q_z;
            for (sl, sh) in res_intersect(&[(rl, q_z - &Int::ONE)], s_z) {
                out.push((&base_l + &sl, &base_l + &sh));
            }
            let rh = hi.mod_floor_wide(q_z);
            let base_h = &qh * q_z;
            for (sl, sh) in res_intersect(&[(Int::ZERO, rh)], s_z) {
                out.push((&base_h + &sl, &base_h + &sh));
            }
        } else {
            // The whole blocks between would be written one by one; left to the general path
            // (the Complexity tradeoff comment at the end of `solve_modular`).
            return None;
        }
    }
    Some(res_normalize(out, max_q_z))
}

/// Consolidates residue constraints across powers `q_1 | q_2 | ... | max_q` of the same base
/// via single-residue stride reduction `(u, stride)` and block-aware divisor intersection.
fn consolidate_prime_powers(powers: &BTreeMap<Int, ResidueSet>, max_q: &Int) -> ConsolidateOut {
    let mut work: Vec<(Int, ResidueSet)> =
        powers.iter().map(|(q, s)| (q.clone(), s.clone())).collect();

    // Complexity tradeoff: repeatedly propagating each singleton into every
    // lower power takes O(k^2) remainder operations. The highest singleton
    // already fixes every lower power; if they agree with it, all lower
    // singletons agree with each other. Reduce that residue once by a
    // product/remainder tree, O(M(B) log k), then intersect each set once.
    // No constraint or answer is given up. Tests: pncx_power_propagation_scale
    // (parameterized by total input bits) and pncx_power_propagation_oracle.
    if let Some(i) = work
        .iter()
        .rposition(|(_, s)| matches!(s.as_slice(), [(a, b)] if a == b))
    {
        let residue = work[i].1[0].0.clone();
        let moduli: Vec<_> = work[..i].iter().map(|p| p.0.clone()).collect();
        let remainders = batch_remainders(&residue, &moduli);
        if remainders.len() != i {
            return ConsolidateOut::Undecided;
        }
        for ((_, set), r) in work[..i].iter_mut().zip(remainders) {
            *set = res_intersect(set, &[(r.clone(), r)]);
            if set.is_empty() {
                return ConsolidateOut::Empty;
            }
        }
    }

    // Pass 2: Upward single-residue stride reduction `(u, stride)`.
    let mut u = Int::ZERO;
    let mut stride = Int::ONE;
    let mut rem_powers: Vec<(Int, ResidueSet)> = Vec::new();
    for (q, s_q) in work {
        let proj = project_stride(&s_q, &u, &stride);
        if proj.is_empty() {
            return ConsolidateOut::Empty;
        }
        if proj.len() == 1 && proj[0].0 == proj[0].1 {
            u = &u + &(&stride * &proj[0].0);
            stride = q;
        } else {
            let q_z = q.div_floor_wide(&stride);
            rem_powers.push((q_z, proj));
        }
    }

    let z_max_q = max_q.div_floor_wide(&stride);
    let info = BaseInfo {
        max_q: max_q.clone(),
        u,
        stride,
        z_max_q: z_max_q.clone(),
    };
    if rem_powers.is_empty() {
        return ConsolidateOut::Ok(info, vec![(Int::ZERO, Int::ZERO)]);
    }

    // Pass 3: Intersect remaining multi-residue powers `q_z | z_max_q`.
    let mut cur = vec![(Int::ZERO, &z_max_q - &Int::ONE)];
    for (q_z, s_z) in rem_powers.into_iter().rev() {
        if let Some(inter) = intersect_mod_divisor(&cur, &s_z, &q_z, &z_max_q) {
            cur = inter;
            if cur.is_empty() {
                return ConsolidateOut::Empty;
            }
        } else {
            // Check if the complement of `cur` has empty intersection with `s_z`, in which case
            // `cur` is redundant on `s_z`.
            let comp_cur = res_complement(&cur, &z_max_q);
            if let Some(forb_inter) = intersect_mod_divisor(&comp_cur, &s_z, &q_z, &z_max_q)
                && forb_inter.is_empty()
            {
                // Every `z` with `(z mod q_z) in s_z` avoids `comp_cur`!
                if let Some(lifted_s) = intersect_mod_divisor(
                    &[(Int::ZERO, &z_max_q - &Int::ONE)],
                    &s_z,
                    &q_z,
                    &z_max_q,
                ) {
                    cur = lifted_s;
                    continue;
                }
            }
            return ConsolidateOut::Undecided;
        }
    }
    ConsolidateOut::Ok(info, cur)
}

/// Core solver on pairwise coprime bases `bases_info[0..t]` with allowed residue sets
/// `allowed[0..t]` (in `z_i in [0, bases_info[i].z_max_q - 1]`) and clauses `clauses` on `[lo, hi]`.
fn solve_coprime_system(
    lo: &Option<Int>,
    hi: &Option<Int>,
    bases_info: &[BaseInfo],
    allowed: Vec<ResidueSet>,
    clauses: Vec<BTreeMap<usize, ResidueSet>>,
    allow_split: bool,
) -> RegimeOut {
    // Complexity tradeoff: splitting each base while replaying unrelated
    // clauses costs O(t L) for t bases and L literals, before arithmetic.
    // The clause incidence graph separates independent residue choices in
    // O(t + L) operations. Solve each component once and combine its points
    // by a balanced CRT tree. This costs the sum of the component solves
    // plus CRT, rather than replaying other components. A bounded interval
    // couples the choices, so it keeps the original path. An undecided
    // component also keeps that path; no existing answer is given up.
    // Test: pncx_independent_components_scale; negative control: omit this
    // sufficient witness, exposing Stage C's repeated component scans.
    // Complexity tradeoff: Stage C replays all bases and clauses, quadratic
    // on connected triangles (I4.20). Recognize matching exclusions on
    // three-element domains, transport their value labels, and remove
    // vertices of degree below three. Reverse greedy coloring costs
    // O(v + e) after O(e log e) grouping, plus balanced CRT bit cost.
    // Nonmatching, inconsistent or unsettled cores give no verdict;
    // this is a sufficient witness, with no search or size budget.
    // Tests: pncx_connected_colors_scale, pncx_coloring_relabelings.
    if allow_split {
        if let Some(point) = score_witness(bases_info, &allowed, &clauses) {
            let period = prod_slice(
                &bases_info
                    .iter()
                    .map(|b| b.max_q.clone())
                    .collect::<Vec<_>>(),
            );
            if let Some(point) = pick_in_span(lo, hi, &point, &period) {
                return RegimeOut::Found(point);
            }
        }
        if let Some(point) = graph_coloring_witness(bases_info, &allowed, &clauses) {
            // A bounded interval may include a representative of the coloring's
            // period. Test that representative; missing it gives no verdict.
            let period = prod_slice(
                &bases_info
                    .iter()
                    .map(|b| b.max_q.clone())
                    .collect::<Vec<_>>(),
            );
            if let Some(point) = pick_in_span(lo, hi, &point, &period) {
                return RegimeOut::Found(point);
            }
        }
    }
    if lo.is_none()
        && hi.is_none()
        && allow_split
        && let Some(point) = independent_component_witness(bases_info, &allowed, &clauses)
    {
        return RegimeOut::Found(point);
    }
    solve_coprime_connected(lo, hi, bases_info, allowed, clauses, allow_split)
}

/// A sufficient point from uniquely most frequent permitted values. A clause
/// must already be satisfied by such a value; choices on the other bases then
/// cannot change that clause's truth.
// Complexity tradeoff: enumerating every residue can be exponential in its
// written bits. Sweep the written interval endpoints, O(S log S), to find a
// unique maximizing value on each base. A tie gives no preferred value, so
// this rule is invariant under local value permutations and affine renaming.
// Failure to cover every clause gives no verdict. CRT retains its bit cost.
// Tests: pncx_score_witness_oracle; pncx_score_witness_scale is deferred to plan
// row PRES-scaling-10_5 in wt/scratch/deferred-tests/PRES-scaling-10_5.rs.
fn score_witness(
    info: &[BaseInfo],
    allowed: &[ResidueSet],
    clauses: &[BTreeMap<usize, ResidueSet>],
) -> Option<Int> {
    if info.len() != allowed.len() || clauses.is_empty() {
        return None;
    }
    let mut events: Vec<BTreeMap<Int, (i128, i128)>> = vec![BTreeMap::new(); info.len()];
    for (i, domain) in allowed.iter().enumerate() {
        for (a, b) in domain {
            events[i].entry(a.clone()).or_default().1 += 1;
            events[i].entry(b + &Int::ONE).or_default().1 -= 1;
        }
    }
    for cl in clauses {
        for (&i, set) in cl {
            let row = events.get_mut(i)?;
            for (a, b) in set {
                row.entry(a.clone()).or_default().0 += 1;
                row.entry(b + &Int::ONE).or_default().0 -= 1;
            }
        }
    }
    let mut preferred = Vec::with_capacity(info.len());
    for row in events {
        let (mut score, mut inside) = (0i128, 0i128);
        let mut best: Option<i128> = None;
        let mut unique = None;
        let mut iter = row.into_iter().peekable();
        while let Some((at, (ds, di))) = iter.next() {
            score += ds;
            inside += di;
            let Some((next, _)) = iter.peek() else {
                break;
            };
            if inside == 0 {
                continue;
            }
            match best {
                None => {
                    best = Some(score);
                    unique = (next == &(&at + &Int::ONE)).then_some(at);
                }
                Some(old) if score > old => {
                    best = Some(score);
                    unique = (next == &(&at + &Int::ONE)).then_some(at);
                }
                Some(old) if score == old => unique = None,
                Some(_) => {}
            }
        }
        preferred.push(unique);
    }
    if !clauses.iter().all(|cl| {
        cl.iter().any(|(&i, s)| {
            preferred
                .get(i)
                .and_then(Option::as_ref)
                .is_some_and(|v| res_contains(s, v))
        })
    }) {
        return None;
    }
    let mut choices = Vec::with_capacity(info.len());
    for (i, base) in info.iter().enumerate() {
        let value = preferred[i]
            .as_ref()
            .or_else(|| allowed[i].first().map(|p| &p.0))?;
        choices.push((base.r_from_z(value), base.max_q.clone()));
    }
    combine_crt_tree(choices).map(|p| p.0)
}

/// A sufficient coloring witness, invariant under independent relabeling of each
/// three-element residue domain. Each edge must exclude a perfect matching of
/// its endpoints' values; transporting those matchings must be consistent.
fn graph_coloring_witness(
    info: &[BaseInfo],
    allowed: &[ResidueSet],
    clauses: &[BTreeMap<usize, ResidueSet>],
) -> Option<Int> {
    if info.len() != allowed.len() || clauses.is_empty() {
        return None;
    }
    let mut domains = Vec::with_capacity(allowed.len());
    for s in allowed {
        if res_count(s) != Int::from(3) {
            return None;
        }
        let mut values = Vec::with_capacity(3);
        for (a, b) in s {
            let mut v = a.clone();
            while v <= *b {
                values.push(v.clone());
                v = &v + &Int::ONE;
            }
        }
        domains.push(values);
    }
    let mut edges: BTreeMap<(usize, usize), BTreeSet<(usize, usize)>> = BTreeMap::new();
    for cl in clauses {
        if cl.len() != 2 {
            return None;
        }
        let mut ends = Vec::with_capacity(2);
        for (&i, s) in cl {
            let missing = res_diff(allowed.get(i)?, s, &info.get(i)?.z_max_q);
            let [(a, b)] = missing.as_slice() else {
                return None;
            };
            if a != b {
                return None;
            }
            ends.push((i, domains.get(i)?.iter().position(|v| v == a)?));
        }
        edges
            .entry((ends[0].0, ends[1].0))
            .or_default()
            .insert((ends[0].1, ends[1].1));
    }
    let n = info.len();
    let mut adjacent: Vec<Vec<(usize, [usize; 3])>> = vec![Vec::new(); n];
    for ((a, b), pairs) in edges {
        if pairs.len() != 3 {
            return None;
        }
        let mut left = [false; 3];
        let mut right = [false; 3];
        let mut perm = [0; 3];
        let mut inverse = [0; 3];
        for (i, j) in pairs {
            if left[i] || right[j] {
                return None;
            }
            left[i] = true;
            right[j] = true;
            perm[i] = j;
            inverse[j] = i;
        }
        adjacent[a].push((b, perm));
        adjacent[b].push((a, inverse));
    }
    let mut labels: Vec<Option<[usize; 3]>> = vec![None; n];
    for start in 0..n {
        if labels[start].is_some() {
            continue;
        }
        labels[start] = Some([0, 1, 2]);
        let mut todo = vec![start];
        while let Some(a) = todo.pop() {
            let from = labels[a]?;
            for &(b, perm) in &adjacent[a] {
                let mut to = [0; 3];
                for i in 0..3 {
                    to[perm[i]] = from[i];
                }
                match labels[b] {
                    Some(old) if old != to => return None,
                    Some(_) => {}
                    None => {
                        labels[b] = Some(to);
                        todo.push(b);
                    }
                }
            }
        }
    }
    let mut degrees: Vec<_> = adjacent.iter().map(Vec::len).collect();
    let mut queue: VecDeque<_> = (0..n).filter(|&i| degrees[i] < 3).collect();
    let mut removed = vec![false; n];
    let mut order = Vec::with_capacity(n);
    while let Some(a) = queue.pop_front() {
        if removed[a] {
            continue;
        }
        removed[a] = true;
        order.push(a);
        for &(b, _) in &adjacent[a] {
            if !removed[b] {
                degrees[b] -= 1;
                if degrees[b] == 2 {
                    queue.push_back(b);
                }
            }
        }
    }
    let mut colors = vec![None; n];
    let mut local_index = vec![0; n];
    // Complexity tradeoff: declining an odd three-core misses easy cubic
    // graphs. First color bipartite cores; otherwise use the constructive
    // Brooks coloring on a subcubic core, O((v+e) log v) graph operations.
    // A universal vertex with a bipartite remainder also has a direct
    // coloring. Other higher-degree cores give no verdict. Tests: pncx_brooks_subcubic_oracle,
    // pncx_prism_core_scale and pncx_coloring_small_graphs_match_enumeration.
    for start in 0..n {
        if removed[start] || colors[start].is_some() {
            continue;
        }
        colors[start] = Some(0usize);
        let mut component = vec![start];
        let mut todo = vec![start];
        let mut bipartite = true;
        while let Some(a) = todo.pop() {
            let next = 1usize.checked_sub(colors[a]?)?;
            for &(b, _) in &adjacent[a] {
                if removed[b] {
                    continue;
                }
                match colors[b] {
                    Some(c) if c != next => bipartite = false,
                    Some(_) => {}
                    None => {
                        colors[b] = Some(next);
                        component.push(b);
                        todo.push(b);
                    }
                }
            }
        }
        if !bipartite {
            component.sort_unstable();
            for (i, &v) in component.iter().enumerate() {
                local_index[v] = i;
            }
            let graph: Vec<Vec<usize>> = component
                .iter()
                .map(|&v| {
                    adjacent[v]
                        .iter()
                        .filter(|(w, _)| !removed[*w])
                        .map(|(w, _)| local_index[*w])
                        .collect()
                })
                .collect();
            let own = brooks::color(&graph).or_else(|| brooks::universal(&graph))?;
            for (&v, c) in component.iter().zip(own) {
                colors[v] = Some(c);
            }
        }
    }
    for a in order.into_iter().rev() {
        let mut used = [false; 3];
        for &(b, _) in &adjacent[a] {
            if let Some(c) = colors[b] {
                used[c] = true;
            }
        }
        colors[a] = (0..3).find(|&c| !used[c]);
        colors[a]?;
    }
    let mut choices = Vec::with_capacity(n);
    for i in 0..n {
        let labels = labels[i]?;
        let local = labels.iter().position(|&c| Some(c) == colors[i])?;
        let r = &info[i].u + &(&info[i].stride * &domains[i][local]);
        choices.push((r, info[i].max_q.clone()));
    }
    combine_crt_tree(choices).map(|(x, _)| x)
}

fn independent_component_witness(
    info: &[BaseInfo],
    allowed: &[ResidueSet],
    clauses: &[BTreeMap<usize, ResidueSet>],
) -> Option<Int> {
    let mut neighbors = vec![Vec::new(); info.len()];
    for cl in clauses {
        let mut keys = cl.keys();
        let &first = keys.next()?;
        for &other in keys {
            neighbors[first].push(other);
            neighbors[other].push(first);
        }
    }
    let mut component = vec![None; info.len()];
    let mut groups = Vec::new();
    for root in 0..info.len() {
        if component[root].is_some() {
            continue;
        }
        let id = groups.len();
        component[root] = Some(id);
        let mut pending = vec![root];
        let mut group = Vec::new();
        while let Some(v) = pending.pop() {
            group.push(v);
            for &other in &neighbors[v] {
                if component[other].is_none() {
                    component[other] = Some(id);
                    pending.push(other);
                }
            }
        }
        groups.push(group);
    }
    if groups.len() <= 1 {
        return None;
    }
    let mut grouped_clauses = vec![Vec::new(); groups.len()];
    for cl in clauses {
        let &first = cl.keys().next()?;
        grouped_clauses[component[first]?].push(cl);
    }
    let mut local_index = vec![0; info.len()];
    let mut choices = Vec::with_capacity(info.len());
    for (group, cs) in groups.into_iter().zip(grouped_clauses) {
        for (i, &v) in group.iter().enumerate() {
            local_index[v] = i;
        }
        let local_info: Vec<_> = group.iter().map(|&v| info[v].clone()).collect();
        let local_allowed = group.iter().map(|&v| allowed[v].clone()).collect();
        let local_clauses = cs
            .into_iter()
            .map(|cl| {
                cl.iter()
                    .map(|(&v, set)| (local_index[v], set.clone()))
                    .collect()
            })
            .collect();
        // This call does not decompose again. Stage C's calls have
        // allow_split=false, so the added wrapper cannot grow call depth.
        let RegimeOut::Found(point) = solve_coprime_connected(
            &None,
            &None,
            &local_info,
            local_allowed,
            local_clauses,
            true,
        ) else {
            return None;
        };
        for base in local_info {
            choices.push((point.mod_floor_wide(&base.max_q), base.max_q));
        }
    }
    combine_crt_tree(choices).map(|(point, _)| point)
}

fn solve_coprime_connected(
    lo: &Option<Int>,
    hi: &Option<Int>,
    bases_info: &[BaseInfo],
    mut allowed: Vec<ResidueSet>,
    mut clauses: Vec<BTreeMap<usize, ResidueSet>>,
    allow_split: bool,
) -> RegimeOut {
    // The two places that start over with the new residue sets loop back here; the recursive
    // calls of Stage C pass `allow_split = false` and cannot split again, so the call depth is
    // at most 2 whatever the input.
    let mut allow_split = allow_split;
    'restart: loop {
        let t = bases_info.len();
        let mut fixed_base: Vec<Option<Int>> = vec![None; t];

        // Stage A: Unit propagation & single-residue fixpoint.
        loop {
            let mut changed = false;
            for i in 0..t {
                if allowed[i].is_empty() {
                    return RegimeOut::Empty;
                }
                if fixed_base[i].is_none()
                    && allowed[i].len() == 1
                    && allowed[i][0].0 == allowed[i][0].1
                {
                    fixed_base[i] = Some(allowed[i][0].0.clone());
                    changed = true;
                }
            }

            let mut next_clauses = Vec::with_capacity(clauses.len());
            for mut cl in clauses {
                let mut satisfied = false;
                cl.retain(|&i, s_i| {
                    if satisfied {
                        return false;
                    }
                    if let Some(r) = &fixed_base[i] {
                        if res_contains(s_i, r) {
                            satisfied = true;
                        }
                        return false;
                    }
                    let inter = res_intersect(&allowed[i], s_i);
                    if inter.is_empty() {
                        false
                    } else if inter == allowed[i] {
                        satisfied = true;
                        false
                    } else {
                        *s_i = inter;
                        true
                    }
                });
                if satisfied {
                    continue;
                }
                if cl.is_empty() {
                    return RegimeOut::Empty;
                }
                if cl.len() == 1 {
                    let Some((i, s_i)) = cl.into_iter().next() else {
                        return RegimeOut::Undecided;
                    };
                    let new_a = res_intersect(&allowed[i], &s_i);
                    if new_a.is_empty() {
                        return RegimeOut::Empty;
                    }
                    if new_a != allowed[i] {
                        allowed[i] = new_a;
                        changed = true;
                    }
                } else {
                    next_clauses.push(cl);
                }
            }
            clauses = next_clauses;
            if !changed {
                break;
            }
        }

        // Combine all fixed bases `fixed_base[i] == Some(z_i)` and any lower-power strides
        // `(bases_info[i].u, bases_info[i].stride)` via CRT ([`combine_crt_tree`]).
        let mut crt_pairs: Vec<(Int, Int)> = Vec::new();
        for i in 0..t {
            if let Some(z) = &fixed_base[i] {
                crt_pairs.push((bases_info[i].r_from_z(z), bases_info[i].max_q.clone()));
            } else if bases_info[i].stride > Int::ONE {
                crt_pairs.push((bases_info[i].u.clone(), bases_info[i].stride.clone()));
            }
        }
        let Some((r0, m0)) = combine_crt_tree(crt_pairs) else {
            return RegimeOut::Empty;
        };

        // Check if the progression `x = r0 + m0 * y` meets `[lo, hi]`, and if `m0` reduces `[lo, hi]`
        // so that some unfixed base `z_max_q > hi_y - lo_y` has single-residue exclusions!
        let (lo_y, hi_y) = match y_span(lo, hi, &r0, &m0) {
            Some(span) => span,
            None => return RegimeOut::Empty,
        };

        if let (Some(ly), Some(hy)) = (&lo_y, &hi_y) {
            if ly == hy {
                let x_cand = &r0 + &(&m0 * ly);
                return if holds_coprime_point(&x_cand, bases_info, &allowed, &clauses) {
                    RegimeOut::Found(x_cand)
                } else {
                    RegimeOut::Empty
                };
            }
            // Short-period hole cutting in `y`-space: for any unfixed base `i` with
            // `bases_info[i].z_max_q > hy - ly` whose forbidden set consists of single residues `z_f`,
            // each forbidden `z_f` maps to a single residue `r_y` modulo `z_max_q`, cutting at most 1
            // integer out of `[ly, hy]`!
            let width_y = hy - ly;
            let mut y_hole_pieces: Vec<Span> = Vec::new();
            let mut cut_any = false;
            let mut satisfied_bases = vec![false; t];
            for i in 0..t {
                let z_q = &bases_info[i].z_max_q;
                if fixed_base[i].is_some() || *z_q <= width_y {
                    continue;
                }
                let comp = res_complement(&allowed[i], z_q);
                let r0_z = (&r0 - &bases_info[i].u).div_floor(&bases_info[i].stride);
                let m0_z = m0.div_floor(&bases_info[i].stride);
                if let Some(inv_m0) = inverse_mod(&m0_z, z_q) {
                    let u_inv = wide_remainder(&-&(&r0_z * &inv_m0), z_q);
                    if let Some(ry_forb) = map_affine_mod(&comp, &inv_m0, &u_inv, z_q) {
                        for (ry_a, ry_b) in ry_forb {
                            for (hl, hh) in concrete_intervals_in_span(ly, hy, z_q, &ry_a, &ry_b) {
                                y_hole_pieces.push((Some(hl), Some(hh)));
                                cut_any = true;
                            }
                        }
                        if !clauses.iter().any(|cl| cl.contains_key(&i)) {
                            satisfied_bases[i] = true;
                        }
                    }
                }
            }
            if cut_any {
                let y_dom = Domain::range(ly.clone(), hy.clone())
                    .intersect(&Domain::from_pieces(y_hole_pieces).complement());
                if y_dom.is_empty() {
                    return RegimeOut::Empty;
                }
                if clauses.is_empty()
                    && (0..t).all(|i| fixed_base[i].is_some() || satisfied_bases[i])
                {
                    let Some(first_y) = y_dom.pieces.first().and_then(|p| p.0.as_ref()) else {
                        return RegimeOut::Undecided;
                    };
                    return RegimeOut::Found(&r0 + &(&m0 * first_y));
                }
            }
        }

        // Active unfixed bases: those with `fixed_base[i].is_none()`.
        // Compute forbidden box `F_j` for each clause `cl` in `clauses`:
        // `F_{j, i} = allowed[i] \ cl[i]`.
        clauses.sort();
        clauses.dedup();

        // Merge clauses of size 2 that share `(i1, F_{j, i1})` on `i2`:
        if clauses.len() > 1 {
            clauses = merge_pair_clauses(clauses, &allowed);
            if clauses.iter().any(|cl| cl.len() <= 1) {
                continue 'restart;
            }
        }

        let mut boxes: Vec<BTreeMap<usize, ResidueSet>> = Vec::with_capacity(clauses.len());
        for cl in &clauses {
            let mut f_box = BTreeMap::new();
            for (&i, s_i) in cl {
                let f_i = res_diff(&allowed[i], s_i, &bases_info[i].z_max_q);
                f_box.insert(i, f_i);
            }
            boxes.push(f_box);
        }

        // Compute exact rational share `share(F_j) = prod_{i in P_j} (|F_{j, i}| / |A_i|)`.
        let a_counts: Vec<Int> = (0..t).map(|i| res_count(&allowed[i])).collect();
        let mut shares: Vec<(Int, Int)> = Vec::with_capacity(boxes.len());
        let mut total_share = (Int::ZERO, Int::ONE);
        for f_box in &boxes {
            let mut num = Int::ONE;
            let mut den = Int::ONE;
            for (&i, f_i) in f_box {
                num = &num * &res_count(f_i);
                den = &den * &a_counts[i];
            }
            let g = num.gcd_recursive(&den);
            let sh = (num.div_floor_wide(&g), den.div_floor_wide(&g));
            total_share = rat_add(&total_share, &sh);
            shares.push(sh);
        }

        // Check if `total_share < 1`:
        if total_share.0 < total_share.1
            && let Some(x_val) = find_point_by_conditional_expectations(
                lo,
                hi,
                &r0,
                &m0,
                bases_info,
                &fixed_base,
                &allowed,
                &a_counts,
                &boxes,
                &shares,
            )
        {
            return RegimeOut::Found(x_val);
        }

        if !allow_split {
            return RegimeOut::Undecided;
        }

        // Stage C: Single-base elementary-interval split across active bases `i`.
        let active_bases: Vec<usize> = (0..t).filter(|&i| fixed_base[i].is_none()).collect();
        for &i in &active_bases {
            let elem = elementary_intervals(&allowed[i], &boxes, i);
            let mut surviving: ResidueSet = Vec::new();
            for (el, eh) in elem {
                let mut sub_allowed = allowed.clone();
                sub_allowed[i] = vec![(el.clone(), eh.clone())];
                match solve_coprime_system(lo, hi, bases_info, sub_allowed, clauses.clone(), false)
                {
                    RegimeOut::Found(x) => return RegimeOut::Found(x),
                    RegimeOut::Empty => {}
                    RegimeOut::Undecided => surviving.push((el, eh)),
                }
            }
            let norm_surv = res_normalize(surviving, &bases_info[i].z_max_q);
            if norm_surv.is_empty() {
                return RegimeOut::Empty;
            }
            if norm_surv != allowed[i] {
                allowed[i] = norm_surv;
                allow_split = false;
                continue 'restart;
            }
        }

        return RegimeOut::Undecided;
    }
}

fn merge_pair_clauses(
    clauses: Vec<BTreeMap<usize, ResidueSet>>,
    allowed: &[ResidueSet],
) -> Vec<BTreeMap<usize, ResidueSet>> {
    let mut by_first: BTreeMap<(usize, usize, ResidueSet), ResidueSet> = BTreeMap::new();
    let mut others = Vec::new();
    for cl in clauses {
        let mut it = cl.iter();
        if let (2, Some((&i1, s1)), Some((&i2, s2))) = (cl.len(), it.next(), it.next()) {
            let e = by_first
                .entry((i1, i2, s1.clone()))
                .or_insert_with(|| allowed[i2].clone());
            *e = res_intersect(e, s2);
        } else {
            others.push(cl);
        }
    }
    for ((i1, i2, s1), s2) in by_first {
        let mut cl = BTreeMap::new();
        cl.insert(i1, s1);
        if !s2.is_empty() {
            cl.insert(i2, s2);
        }
        others.push(cl);
    }
    others
}

fn rat_add(a: &(Int, Int), b: &(Int, Int)) -> (Int, Int) {
    let num = &(&a.0 * &b.1) + &(&b.0 * &a.1);
    let den = &a.1 * &b.1;
    let g = num.gcd_recursive(&den);
    (num.div_floor_wide(&g), den.div_floor_wide(&g))
}

/// 1D Event-Point Method of Conditional Expectations to deterministically select a residue
/// `z_i in allowed[i]` for each unfixed base `i` when `total_share < 1`, then lift via CRT.
#[allow(clippy::too_many_arguments)]
fn find_point_by_conditional_expectations(
    lo: &Option<Int>,
    hi: &Option<Int>,
    r0: &Int,
    m0: &Int,
    bases_info: &[BaseInfo],
    fixed_base: &[Option<Int>],
    allowed: &[ResidueSet],
    a_counts: &[Int],
    boxes: &[BTreeMap<usize, ResidueSet>],
    shares: &[(Int, Int)],
) -> Option<Int> {
    let t = bases_info.len();
    let unfixed: Vec<usize> = (0..t).filter(|&i| fixed_base[i].is_none()).collect();
    if unfixed.is_empty() {
        return pick_in_span(lo, hi, r0, m0);
    }

    // Try selecting residues in forward order of `unfixed` and reverse order of `unfixed`.
    let rev_unfixed: Vec<usize> = unfixed.iter().copied().rev().collect();
    for order in [&unfixed, &rev_unfixed] {
        let mut chosen: Vec<Option<Int>> = fixed_base.to_vec();
        let mut active_boxes: Vec<usize> = (0..boxes.len()).collect();
        let mut weights: Vec<(Int, Int)> = shares.to_vec();

        for &i in order {
            let elem = elementary_intervals(&allowed[i], boxes, i);
            let mut best_z = elem[0].0.clone();
            let mut best_weight: Option<(Int, Int)> = None;

            for (el, _) in &elem {
                let mut w_sum = (Int::ZERO, Int::ONE);
                for &b_idx in &active_boxes {
                    let f_box = &boxes[b_idx];
                    if let Some(f_i) = f_box.get(&i) {
                        if res_contains(f_i, el) {
                            let f_cnt = res_count(f_i);
                            let num = &weights[b_idx].0 * &a_counts[i];
                            let den = &weights[b_idx].1 * &f_cnt;
                            let g = num.gcd_recursive(&den);
                            w_sum =
                                rat_add(&w_sum, &(num.div_floor_wide(&g), den.div_floor_wide(&g)));
                        }
                    } else {
                        w_sum = rat_add(&w_sum, &weights[b_idx]);
                    }
                }
                let better = match &best_weight {
                    None => true,
                    Some(bw) => &w_sum.0 * &bw.1 < &bw.0 * &w_sum.1,
                };
                if better {
                    best_weight = Some(w_sum);
                    best_z = el.clone();
                }
            }

            chosen[i] = Some(best_z.clone());
            // Update `active_boxes` and `weights`.
            let mut next_active = Vec::with_capacity(active_boxes.len());
            for b_idx in active_boxes {
                if let Some(f_i) = boxes[b_idx].get(&i) {
                    if res_contains(f_i, &best_z) {
                        let f_cnt = res_count(f_i);
                        let num = &weights[b_idx].0 * &a_counts[i];
                        let den = &weights[b_idx].1 * &f_cnt;
                        let g = num.gcd_recursive(&den);
                        weights[b_idx] = (num.div_floor_wide(&g), den.div_floor_wide(&g));
                        next_active.push(b_idx);
                    }
                } else {
                    next_active.push(b_idx);
                }
            }
            active_boxes = next_active;
        }

        // Combine all chosen residues via CRT:
        let mut pairs = vec![(r0.clone(), m0.clone())];
        for &i in order {
            let z_i = chosen.get(i)?.as_ref()?;
            pairs.push((bases_info[i].r_from_z(z_i), bases_info[i].max_q.clone()));
        }
        if let Some((r_full, m_full)) = combine_crt_tree(pairs)
            && let Some(x_val) = pick_in_span(lo, hi, &r_full, &m_full)
        {
            return Some(x_val);
        }

        // If `m_full` exceeded the finite span `hi - lo` so `r_full` missed `[lo, hi]`, check
        // `r0 + m0 * y` and incremental CRT prefixes with `y`-space short-period hole cutting.
        if let Some(x_cand) = find_point_in_y_span(lo, hi, r0, m0, bases_info, allowed, boxes) {
            return Some(x_cand);
        }
        if let (Some(l), Some(h)) = (lo, hi) {
            let span_width = h - l;
            let mut r_cur = r0.clone();
            let mut m_cur = m0.clone();
            for &i in order {
                if m_cur > span_width {
                    break;
                }
                let z_i = chosen.get(i)?.as_ref()?;
                let r_i = bases_info[i].r_from_z(z_i);
                let Some((rn, mn)) = combine_crt_pair(&r_cur, &m_cur, &r_i, &bases_info[i].max_q)
                else {
                    break;
                };
                r_cur = rn;
                m_cur = mn;
                if let Some(x_cand) =
                    find_point_in_y_span(lo, hi, &r_cur, &m_cur, bases_info, allowed, boxes)
                {
                    return Some(x_cand);
                }
            }
        }
    }
    None
}

fn find_point_in_y_span(
    lo: &Option<Int>,
    hi: &Option<Int>,
    r_cur: &Int,
    m_cur: &Int,
    bases_info: &[BaseInfo],
    allowed: &[ResidueSet],
    boxes: &[BTreeMap<usize, ResidueSet>],
) -> Option<Int> {
    if let Some(x_cand) = pick_in_span(lo, hi, r_cur, m_cur)
        && holds_coprime_boxes(&x_cand, bases_info, allowed, boxes)
    {
        return Some(x_cand);
    }
    let (Some(ly), Some(hy)) = y_span(lo, hi, r_cur, m_cur)? else {
        return None;
    };
    let width_y = &hy - &ly;
    let mut y_holes: Vec<Span> = Vec::new();
    for (k, info_k) in bases_info.iter().enumerate() {
        let z_q = &info_k.z_max_q;
        if *z_q <= width_y {
            continue;
        }
        let r_cur_z = (r_cur - &info_k.u).div_floor(&info_k.stride);
        let m_cur_z = m_cur.div_floor(&info_k.stride);
        let Some(inv_m) = inverse_mod(&m_cur_z, z_q) else {
            continue;
        };
        let u_inv = wide_remainder(&-&(&r_cur_z * &inv_m), z_q);
        let comp = res_complement(&allowed[k], z_q);
        if let Some(ry_forb) = map_affine_mod(&comp, &inv_m, &u_inv, z_q) {
            for (ry_a, ry_b) in ry_forb {
                for (hl, hh) in concrete_intervals_in_span(&ly, &hy, z_q, &ry_a, &ry_b) {
                    y_holes.push((Some(hl), Some(hh)));
                }
            }
        }
        for f_box in boxes {
            if let Some(f_k) = f_box.get(&k)
                && let Some(ry_forb) = map_affine_mod(f_k, &inv_m, &u_inv, z_q)
            {
                for (ry_a, ry_b) in ry_forb {
                    for (hl, hh) in concrete_intervals_in_span(&ly, &hy, z_q, &ry_a, &ry_b) {
                        y_holes.push((Some(hl), Some(hh)));
                    }
                }
            }
        }
    }
    if y_holes.is_empty() {
        return None;
    }
    let y_dom = Domain::range(ly, hy).intersect(&Domain::from_pieces(y_holes).complement());
    for (yl, _) in &y_dom.pieces {
        if let Some(y_val) = yl {
            let x_cand = r_cur + &(m_cur * y_val);
            if holds_coprime_boxes(&x_cand, bases_info, allowed, boxes) {
                return Some(x_cand);
            }
        }
    }
    None
}

/// Partition `allowed_i` at all endpoints of `{boxes[j][i]}` into elementary closed intervals
/// `[el, eh]` on which membership in every `boxes[j][i]` is constant.
fn elementary_intervals(
    allowed_i: &[(Int, Int)],
    boxes: &[BTreeMap<usize, ResidueSet>],
    i: usize,
) -> ResidueSet {
    let mut cuts: Vec<Int> = Vec::new();
    for f_box in boxes {
        if let Some(f_i) = f_box.get(&i) {
            for (lo, hi) in f_i {
                cuts.push(lo.clone());
                cuts.push(hi + &Int::ONE);
            }
        }
    }
    cuts.sort();
    cuts.dedup();

    let mut out = Vec::new();
    for (a_lo, a_hi) in allowed_i {
        let mut cur = a_lo.clone();
        for c in &cuts {
            if *c > cur && *c <= *a_hi {
                out.push((cur, c - &Int::ONE));
                cur = c.clone();
            }
        }
        if cur <= *a_hi {
            out.push((cur, a_hi.clone()));
        }
    }
    out
}

fn combine_crt_pair(r1: &Int, m1: &Int, r2: &Int, m2: &Int) -> Option<(Int, Int)> {
    let g = wide_gcd(m1, m2);
    let diff = r2 - r1;
    if !wide_remainder(&diff, &g).is_zero() {
        return None;
    }
    let m2_g = exact_quotient(m2, &g);
    let u = inverse_mod(&exact_quotient(m1, &g), &m2_g)?;
    let lcm = m1 * &m2_g;
    let step = wide_remainder(&(&exact_quotient(&diff, &g) * &u), &m2_g);
    let r = wide_remainder(&(r1 + &(m1 * &step)), &lcm);
    Some((r, lcm))
}

/// The solution `(r, m)` of `x == r_i (mod m_i)` for all `(r_i, m_i)` in `pairs`, `m` the lcm
/// of the `m_i`, or `None` when the congruences conflict. When the moduli are pairwise coprime
/// (always so for the bases of `solve_regime_step`), by the product and remainder trees:
/// `x = sum_i c_i M / m_i mod M` with `c_i = r_i (M / m_i)^-1 mod m_i`, the sum built up the
/// product tree as `v = v_left P_right + v_right P_left`, O(M(N) log k) for `k` moduli of `N`
/// bits, plus one inverse modulo each `m_i` ([`inverse_mod`], O(M(n) log n) for `n` bits).
///
/// When one modulus is not coprime to the product of the others, the pairs are combined two
/// at a time up a tree, each by a gcd, exact quotients and an inverse on the merged moduli
/// ([`combine_crt_pair`]), O(M(N) log N) at each level of the tree. Tests:
/// `one_scope::the_coprime_base_of_distinct_primes_scales`, `pncx_fibonacci_crt_scale`.
fn combine_crt_tree(mut pairs: Vec<(Int, Int)>) -> Option<(Int, Int)> {
    if pairs.is_empty() {
        return Some((Int::ZERO, Int::ONE));
    }
    pairs.retain(|(_, m)| *m != Int::ONE);
    if pairs.is_empty() {
        return Some((Int::ZERO, Int::ONE));
    }
    let tree = product_tree(pairs.iter().map(|(_, m)| m.clone()).collect());
    let cof = cofactors_mod_leaves(&tree);
    let mut vals: Option<Vec<Int>> = Some(Vec::with_capacity(pairs.len()));
    for ((r, m), e) in pairs.iter().zip(&cof) {
        let Some(inv) = inverse_mod(e, m) else {
            vals = None;
            break;
        };
        if let Some(v) = vals.as_mut() {
            v.push(wide_remainder(&(&wide_remainder(r, m) * &inv), m));
        }
    }
    if let Some(mut vals) = vals {
        for prods in &tree[..tree.len() - 1] {
            vals = vals
                .chunks(2)
                .zip(prods.chunks(2))
                .map(|(v, p)| {
                    if v.len() == 2 {
                        &(&v[0] * &p[1]) + &(&v[1] * &p[0])
                    } else {
                        v[0].clone()
                    }
                })
                .collect();
        }
        let big_m = tree.last()?.first()?.clone();
        return Some((vals.first()?.mod_floor_wide(&big_m), big_m));
    }
    while pairs.len() > 1 {
        let mut next = Vec::with_capacity(pairs.len().div_ceil(2));
        let mut it = pairs.into_iter();
        while let Some((r1, m1)) = it.next() {
            if let Some((r2, m2)) = it.next() {
                next.push(combine_crt_pair(&r1, &m1, &r2, &m2)?);
            } else {
                next.push((r1, m1));
            }
        }
        pairs = next;
    }
    pairs.pop()
}

fn y_span(lo: &Option<Int>, hi: &Option<Int>, r0: &Int, m0: &Int) -> Option<Span> {
    let lo_y = lo.as_ref().map(|l| -(&(r0 - l).div_floor_wide(m0)));
    let hi_y = hi.as_ref().map(|h| (h - r0).div_floor_wide(m0));
    if let (Some(ly), Some(hy)) = (&lo_y, &hi_y)
        && ly > hy
    {
        return None;
    }
    Some((lo_y, hi_y))
}

fn pick_in_span(lo: &Option<Int>, hi: &Option<Int>, r0: &Int, m0: &Int) -> Option<Int> {
    if let Some(l) = lo
        && *l > Int::ZERO
    {
        let x = l + &(r0 - l).mod_floor_wide(m0);
        return hi.as_ref().is_none_or(|h| x <= *h).then_some(x);
    }
    if let Some(h) = hi
        && *h < Int::ZERO
    {
        let x = h - &(h - r0).mod_floor_wide(m0);
        return lo.as_ref().is_none_or(|l| x >= *l).then_some(x);
    }
    let r_pos = r0.mod_floor_wide(m0);
    if hi.as_ref().is_none_or(|h| r_pos <= *h) {
        return Some(r_pos);
    }
    let r_neg = &r_pos - m0;
    if lo.as_ref().is_none_or(|l| r_neg >= *l) {
        return Some(r_neg);
    }
    None
}

fn holds_coprime_point(
    x: &Int,
    bases_info: &[BaseInfo],
    allowed: &[ResidueSet],
    clauses: &[BTreeMap<usize, ResidueSet>],
) -> bool {
    let mut z_vals = Vec::with_capacity(bases_info.len());
    for (i, info) in bases_info.iter().enumerate() {
        let Some(z) = info.z_from_x(x) else {
            return false;
        };
        if !res_contains(&allowed[i], &z) {
            return false;
        }
        z_vals.push(z);
    }
    for cl in clauses {
        if !cl.iter().any(|(&i, s)| res_contains(s, &z_vals[i])) {
            return false;
        }
    }
    true
}

fn holds_coprime_boxes(
    x: &Int,
    bases_info: &[BaseInfo],
    allowed: &[ResidueSet],
    boxes: &[BTreeMap<usize, ResidueSet>],
) -> bool {
    let mut z_vals = Vec::with_capacity(bases_info.len());
    for (i, info) in bases_info.iter().enumerate() {
        let Some(z) = info.z_from_x(x) else {
            return false;
        };
        if !res_contains(&allowed[i], &z) {
            return false;
        }
        z_vals.push(z);
    }
    for f_box in boxes {
        if f_box.iter().all(|(&i, f_i)| res_contains(f_i, &z_vals[i])) {
            return false;
        }
    }
    true
}

#[allow(clippy::too_many_arguments)]
fn build_model(
    x_root: &Atom,
    x_val: &Int,
    all_atoms: &BTreeSet<Atom>,
    fixed: &HashMap<Atom, Int>,
    uf: &UnitUf,
    rem_defs: &HashMap<Atom, FullRemDef>,
    global_quots: &HashMap<Atom, GlobalQuot>,
    local_windows: &HashMap<Atom, Vec<LocalWindow>>,
) -> Model {
    let mut model = Model::new();
    model.insert(x_root.clone(), x_val.clone());

    for (a, v) in fixed {
        model.insert(a.clone(), v.clone());
    }

    // Global quotients `q_root`:
    for (q_root, gq) in global_quots {
        let sx_val = if gq.s_x > 0 { x_val.clone() } else { -x_val };
        let q_div = (&sx_val + &gq.c_lo).div_floor_wide(&gq.m);
        let q_val = if gq.sigma_q > 0 { q_div } else { -&q_div };
        model.insert(q_root.clone(), q_val);
    }

    // Local existential quotients `q_root`:
    for (q_root, wins) in local_windows {
        let mut chosen_q = Int::ZERO;
        for lw in wins {
            let sx_val = if lw.s_x > 0 { x_val.clone() } else { -x_val };
            let u = &sx_val + &lw.c_lo;
            if u.mod_floor_wide(&lw.m) <= lw.w {
                let q_div = u.div_floor_wide(&lw.m);
                chosen_q = if lw.sigma_q > 0 { q_div } else { -&q_div };
                break;
            }
        }
        model.insert(q_root.clone(), chosen_q);
    }

    // Three-term remainders `r_root`:
    for (r_root, rem) in rem_defs {
        let q_val = model.get(&rem.q_root).cloned().unwrap_or(Int::ZERO);
        let sum = &(&(&rem.c_x * x_val) + &(&rem.c_q * &q_val)) + &rem.k;
        let r_val = if rem.c_r > 0 { -&sum } else { sum };
        model.insert(r_root.clone(), r_val);
    }

    // Propagate unit-equality classes `a = s * root + d`:
    for a in all_atoms {
        if model.contains_key(a) {
            continue;
        }
        let (root, s, d) = uf.get(a);
        let root_val = model.get(&root).cloned().unwrap_or(Int::ZERO);
        let val = if s > 0 {
            &root_val + &d
        } else {
            &d - &root_val
        };
        model.insert(a.clone(), val);
    }

    model
}
// Clauses of two moduli grouped by their span and moduli, each with its two residues.
type PairGroups<'a> = BTreeMap<(Option<&'a Span>, &'a Int, &'a Int), Vec<(&'a Int, &'a Int)>>;

/// The bounds that triples of clauses force (Codex's R3-CODEX-6, proved there): three clauses
/// `x mod a == a_j || x mod b == b_j || x in D`, with one interval or empty `D`, the three `a_j` distinct
/// and the three `b_j` distinct, force `x` into `D`, since outside `D` the one value of `x mod a`
/// and the one of `x mod b` satisfy at most two of them. Clauses are grouped by `(D, a, b)`; a
/// group tests for a matching of three pairs, independently of the order in which
/// the clauses were written. O(c log c) operations for c clauses.
///
/// Complexity tradeoff: without this bound the walk visits every regime below `D` on the
/// regimes3 family (23x per 8x, Gemini's round-3 control); it finds only bounds forced by three
/// two-modulus clauses, not every implied bound. Test: the regimes3 axis of `pncx_probe`.
fn forced_pair_bounds(clauses: &[FlatClause]) -> Domain {
    let mut groups: PairGroups<'_> = BTreeMap::new();
    for cl in clauses {
        if cl.mods.len() != 2 {
            continue;
        }
        let mut lits = cl.mods.iter();
        let (Some((a, sa)), Some((b, sb))) = (lits.next(), lits.next()) else {
            continue;
        };
        // Complexity tradeoff: the empty bound used to skip the same
        // three-clause contradiction, leaving all later cuts to the walk.
        // Include it in the existing O(c log c) grouping; a matching then
        // proves there is no point. No additional refinement is needed.
        // Tests: pncx_empty_pair_implication and pncx_bound_matching_scale.
        let span = match cl.bounds.pieces.as_slice() {
            [] => None,
            [span] => Some(span),
            _ => continue,
        };
        let ([(ra, ra_hi)], [(rb, rb_hi)]) = (sa.as_slice(), sb.as_slice()) else {
            continue;
        };
        if ra == ra_hi && rb == rb_hi {
            groups.entry((span, a, b)).or_default().push((ra, rb));
        }
    }
    let (mut lo, mut hi) = (None, None);
    for ((span, _, _), pairs) in groups {
        if three_disjoint_pairs(&pairs) {
            let Some(span) = span else {
                return Domain::empty();
            };
            lo = max_lo(lo, span.0.clone());
            hi = min_hi(hi, span.1.clone());
        }
    }
    Domain::from_pieces(vec![(lo, hi)])
}

/// Whether three edges have distinct endpoints on each side.
// Complexity tradeoff: greedily keeping disjoint pairs can miss a triple
// depending on input order, e.g. (0,0),(0,1),(1,0),(2,2). Testing every triple
// costs O(c^3). Three augmenting-path passes find the required matching in
// O(c) graph operations after O(c log c) indexing. Nothing previously forced
// is lost. Three is the number in the implication, not an input-size limit.
// Tests: pncx_bound_matching_is_order_independent, pncx_bound_matching_scale.
fn three_disjoint_pairs(pairs: &[(&Int, &Int)]) -> bool {
    let left: BTreeSet<_> = pairs.iter().map(|p| p.0).collect();
    let right: BTreeSet<_> = pairs.iter().map(|p| p.1).collect();
    let left: BTreeMap<_, _> = left.into_iter().enumerate().map(|(i, v)| (v, i)).collect();
    let right: BTreeMap<_, _> = right.into_iter().enumerate().map(|(i, v)| (v, i)).collect();
    let mut adjacent = vec![Vec::new(); left.len()];
    for (a, b) in pairs {
        let (Some(&a), Some(&b)) = (left.get(a), right.get(b)) else {
            return false;
        };
        adjacent[a].push(b);
    }
    let (mut lm, mut rm): (Vec<Option<usize>>, Vec<Option<usize>>) =
        (vec![None; left.len()], vec![None; right.len()]);
    for _ in 0..3 {
        let mut seen = vec![false; left.len()];
        let mut parent = vec![None; right.len()];
        let mut todo = VecDeque::new();
        for a in 0..left.len() {
            if lm[a].is_none() {
                seen[a] = true;
                todo.push_back(a);
            }
        }
        let mut target = None;
        'walk: while let Some(a) = todo.pop_front() {
            for &b in &adjacent[a] {
                if parent[b].is_some() {
                    continue;
                }
                parent[b] = Some(a);
                match rm[b] {
                    None => {
                        target = Some(b);
                        break 'walk;
                    }
                    Some(a) if !seen[a] => {
                        seen[a] = true;
                        todo.push_back(a);
                    }
                    Some(_) => {}
                }
            }
        }
        let Some(mut b) = target else {
            return false;
        };
        while let Some(a) = parent[b] {
            let old = lm[a];
            lm[a] = Some(b);
            rm[b] = Some(a);
            match old {
                Some(previous) => b = previous,
                None => break,
            }
        }
    }
    true
}

/// Two clauses on each separate pair have a direct sufficient witness: meet the first
/// clause on its first divisor and the second on its second divisor. CRT combines these
/// choices without refining the divisors or splitting combinations. There are O(c log c)
/// map operations for c clauses and a balanced CRT tree; integer costs are those of CRT.
/// Failure to build this witness says nothing about the other choices.
fn separate_pair_witness(
    lo: &Option<Int>,
    hi: &Option<Int>,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> Option<Int> {
    if !unit_mods.is_empty() || clauses.is_empty() {
        return None;
    }
    let mut groups: BTreeMap<(&Int, &Int), Vec<&BTreeMap<Int, ResidueSet>>> = BTreeMap::new();
    for cl in clauses {
        if cl.len() != 2 {
            return None;
        }
        let mut keys = cl.keys();
        let a = keys.next()?;
        let b = keys.next()?;
        groups.entry((a, b)).or_default().push(cl);
    }
    let mut used = BTreeSet::new();
    let mut pairs = Vec::with_capacity(groups.len());
    for ((a, b), cs) in groups {
        if cs.len() != 2 || !used.insert(a) || !used.insert(b) {
            return None;
        }
        pairs.push((a, &cs[0][a], b, &cs[1][b]));
    }
    // The residue chosen on each divisor is the first permitted one at or above `lo`, or the
    // last at or below `hi`, never the first in the coordinate's own order: that order follows
    // the root the names choose (I4.15). With no bound every choice gives a point.
    let anchored = |pick: &dyn Fn(&Int, &ResidueSet) -> Option<Int>| -> Option<Int> {
        let mut choices = Vec::with_capacity(2 * pairs.len());
        for (a, sa, b, sb) in &pairs {
            choices.push((pick(a, sa)?.mod_floor_wide(a), (*a).clone()));
            choices.push((pick(b, sb)?.mod_floor_wide(b), (*b).clone()));
        }
        let (r, m) = combine_crt_tree(choices)?;
        let x = pick_in_span(lo, hi, &r, &m)?;
        holds_modular_point(&x, unit_mods, clauses).then_some(x)
    };
    match (lo, hi) {
        (None, None) => anchored(&|_, s| s.first().map(|(r, _)| r.clone())),
        _ => lo
            .as_ref()
            .and_then(|l| anchored(&|m, s| first_residue_at(l, m, s)))
            .or_else(|| {
                hi.as_ref()
                    .and_then(|h| anchored(&|m, s| last_residue_at(h, m, s)))
            }),
    }
}
struct ScalarWitness<'a> {
    x_root: &'a Atom,
    x_val: &'a Int,
    fixed: &'a HashMap<Atom, Int>,
    uf: &'a UnitUf,
    rem_defs: &'a HashMap<Atom, FullRemDef>,
    global_quots: &'a HashMap<Atom, GlobalQuot>,
    local_windows: &'a HashMap<Atom, Vec<LocalWindow>>,
}

impl ScalarWitness<'_> {
    fn quotient(&self, a: &Atom) -> Int {
        if let Some(wins) = self.local_windows.get(a) {
            for lw in wins {
                let sx = if lw.s_x > 0 {
                    self.x_val.clone()
                } else {
                    -self.x_val
                };
                let u = &sx + &lw.c_lo;
                if u.mod_floor_wide(&lw.m) <= lw.w {
                    let q = u.div_floor_wide(&lw.m);
                    return if lw.sigma_q > 0 { q } else { -&q };
                }
            }
            return Int::ZERO;
        }
        if let Some(gq) = self.global_quots.get(a) {
            let sx = if gq.s_x > 0 {
                self.x_val.clone()
            } else {
                -self.x_val
            };
            let q = (&sx + &gq.c_lo).div_floor_wide(&gq.m);
            return if gq.sigma_q > 0 { q } else { -&q };
        }
        if let Some(v) = self.fixed.get(a) {
            return v.clone();
        }
        if a == self.x_root {
            return self.x_val.clone();
        }
        Int::ZERO
    }

    fn root(&self, a: &Atom) -> Int {
        if let Some(rem) = self.rem_defs.get(a) {
            let q = self.quotient(&rem.q_root);
            let sum = &(&(&rem.c_x * self.x_val) + &(&rem.c_q * &q)) + &rem.k;
            return if rem.c_r > 0 { -&sum } else { sum };
        }
        self.quotient(a)
    }

    fn atom(&self, a: &Atom) -> Int {
        if self.rem_defs.contains_key(a)
            || self.local_windows.contains_key(a)
            || self.global_quots.contains_key(a)
            || self.fixed.contains_key(a)
            || a == self.x_root
        {
            return self.root(a);
        }
        let (root, s, d) = self.uf.get(a);
        let v = self.root(&root);
        if s > 0 { &v + &d } else { &d - &v }
    }

    fn holds(&self, f: &Formula) -> bool {
        // Complexity tradeoff: reconstructing k quotients of a B-bit point
        // writes O(k B) temporary bits even for a Boolean answer. Batch the
        // remainders in a product/remainder tree, then cancel quotient terms
        // algebraically when their coefficients are multiples of the divisor.
        // The tree costs O(M(B + S) log k) bit operations for S modulus bits;
        // unmatched constraints retain direct evaluation, with no verdict lost.
        // Tests: pncx_pairs_scale and the enumeration suites. Negative control:
        // evaluating every constraint directly fails the large pairs scale.
        let specs = self.quotient_specs();
        f.fold(
            (),
            |_, ()| (),
            |g, (), values: Vec<bool>| match g {
                Formula::Con(c) => {
                    if let Some(specs) = &specs
                        && let Some(v) = self.reduced_value(c, specs)
                    {
                        return match c.rel {
                            Rel::Eq => v.is_zero(),
                            Rel::Ge => !v.is_negative(),
                        };
                    }
                    let v = c
                        .lin
                        .terms
                        .iter()
                        .fold(c.lin.constant.clone(), |v, (a, k)| {
                            &v + &(k * &self.atom(a))
                        });
                    match c.rel {
                        Rel::Eq => v.is_zero(),
                        Rel::Ge => !v.is_negative(),
                    }
                }
                Formula::And(_) => values.into_iter().all(|v| v),
                Formula::Or(_) => values.into_iter().any(|v| v),
                Formula::Not(_) => !values[0],
            },
        )
    }

    fn quotient_specs(&self) -> Option<HashMap<Atom, Option<QuotientValue>>> {
        // Fixed values and extracted quotient/remainder roots must have the
        // same precedence as atom(). Otherwise use its direct evaluation.
        for a in self
            .rem_defs
            .keys()
            .chain(self.global_quots.keys())
            .chain(self.local_windows.keys())
        {
            if self.fixed.contains_key(a) || self.uf.get(a).0 != *a {
                return None;
            }
        }
        let moduli: Vec<_> = self
            .global_quots
            .values()
            .map(|q| q.m.clone())
            .chain(self.local_windows.values().flatten().map(|q| q.m.clone()))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let rems = batch_remainders(self.x_val, &moduli);
        let remainder = |m: &Int| moduli.binary_search(m).ok().and_then(|i| rems.get(i));
        let mut specs = HashMap::new();
        for (a, q) in self.global_quots {
            let xm = remainder(&q.m)?;
            let sx = if q.s_x > 0 { xm.clone() } else { -xm };
            let r = (&sx + &q.c_lo).mod_floor_wide(&q.m);
            specs.insert(
                a.clone(),
                Some(QuotientValue {
                    sx: q.s_x,
                    c: q.c_lo.clone(),
                    sigma: q.sigma_q,
                    m: q.m.clone(),
                    r,
                }),
            );
        }
        for (a, wins) in self.local_windows {
            let mut chosen = None;
            for q in wins {
                let xm = remainder(&q.m)?;
                let sx = if q.s_x > 0 { xm.clone() } else { -xm };
                let r = (&sx + &q.c_lo).mod_floor_wide(&q.m);
                if r <= q.w {
                    chosen = Some(QuotientValue {
                        sx: q.s_x,
                        c: q.c_lo.clone(),
                        sigma: q.sigma_q,
                        m: q.m.clone(),
                        r,
                    });
                    break;
                }
            }
            specs.insert(a.clone(), chosen);
        }
        Some(specs)
    }

    fn reduced_value(&self, c: &Con, specs: &HashMap<Atom, Option<QuotientValue>>) -> Option<Int> {
        let lin = rewrite_lin_full(&c.lin, self.fixed, self.uf, self.rem_defs);
        let mut value = lin.constant;
        let mut cx = Int::ZERO;
        for (a, k) in lin.terms {
            if &a == self.x_root {
                cx = &cx + &k;
                continue;
            }
            let Some(q) = specs.get(&a)? else {
                continue;
            };
            let divisor = if q.sigma > 0 { q.m.clone() } else { -&q.m };
            if !k.mod_floor_wide(&divisor).is_zero() {
                return None;
            }
            let t = k.div_floor_wide(&divisor);
            cx = if q.sx > 0 { &cx + &t } else { &cx - &t };
            value = &value + &(&t * &(&q.c - &q.r));
        }
        if !cx.is_zero() {
            value = &value + &(&cx * self.x_val);
        }
        Some(value)
    }
}

struct QuotientValue {
    sx: i8,
    c: Int,
    sigma: i8,
    m: Int,
    r: Int,
}

fn batch_remainders(x: &Int, moduli: &[Int]) -> Vec<Int> {
    if moduli.is_empty() {
        return Vec::new();
    }
    // When the point's magnitude is below every divisor, the remainder is
    // already known. This is an algebraic case, independent of bit width.
    if moduli.iter().min().is_some_and(|m| x.abs() < *m) {
        return moduli
            .iter()
            .map(|m| if x.is_negative() { m + x } else { x.clone() })
            .collect();
    }
    let tree = product_tree(moduli.to_vec());
    let Some(root) = tree.last().and_then(|level| level.first()) else {
        return Vec::new();
    };
    let mut rems = vec![wide_remainder(x, root)];
    for level in tree[..tree.len() - 1].iter().rev() {
        rems = level
            .iter()
            .enumerate()
            .map(|(i, m)| wide_remainder(&rems[i / 2], m))
            .collect();
    }
    rems
}

fn wide_remainder(a: &Int, m: &Int) -> Int {
    if !a.is_negative() && a < m {
        return a.clone();
    }
    if let (Some(_), Some(_)) = (a.to_i128(), m.to_i128()) {
        return a.mod_floor(m);
    }
    // Complexity tradeoff: quadratic long division in Int::mod_floor is
    // replaced by the kernel's subquadratic remainder, O(M(B)), without an
    // unused quotient. The operands are written integers; a failed conversion
    // retains the original exact operation. Test: pncx_batch_remainders_match.
    let an = zedc_int::int::Num::from(a);
    let mn = zedc_int::int::Num::from(m);
    match (an.built(), mn.built()) {
        (Ok(ab), Ok(mb)) => {
            let r = Int::from(num_bigint::BigInt::from(zed_kernel::num::rem_uint(
                ab.magnitude(),
                mb.magnitude(),
            )));
            if a.is_negative() && !r.is_zero() {
                m - &r
            } else {
                r
            }
        }
        _ => a.mod_floor_wide(m),
    }
}

/// `a^-1 mod m` for `m` above zero, in `[0, m)`, or `None` when `gcd(a, m) != 1`.
///
/// Complexity tradeoff: the Euclidean `bezout` is O(n^2) on `n`-bit moduli, two Fibonacci
/// neighbours being its slowest case (`pncx_fibonacci_crt_scale`, 77.9 times the work for 8
/// times the width, R6-CLAUDE-7); the kernel's binary half gcd with its steps kept
/// (`zed_kernel::num::inverse_mod_uint`) is O(M(n) log n). A value that cannot be built keeps
/// the Euclidean `bezout`, as do values that fit in 128 bits, which keep the arithmetic they
/// had; the inverse is the same.
fn inverse_mod(a: &Int, m: &Int) -> Option<Int> {
    if let (Some(_), Some(_)) = (a.to_i128(), m.to_i128()) {
        let (g, u, _) = a.mod_floor(m).extended_gcd(m)?;
        return (g == Int::ONE).then(|| u.mod_floor(m));
    }
    let a = wide_remainder(a, m);
    let an = zedc_int::int::Num::from(&a);
    let mn = zedc_int::int::Num::from(m);
    match (an.built(), mn.built()) {
        (Ok(ab), Ok(mb)) => zed_kernel::num::inverse_mod_uint(ab.magnitude(), mb.magnitude())
            .map(|x| Int::from(num_bigint::BigInt::from(x))),
        _ => {
            let (g, u, _) = a.extended_gcd(m)?;
            (g == Int::ONE).then(|| u.mod_floor(m))
        }
    }
}

/// The greatest common divisor of `a` and `b`, never negative, by the kernel's half gcd
/// (`zed_kernel::num::gcd_uint`), O(M(n) log n), where `Int::gcd` on wide values is the
/// binary gcd of num-integer, O(n^2).
fn wide_gcd(a: &Int, b: &Int) -> Int {
    if let (Some(_), Some(_)) = (a.to_i128(), b.to_i128()) {
        return a.gcd(b);
    }
    let an = zedc_int::int::Num::from(a);
    let bn = zedc_int::int::Num::from(b);
    match (an.built(), bn.built()) {
        (Ok(ab), Ok(bb)) => Int::from(num_bigint::BigInt::from(zed_kernel::num::gcd_uint(
            ab.magnitude(),
            bb.magnitude(),
        ))),
        _ => a.gcd(b),
    }
}

/// `a / d` for `d` above zero dividing `a`, by the kernel's division
/// (`zed_kernel::num::div_rem_uint`), O(M(n)), where `Int::div_floor` on wide values is long
/// division, O(n^2).
fn exact_quotient(a: &Int, d: &Int) -> Int {
    if let (Some(_), Some(_)) = (a.to_i128(), d.to_i128()) {
        return a.div_floor(d);
    }
    let an = zedc_int::int::Num::from(a);
    let dn = zedc_int::int::Num::from(d);
    match (an.built(), dn.built()) {
        (Ok(ab), Ok(db)) => {
            let q = Int::from(num_bigint::BigInt::from(
                zed_kernel::num::div_rem_uint(ab.magnitude(), db.magnitude()).0,
            ));
            if a.is_negative() { -&q } else { q }
        }
        _ => a.div_floor(d),
    }
}

/// Intersect a collection without repeatedly scanning an accumulated result.
fn intersect_domains(mut domains: Vec<Domain>) -> Domain {
    while domains.len() > 1 {
        let mut next = Vec::with_capacity(domains.len().div_ceil(2));
        let mut it = domains.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) => a.intersect(&b),
                None => a,
            });
        }
        domains = next;
    }
    domains.pop().unwrap_or_else(Domain::all)
}

/// Intersect a nonempty collection of normalized residue sets by balanced halves.
fn intersect_residue_sets(mut sets: Vec<ResidueSet>) -> ResidueSet {
    while sets.len() > 1 {
        let mut next = Vec::with_capacity(sets.len().div_ceil(2));
        let mut it = sets.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) => res_intersect(&a, &b),
                None => a,
            });
        }
        sets = next;
    }
    sets.pop().unwrap_or_default()
}

#[cfg(test)]
mod r4_tests;

/// The first point at least `lo` permitted by a single residue condition.
fn first_residue_at(lo: &Int, m: &Int, s: &[(Int, Int)]) -> Option<Int> {
    let r = lo.mod_floor_wide(m);
    let i = s.partition_point(|(_, b)| b < &r);
    if let Some((a, _)) = s.get(i) {
        Some(if &r >= a { lo.clone() } else { lo + &(a - &r) })
    } else {
        s.first().map(|(a, _)| lo + &(&(m - &r) + a))
    }
}

/// The maximum of the individual lower bounds is necessary, not sufficient.
/// Accept it only after checking every constraint on that point.
fn lower_witness(
    lo: &Int,
    hi: &Option<Int>,
    units: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> Option<Int> {
    let mut x = lo.clone();
    for (m, s) in units {
        x = x.max(first_residue_at(lo, m, s)?);
    }
    for cl in clauses {
        let first = cl
            .iter()
            .filter_map(|(m, s)| first_residue_at(lo, m, s))
            .min()?;
        x = x.max(first);
    }
    if hi.as_ref().is_some_and(|h| &x > h) {
        return None;
    }
    holds_modular_point(&x, units, clauses).then_some(x)
}

/// The last point at most `hi` permitted by a single residue condition.
fn last_residue_at(hi: &Int, m: &Int, s: &[(Int, Int)]) -> Option<Int> {
    let r = hi.mod_floor_wide(m);
    let i = s.partition_point(|(a, _)| a <= &r);
    if let Some(i) = i.checked_sub(1) {
        let (_, b) = &s[i];
        Some(if &r <= b { hi.clone() } else { hi - &(&r - b) })
    } else {
        s.last().map(|(_, b)| hi - &(&(&r + m) - b))
    }
}

/// The mirror of [`lower_witness`]: the minimum of the individual upper bounds below `hi`,
/// accepted only after checking every constraint on that point. With it the witnesses tried do
/// not change when the coordinate's sign does (I4.15).
fn upper_witness(
    lo: &Option<Int>,
    hi: &Int,
    units: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> Option<Int> {
    let mut x = hi.clone();
    for (m, s) in units {
        x = x.min(last_residue_at(hi, m, s)?);
    }
    for cl in clauses {
        let last = cl
            .iter()
            .filter_map(|(m, s)| last_residue_at(hi, m, s))
            .max()?;
        x = x.min(last);
    }
    if lo.as_ref().is_some_and(|l| &x < l) {
        return None;
    }
    holds_modular_point(&x, units, clauses).then_some(x)
}

#[cfg(test)]
mod r6_tests;

#[cfg(test)]
mod r7_tests;
