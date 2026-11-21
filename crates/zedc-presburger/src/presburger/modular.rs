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

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use zed_collections::intervals;
use zed_graph::MinHeap;
use zed_kernel::num::{coprime, mul_uint, rem_uint, trees};
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

    fn from_pieces(pieces: Vec<Span>) -> Self {
        Domain {
            pieces: intervals::coalesce(pieces),
        }
    }

    // Complexity tradeoff: the two lists joined and coalesced sort them again, O(n log n); both
    // are normal, so one merge by lower end, O(n), gives the same list.
    fn union(&self, other: &Self) -> Self {
        Domain {
            pieces: intervals::union(&self.pieces, &other.pieces),
        }
    }

    fn complement(&self) -> Self {
        Domain {
            pieces: intervals::complement_spans(&self.pieces),
        }
    }

    fn intersect(&self, other: &Self) -> Self {
        Domain {
            pieces: intervals::intersect(&self.pieces, &other.pieces),
        }
    }

    fn contains_span(&self, lo: &Option<Int>, hi: &Option<Int>) -> bool {
        // Complexity tradeoff: scanning s disjoint intervals for each point
        // costs O(s) per lookup. Their sorted starts locate the only possible
        // containing interval in O(log s) comparisons. Nothing is given up for
        // the nonempty spans callers pass. Tests: pncx_domain_membership_scale
        // (the scan fails) and pncx_domain_membership_matches_scan.
        // `Option`'s order puts `None` first, as an unbounded lower end must be.
        let end = self.pieces.partition_point(|(l, _)| l <= lo);
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

/// Normalizes a collection of closed intervals, clipped to `0..m`, into a sorted, disjoint,
/// non-adjacent `ResidueSet`.
fn res_normalize(mut intervals: Vec<(Int, Int)>, m: &Int) -> ResidueSet {
    let max_r = m - &Int::ONE;
    for (l, h) in &mut intervals {
        if *l < Int::ZERO {
            *l = Int::ZERO;
        }
        if *h > max_r {
            *h = max_r.clone();
        }
    }
    // An interval wholly outside `0..m` is empty once clipped, and `coalesce` drops it.
    intervals::coalesce(intervals)
}

/// The residues of `0..m` outside `s`, sorted by lower end (overlapping or nested intervals are
/// read correctly, DRY-sorted-structures D2).
fn res_complement(s: &[(Int, Int)], m: &Int) -> ResidueSet {
    intervals::complement(s, Int::ZERO, m - &Int::ONE)
}

/// The union of the residue sets `a` and `b`, clipped to `0..m`.
// Complexity tradeoff: the two joined and normalized sort them again, O(n log n); a residue
// set is sorted by lower end (each is built by the functions of this section, all of which
// return normal lists, or is a single interval), so one merge, O(n), gives the same list, and
// the meet with `0..m` clips it as `res_normalize` did.
fn res_union(a: &[(Int, Int)], b: &[(Int, Int)], m: &Int) -> ResidueSet {
    debug_assert!(a.is_sorted_by(|x, y| x.0 <= y.0) && b.is_sorted_by(|x, y| x.0 <= y.0));
    intervals::intersect(&intervals::union(a, b), &[(Int::ZERO, m - &Int::ONE)])
}

fn res_intersect(a: &[(Int, Int)], b: &[(Int, Int)]) -> ResidueSet {
    intervals::intersect(a, b)
}

fn res_diff(a: &[(Int, Int)], b: &[(Int, Int)], m: &Int) -> ResidueSet {
    intervals::intersect(a, &res_complement(b, m))
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

/// Whether every residue of `inner` lies in `outer`, both sorted and disjoint in `0..m`: no gap
/// of `outer` meets `inner`. Each gap is tested against the last run of `inner` that starts
/// in it or before it: the runs before that one end before it starts. O(g log u) for `g` gaps
/// of `outer` and `u` runs of `inner`.
fn res_within(inner: &[(Int, Int)], outer: &[(Int, Int)], m: &Int) -> bool {
    res_complement(outer, m).iter().all(|(gap_lo, gap_hi)| {
        let i = inner.partition_point(|(lo, _)| lo <= gap_hi);
        i == 0 || inner[i - 1].1 < *gap_lo
    })
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
        ((a - c_lo).mod_floor(m), (b - c_lo).mod_floor(m))
    } else {
        ((c_lo - b).mod_floor(m), (c_lo - a).mod_floor(m))
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

/// Union-Find with affine potentials `atom = sign * parent + offset`, `sign in {-1, 1}`,
/// linking by subtree size without compressing edge offsets.
// Complexity tradeoff: naive path compression (`find`/`flatten`) rewrites every atom's edge
// directly to the root, copying a single `B`-bit written offset onto `Omega(n)` atoms in
// `O(n * B)` time and bytes (`r6_tests::pncx_wide_affine_alias_scale`: 50.6x bytes and 13.4x
// instructions for 8x size, 391.9 MB at n = 1024). Linking by subtree size without compressing
// offsets keeps tree height at most `floor(log2 n)` (Tarjan and van Leeuwen 1984,
// doi:10.1145/62.2160, read 2026-11-21: sec. 2, Lemma 1, size >= 2^height, and Corollary 2;
// the proof is sketched in the crate's `lib.rs`, "References", and the full comment is in
// zed-graph `union_find.rs`) while leaving
// every edge offset stored on a single tree edge (O(S) total stored bits for total input
// bit-length S). Dense `usize` indices keep tree walks and LCA queries allocation-free without
// `HashMap` lookups or `Atom` clones; LCA cancellation in `rewrite_lin_full` and `union` avoids
// crossing any wide edge above the LCA of cancelling terms. Nothing is given up: `get`
// re-anchors to the smallest `Atom` (`canon`) in O(log n) hops for callers expecting canonical
// roots, while `solve_modular_whole` works over balanced internal tree roots (invariant under
// renaming via `solve_regime`). Tests: `pncx_wide_affine_alias_scale`,
// `pncx_affine_alias_chain_scale`, `pncx_alias_chain_axis`,
// `one_scope::one_variable_answers_do_not_depend_on_names`.
struct UnitUf {
    ids: HashMap<Atom, usize>,
    atoms: Vec<Atom>,
    parent: Vec<usize>,
    sign: Vec<i8>,
    offset: Vec<Int>,
    size: Vec<usize>,
    /// Index of the smallest `Atom` (by `Ord`) in this component, stored at each tree root.
    canon: Vec<usize>,
}

impl UnitUf {
    fn new() -> Self {
        UnitUf {
            ids: HashMap::new(),
            atoms: Vec::new(),
            parent: Vec::new(),
            sign: Vec::new(),
            offset: Vec::new(),
            size: Vec::new(),
            canon: Vec::new(),
        }
    }

    fn ensure_id(&mut self, a: &Atom) -> usize {
        if let Some(&id) = self.ids.get(a) {
            return id;
        }
        let id = self.atoms.len();
        self.ids.insert(a.clone(), id);
        self.atoms.push(a.clone());
        self.parent.push(id);
        self.sign.push(1);
        self.offset.push(Int::ZERO);
        self.size.push(1);
        self.canon.push(id);
        id
    }

    fn ensure(&mut self, a: &Atom) {
        self.ensure_id(a);
    }

    fn root_and_depth_id(&self, mut u: usize) -> (usize, usize) {
        let mut d = 0usize;
        while self.parent[u] != u {
            u = self.parent[u];
            d += 1;
        }
        (u, d)
    }

    fn tree_root_id(&self, mut u: usize) -> usize {
        while self.parent[u] != u {
            u = self.parent[u];
        }
        u
    }

    /// The balanced tree root of `a` (pointer hops only, no integer arithmetic).
    fn tree_root(&self, a: &Atom) -> Atom {
        match self.ids.get(a) {
            Some(&id) => self.atoms[self.tree_root_id(id)].clone(),
            None => a.clone(),
        }
    }

    /// Lowest common ancestor of `u` (at depth `du`) and `v` (at depth `dv`) in the same tree,
    /// returning `(lca, lca_depth)` with pointer hops only.
    fn lca_same_tree(
        &self,
        mut u: usize,
        mut du: usize,
        mut v: usize,
        mut dv: usize,
    ) -> (usize, usize) {
        while du > dv {
            u = self.parent[u];
            du -= 1;
        }
        while dv > du {
            v = self.parent[v];
            dv -= 1;
        }
        while u != v {
            u = self.parent[u];
            v = self.parent[v];
            du -= 1;
        }
        (u, du)
    }

    /// Expresses `u = s * target + d` where `target` is an ancestor of `u`.
    fn walk_to_id(&self, mut u: usize, target: usize) -> (i8, Int) {
        let mut s: i8 = 1;
        let mut d = Int::ZERO;
        while u != target {
            let pd = &self.offset[u];
            if !pd.is_zero() {
                d = if s > 0 { &d + pd } else { &d - pd };
            }
            s *= self.sign[u];
            u = self.parent[u];
        }
        (s, d)
    }

    /// Expresses `u = s * tree_root + d`.
    fn tree_get_id(&self, mut u: usize) -> (usize, i8, Int) {
        let mut s: i8 = 1;
        let mut d = Int::ZERO;
        while self.parent[u] != u {
            let pd = &self.offset[u];
            if !pd.is_zero() {
                d = if s > 0 { &d + pd } else { &d - pd };
            }
            s *= self.sign[u];
            u = self.parent[u];
        }
        (u, s, d)
    }

    /// Expresses `a = s * tree_root + d` in O(log n) hops.
    fn tree_get(&self, a: &Atom) -> (Atom, i8, Int) {
        match self.ids.get(a) {
            Some(&id) => {
                let (r, s, d) = self.tree_get_id(id);
                (self.atoms[r].clone(), s, d)
            }
            None => (a.clone(), 1, Int::ZERO),
        }
    }

    /// Expresses `a = s * canon_root + d`, re-anchored to the smallest `Atom` in `a`'s component,
    /// in O(log n) hops.
    #[cfg(test)]
    fn get(&self, a: &Atom) -> (Atom, i8, Int) {
        let Some(&id) = self.ids.get(a) else {
            return (a.clone(), 1, Int::ZERO);
        };
        let (r, sa, da) = self.tree_get_id(id);
        let c = self.canon[r];
        if c == r {
            return (self.atoms[r].clone(), sa, da);
        }
        let (_, sc, dc) = self.tree_get_id(c);
        // a = sa * r + da, c = sc * r + dc => r = sc * c - sc * dc
        // => a = (sa * sc) * c + (da - sa * sc * dc)
        let s = sa * sc;
        let d = if s > 0 { &da - &dc } else { &da + &dc };
        (self.atoms[c].clone(), s, d)
    }

    /// Returns `[min_{v = +root + d} d, min_{v = -root + d} d]` over all atoms in `root`'s tree
    /// in one bottom-up pass (each edge offset is added or subtracted at most twice, O(S) bit
    /// work).
    fn min_offsets_of(&self, root: &Atom) -> [Option<Int>; 2] {
        let Some(&root_id) = self.ids.get(root) else {
            return [Some(Int::ZERO), None];
        };
        let n = self.atoms.len();
        let mut head = vec![usize::MAX; n];
        let mut next = vec![usize::MAX; n];
        for u in 0..n {
            let p = self.parent[u];
            if p != u {
                next[u] = head[p];
                head[p] = u;
            }
        }
        let mut order = Vec::new();
        let mut stack = vec![root_id];
        while let Some(u) = stack.pop() {
            order.push(u);
            let mut c = head[u];
            while c != usize::MAX {
                stack.push(c);
                c = next[c];
            }
        }
        let mut best: Vec<[Option<Int>; 2]> = vec![[None, None]; n];
        for &u in order.iter().rev() {
            let mut cur: [Option<Int>; 2] = [Some(Int::ZERO), None];
            let mut c = head[u];
            while c != usize::MAX {
                let se = self.sign[c];
                let de = &self.offset[c];
                // For `v = sv * c + dv` and `c = se * u + de`,
                // `v = (sv * se) * u + (sv * de + dv)`.
                if let Some(d_pos) = best[c][0].take() {
                    let cand = if de.is_zero() { d_pos } else { &d_pos + de };
                    let slot = &mut cur[usize::from(se < 0)];
                    if slot.as_ref().is_none_or(|l| cand < *l) {
                        *slot = Some(cand);
                    }
                }
                if let Some(d_neg) = best[c][1].take() {
                    let cand = if de.is_zero() { d_neg } else { &d_neg - de };
                    let slot = &mut cur[usize::from(se > 0)];
                    if slot.as_ref().is_none_or(|l| cand < *l) {
                        *slot = Some(cand);
                    }
                }
                c = next[c];
            }
            best[u] = cur;
        }
        std::mem::take(&mut best[root_id])
    }

    /// Links `a = s * b + d`. Returns `Err(())` on contradiction, or `Ok(Some((tree_root, val)))`
    /// when an opposite-sign cycle fixes `tree_root` to an integer `val`.
    fn union(&mut self, a: &Atom, b: &Atom, s: i8, d: &Int) -> Result<Option<(Atom, Int)>, ()> {
        let ia = self.ensure_id(a);
        let ib = self.ensure_id(b);
        let (ra, da_depth) = self.root_and_depth_id(ia);
        let (rb, db_depth) = self.root_and_depth_id(ib);
        if ra == rb {
            let (lca, _) = self.lca_same_tree(ia, da_depth, ib, db_depth);
            let (sa, da) = self.walk_to_id(ia, lca);
            let (sb, db) = self.walk_to_id(ib, lca);
            // sa * lca + da = s * (sb * lca + db) + d
            let s_db = if s > 0 { db } else { -&db };
            let rhs_const = &(&s_db + d) - &da;
            let rel_s = sa * s * sb;
            let rel_d = if sa > 0 { rhs_const } else { -&rhs_const };
            if rel_s == 1 {
                if !rel_d.is_zero() {
                    return Err(());
                }
                return Ok(None);
            }
            // 2 * lca = rel_d
            let two = Int::from(2);
            if !rel_d.mod_floor(&two).is_zero() {
                return Err(());
            }
            let lca_val = rel_d.div_floor(&two);
            // Lift `lca = sl * ra + dl` to `ra = sl * (lca_val - dl)`.
            let (sl, dl) = self.walk_to_id(lca, ra);
            let diff = &lca_val - &dl;
            let root_val = if sl > 0 { diff } else { -&diff };
            return Ok(Some((self.atoms[ra].clone(), root_val)));
        }
        let (_, sa, da) = self.tree_get_id(ia);
        let (_, sb, db) = self.tree_get_id(ib);
        // sa * ra + da = s * (sb * rb + db) + d  =>  ra = rel_s * rb + rel_d
        let s_db = if s > 0 { db } else { -&db };
        let rhs_const = &(&s_db + d) - &da;
        let rel_s = sa * s * sb;
        let rel_d = if sa > 0 { rhs_const } else { -&rhs_const };
        // Link smaller subtree under larger subtree; break ties by smaller Atom.
        let attach_ra_under_rb = self.size[ra] < self.size[rb]
            || (self.size[ra] == self.size[rb] && self.atoms[ra] > self.atoms[rb]);
        if attach_ra_under_rb {
            self.parent[ra] = rb;
            self.sign[ra] = rel_s;
            self.offset[ra] = rel_d;
            self.size[rb] += self.size[ra];
            if self.atoms[self.canon[ra]] < self.atoms[self.canon[rb]] {
                self.canon[rb] = self.canon[ra];
            }
        } else {
            // rb = rel_s * (ra - rel_d) = rel_s * ra - rel_s * rel_d
            let inv_d = if rel_s > 0 { -&rel_d } else { rel_d };
            self.parent[rb] = ra;
            self.sign[rb] = rel_s;
            self.offset[rb] = inv_d;
            self.size[ra] += self.size[rb];
            if self.atoms[self.canon[rb]] < self.atoms[self.canon[ra]] {
                self.canon[ra] = self.canon[rb];
            }
        }
        Ok(None)
    }
}

fn add_scaled(acc: &mut Int, k: &Int, d: &Int) {
    if d.is_zero() {
        return;
    }
    if k.is_unit() {
        *acc = if k.is_positive() {
            &*acc + d
        } else {
            &*acc - d
        };
    } else {
        *acc = &*acc + &(k * d);
    }
}

fn emit_root_term(
    r: &Atom,
    k1: Int,
    rem_defs: &HashMap<Atom, FullRemDef>,
    terms: &mut BTreeMap<Atom, Int>,
    constant: &mut Int,
) {
    if let Some(rem) = rem_defs.get(r) {
        let factor = if rem.c_r > 0 { -&k1 } else { k1 };
        add_scaled(constant, &factor, &rem.k);
        let e_x = terms.entry(rem.x_root.clone()).or_insert(Int::ZERO);
        *e_x = &*e_x + &(&factor * &rem.c_x);
        let e_q = terms.entry(rem.q_root.clone()).or_insert(Int::ZERO);
        *e_q = &*e_q + &(&factor * &rem.c_q);
    } else {
        let e = terms.entry(r.clone()).or_insert(Int::ZERO);
        *e = &*e + &k1;
    }
}

fn rewrite_lin_full(
    lin: &Lin,
    fixed: &HashMap<Atom, Int>,
    uf: &UnitUf,
    rem_defs: &HashMap<Atom, FullRemDef>,
) -> Lin {
    let mut constant = lin.constant.clone();
    if lin.terms.is_empty() {
        return Lin {
            terms: BTreeMap::new(),
            constant,
        };
    }
    if lin.terms.len() == 1 {
        let (a, k) = lin.terms.iter().next().expect("checked non-empty");
        if let Some(v) = fixed.get(a) {
            add_scaled(&mut constant, k, v);
            return Lin {
                terms: BTreeMap::new(),
                constant,
            };
        }
        let (r1, s1, d1) = uf.tree_get(a);
        if let Some(v) = fixed.get(&r1) {
            let val = if s1 > 0 { v + &d1 } else { &d1 - v };
            add_scaled(&mut constant, k, &val);
            return Lin {
                terms: BTreeMap::new(),
                constant,
            };
        }
        add_scaled(&mut constant, k, &d1);
        let k1 = if s1 > 0 { k.clone() } else { -k };
        let mut terms = BTreeMap::new();
        emit_root_term(&r1, k1, rem_defs, &mut terms, &mut constant);
        terms.retain(|_, v| !v.is_zero());
        return Lin { terms, constant };
    }
    if lin.terms.len() == 2 {
        let mut it = lin.terms.iter();
        let (a, ka) = it.next().expect("len == 2");
        let (b, kb) = it.next().expect("len == 2");
        if !fixed.contains_key(a)
            && !fixed.contains_key(b)
            && let (Some(&ia), Some(&ib)) = (uf.ids.get(a), uf.ids.get(b))
        {
            let (ra, da_depth) = uf.root_and_depth_id(ia);
            let (rb, db_depth) = uf.root_and_depth_id(ib);
            if ra == rb {
                // Both terms lie in the same UF tree: collapse at their LCA first so cancelling
                // terms (`net_k == 0`) never cross wide edges above the LCA.
                let (lca, _) = uf.lca_same_tree(ia, da_depth, ib, db_depth);
                let (sa, da) = uf.walk_to_id(ia, lca);
                let (sb, db) = uf.walk_to_id(ib, lca);
                add_scaled(&mut constant, ka, &da);
                add_scaled(&mut constant, kb, &db);
                let k_a = if sa > 0 { ka.clone() } else { -ka };
                let net_k = if sb > 0 { &k_a + kb } else { &k_a - kb };
                if net_k.is_zero() {
                    return Lin {
                        terms: BTreeMap::new(),
                        constant,
                    };
                }
                let (sl, dl) = uf.walk_to_id(lca, ra);
                let r_atom = &uf.atoms[ra];
                if let Some(v) = fixed.get(r_atom) {
                    let val = if sl > 0 { v + &dl } else { &dl - v };
                    add_scaled(&mut constant, &net_k, &val);
                    return Lin {
                        terms: BTreeMap::new(),
                        constant,
                    };
                }
                add_scaled(&mut constant, &net_k, &dl);
                let k1 = if sl > 0 { net_k } else { -&net_k };
                let mut terms = BTreeMap::new();
                emit_root_term(r_atom, k1, rem_defs, &mut terms, &mut constant);
                terms.retain(|_, v| !v.is_zero());
                return Lin { terms, constant };
            }
        }
    }
    let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
    let mut groups: HashMap<usize, Vec<(usize, usize, &Int)>> = HashMap::new();
    for (a, k) in &lin.terms {
        if let Some(v) = fixed.get(a) {
            add_scaled(&mut constant, k, v);
            continue;
        }
        if let Some(&id) = uf.ids.get(a) {
            let (r, depth) = uf.root_and_depth_id(id);
            groups.entry(r).or_default().push((id, depth, k));
        } else {
            emit_root_term(a, k.clone(), rem_defs, &mut terms, &mut constant);
        }
    }
    for (r, members) in groups {
        let (mut lca, mut lca_depth) = (members[0].0, members[0].1);
        for &(id, depth, _) in &members[1..] {
            (lca, lca_depth) = uf.lca_same_tree(lca, lca_depth, id, depth);
        }
        let mut net_k = Int::ZERO;
        for (id, _, k) in members {
            let (s, d) = uf.walk_to_id(id, lca);
            add_scaled(&mut constant, k, &d);
            net_k = if s > 0 { &net_k + k } else { &net_k - k };
        }
        if net_k.is_zero() {
            continue;
        }
        let (sl, dl) = uf.walk_to_id(lca, r);
        let r_atom = &uf.atoms[r];
        if let Some(v) = fixed.get(r_atom) {
            let val = if sl > 0 { v + &dl } else { &dl - v };
            add_scaled(&mut constant, &net_k, &val);
            continue;
        }
        add_scaled(&mut constant, &net_k, &dl);
        let k1 = if sl > 0 { net_k } else { -&net_k };
        emit_root_term(r_atom, k1, rem_defs, &mut terms, &mut constant);
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
// take 17.1 times the work for 8 times the depth (limit 14.2 of 2026-11-11). It was added for the
// `fails` questions of pairs (I3.2), which the zero witness and the batched remainder check now
// answer near-linearly (`one_scope::the_fails_questions_of_pairs_scale`,
// `pncx_probe::pncx_pairs_scale`, `pncx_probe::pncx_disj_scale` pass without it). What is
// given up: such a formula goes to the general path whole; no answer of the 5,000-formula
// enumeration test changed (sat 4277, empty 712, refused 11 with and without the split).
pub fn solve_modular(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    // Every 3-term remainder equality `c_u·u + c_v·v + c_q·q + k == 0` (`|c_u| = |c_v| = 1`,
    // `|c_q| = m >= 2`) has at most two unit roots `{u, v}`, and step 4 requires every
    // eliminated remainder `r` to be defined in terms of the same single primary root `x_root`
    // (since `r`'s 1-term bounds rewrite to 2-term constraints on `(x_root, q_root)`). Therefore
    // `x_root` must lie in the intersection over all candidate remainder rows of the set of unit
    // roots whose partner is bounded to width `< m`. That intersection has size at most 2
    // regardless of how many rows tie, and depends only on the equivalence classes of step 1 and
    // the bound widths of step 2, never on atom names or row order. Trying every candidate in
    // the intersection (at most two runs of steps 4+, reusing steps 0–2) is therefore exact and
    // completely independent of variable names and row order (U4 / I6.3).
    //
    // Complexity tradeoff: naive, orient each of t tied rows independently and try all 2^t
    // combinations, exponential in t; used, intersect the valid `x_root` sets across all
    // remainder rows to at most 2 candidates, then run steps 4+ at most twice, O(n log n) in
    // total. Nothing is given up for formulas accepted by step 4: any valid `rem_defs` eliminating
    // all candidate remainder rows must have its unique `x_root` in this intersection.
    // Tests: `one_scope::remainder_alias_answers_do_not_depend_on_names`,
    // `one_scope::one_variable_modular_formulas_match_enumeration`,
    // `solve_names_tests::two_tied_remainder_rows_are_answered_alike_under_every_naming`,
    // `solve_names_tests::solve_modular_never_gives_two_verdicts_on_tied_remainder_rows`.
    solve_modular_whole(f, want_model)
}

/// A point of `f` found by [`solve_modular`], or `None` when `f` has no point or lies outside
/// its scope. Because [`solve_modular`] chooses `x_root` from the name- and order-independent
/// candidate intersection (size at most 2) and tries every candidate, whether a point is found
/// does not depend on atom names or row order.
pub(super) fn point_by_structure(f: &Formula) -> Option<Model> {
    solve_modular(f, true).flatten()
}

/// Decide a conjunction of equalities with private integer quotients and one free integer.
/// The caller enters only for a Boolean query on a flattened conjunction of rows with at
/// least one nonzero constant. The empty conjunction and the homogeneous zero witness stay
/// with the general solver. Each accepted row has exactly two non-product atoms in
/// `s*x + a*q + c = 0`, where the same `x` occurs with `s = ±1` in every row and
/// `|a| > 1`. A bound, an equality of a different shape, a unit-modulus row, or a shared
/// quotient declines this shortcut. A unit modulus by itself places no restriction on x.
///
/// Solving the row for q is possible exactly when a divides `s*x+c`. Thus the row requires
/// `x = -s*c (mod |a|)`, and any such x gives the integer quotient `-(s*x+c)/a`. The
/// quotients occur nowhere else in this conjunction, so the choices of quotient are independent.
///
/// Each modulus is the product of its supplied pairwise coprime powers. Divisibility by that
/// product is equivalent to divisibility by each power. For powers of the same base, the
/// smaller divides the larger. Their residue classes are disjoint if the larger residue
/// differs from the smaller modulo the smaller power. Otherwise every integer in the larger
/// class is in the smaller one. After processing any prefix, the map therefore preserves
/// precisely the joint requirement of all processed rows on each base. A conflict cannot be
/// solved. If no conflict occurs, CRT gives an x satisfying the retained powers because
/// powers from distinct bases are coprime. This x gives all the independent quotients above.
///
/// Complexity tradeoff: naive, build the CRT integer of all rows (`combine_crt_tree`), which
/// costs O(M(B) log k) for `k` rows of `B` modulus bits in all and measured 23.3 times work
/// for 8 times the rows (bench `pncx_crt_tree_scale`, deferred, plan row
/// PERF-negated-chain-unsolved). A Boolean answer needs only whether the integer exists. Used:
/// one residue per coprime base, kept in a hash map, never multiplied out.
///
/// Cost, step by step. Let `B` be the bits of all names, moduli and constants of the rows,
/// `len` a width in num-bigint's 64-bit words, and `W` the largest `len(m)`.
/// 1. The root is read from the first row's two terms: O(1) atom reads.
/// 2. Per row: the `BTreeMap` lookup of the root, of depth one for two terms, compares atoms
///    in time linear in the name; the `HashSet` insert hashes the quotient's name, expected O(1)
///    table operations; `abs` and the negated constant copy values linear in their widths;
///    the `BTreeSet` insert of the modulus makes O(log k) comparisons, each linear in the
///    width. Over the rows: O(B log k).
/// 3. A modulus `m` has at most `log2 m` factors: its bases are pairwise coprime and at least
///    2, so their product, which divides `m`, is at least `2^count`.
/// 4. Reducing `r` by a power `p` is num-bigint's schoolbook division, O((len r + 1) len p)
///    word operations. The comparison reduces the stored residue, which is below a power from
///    an earlier row and so at most `W` words, by `p` or compares two residues below `p`:
///    O((W + 1) len p). The powers of a row multiply to `m`, so their widths in words add to
///    at most `len m` plus the number of factors, which by step 3 is at most `bits(m)`. A row
///    costs O((len r + W) bits(m)), and the `factors` lookup O(log k) comparisons of width
///    `len m`.
/// 5. Each factor makes one hash-map entry operation: a hash of the base, linear in its width,
///    and expected O(1) table operations.
///
/// So this routine's own work is O(B log k + Σ (len r_i + W) bits(m_i)). As `len r_i` is at
/// most `bits(r_i)` and `bits(m_i)` at most `64 W`, the sum is at most `64 W Σ bits(r_i) + W B`,
/// so the whole is O(B (log k + W)): O(B log B) expected when every modulus fits in a bounded
/// number of words, as in `pncx_shared_formula_scale`, and not O(B log B) for wide moduli. To
/// that add `coprime_factorization`, whose bound is stated and argued at that function, not
/// here; on distinct primes of more than 44 bits it measured 14.4 times the work for 8 times
/// `B` (R2 Gemini seat, `ADV_WIDE48_UNIT`, 2026-11-21), open in PERF-private-quotient-wide-moduli.
/// Measured on the bench (2026-11-20, R2 Sol seat, load 54.65): 8.826 times the instructions
/// and 8.02 times the bytes for 8 times the rows. Before: 9.536 and 8.85.
///
/// Tests: `private_quotients_match_concrete_models_on_small_systems` and
/// `private_quotients_agree_with_enumeration_and_skip_shared_variables`.
fn private_quotient_consistency(cons: &[&Con]) -> Option<bool> {
    let (root, _) = cons.first()?.lin.terms.iter().find(|(_, k)| k.is_unit())?;
    if matches!(root, Atom::Product(..)) {
        return None;
    }
    let mut quotients = HashSet::with_capacity(cons.len());
    let mut moduli = BTreeSet::new();
    let mut rows = Vec::with_capacity(cons.len());
    for c in cons {
        if c.rel != Rel::Eq || c.lin.terms.len() != 2 {
            return None;
        }
        let k_root = c.lin.terms.get(root).filter(|k| k.is_unit())?;
        let (q, k_q) = c.lin.terms.iter().find(|(a, _)| *a != root)?;
        if matches!(q, Atom::Product(..)) || k_q.is_unit() || k_q.is_zero() || !quotients.insert(q)
        {
            return None;
        }
        let m = k_q.abs();
        let r = if k_root.is_negative() {
            c.lin.constant.clone()
        } else {
            -&c.lin.constant
        };
        moduli.insert(m.clone());
        rows.push((m, r));
    }

    let factors = coprime_factorization(&moduli);
    let mut strongest: HashMap<&Int, (&Int, Int)> = HashMap::with_capacity(moduli.len());
    for (m, r) in rows {
        for (base, power) in &factors[&m] {
            let residue = r.mod_floor(power);
            match strongest.entry(base) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert((power, residue));
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let (old_power, old_residue) = entry.get();
                    let compatible = match power.cmp(old_power) {
                        std::cmp::Ordering::Less => old_residue.mod_floor(power) == residue,
                        std::cmp::Ordering::Equal => *old_residue == residue,
                        std::cmp::Ordering::Greater => residue.mod_floor(old_power) == *old_residue,
                    };
                    if !compatible {
                        return Some(false);
                    }
                    if power > *old_power {
                        entry.insert((power, residue));
                    }
                }
            }
        }
    }
    Some(true)
}

fn solve_modular_whole(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    // Collect top-level conjunction and verify no Product atoms exist anywhere in `f`.
    let mut top_cons: Vec<&Con> = Vec::new();
    let mut top_clauses: Vec<&Formula> = Vec::new();
    // The formula's one walk of the conjuncts (`Formula::conjunct_list`, dryA5 row 4), of which
    // this was a copy in the same order, but for one thing kept: a disjunction or negation
    // shared at two places is kept once, at its first, as this copy kept it, so step 6 folds it
    // once. Whether a verdict holds with it twice is idempotence of conjunction; which point
    // is found was not checked, so the list is kept as it was.
    let mut seen_top: HashSet<Id> = HashSet::new();
    for g in f.conjunct_list().iter() {
        match g {
            Formula::And(_) => unreachable!("conjunct_list flattens every conjunction"),
            Formula::Con(c) => top_cons.push(c),
            Formula::Or(ds) if ds.is_empty() => return Some(None),
            Formula::Or(_) | Formula::Not(_) => {
                if seen_top.insert(Id::any(g)) {
                    top_clauses.push(g);
                }
            }
        }
    }

    // A conjunction with all constants zero can use the existing zero witness before
    // any factorization. A nonzero constant rules out that witness for these equalities.
    if !want_model
        && top_clauses.is_empty()
        && top_cons.iter().any(|c| !c.lin.constant.is_zero())
        && let Some(consistent) = private_quotient_consistency(&top_cons)
    {
        return Some(consistent.then(Model::new));
    }

    // Check all constraints in the DAG for products, at least one non-unit coefficient, and collect
    // all atoms. `Formula::walk` and not `Formula::cons`, which is written in presburger.rs: a call
    // of it here would close an import cycle with presburger.rs (step S.1f). The list is the same.
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

    // Step 1: Constant equalities propagation (`k * a + c == 0`) and Unit equalities
    // (`a = ±b + d`).
    let mut fixed: HashMap<Atom, Int> = HashMap::new();
    let mut uf = UnitUf::new();
    for a in &all_atoms {
        uf.ensure(a);
    }

    // Complexity tradeoff: repeating the pass over every row until a pass fixes nothing costs
    // one pass per atom fixed in a chain (`2 a_i == 2 a_(i+1)` written so that each pass fixes
    // one more), O(n^2) rows read (R7-CLAUDE-1, `r7_tests::bench::pncx_fixed_chain_scale`), and a
    // pass that only joined two classes stopped the loop, so a row read before the join was never
    // read again and the result followed the order of the rows. A FIFO worklist reads each row
    // O(log n) times, but if a wide unit equality `a = b + B` is processed before small unit
    // equalities, later small unions on the same component cross the wide edge `O(n)` times,
    // `O(n * B)` bit work. Ordering the worklist by ascending bit-width (Kruskal's minimum
    // bit-weight spanning forest) processes every small unit equality before wider edges, so
    // when an edge of width `B` is joined, every existing tree edge has width `<= B`, bounding
    // total Step 1 bit work by `O(S log n)` for total input bit-length `S` regardless of row
    // order. Its result is the fixpoint of the same sound rules, independent of row order.
    // Nothing is given up. Tests: `pncx_wide_affine_alias_scale`, `pncx_fixed_chain_scale`.
    let empty_rems: HashMap<Atom, FullRemDef> = HashMap::new();
    let mut class_rows: HashMap<Atom, Vec<usize>> = HashMap::new();
    for (i, c) in top_cons.iter().enumerate() {
        for a in c.lin.terms.keys() {
            class_rows.entry(a.clone()).or_default().push(i);
        }
    }
    let con_bit_weight = |c: &Con| -> u64 {
        let mut w = c.lin.constant.bits();
        for k in c.lin.terms.values() {
            w = w.max(k.bits());
        }
        w
    };
    let mut row_weight: Vec<u64> = top_cons.iter().map(|c| con_bit_weight(c)).collect();
    let mut queued = vec![true; top_cons.len()];
    let mut queue: MinHeap<(u64, usize)> = row_weight
        .iter()
        .enumerate()
        .map(|(i, &w)| (w, i))
        .collect();
    // Puts the rows of a modified class back in the priority worklist with at least `trigger_w`.
    fn requeue(
        rows: Option<&Vec<usize>>,
        trigger_w: u64,
        row_weight: &mut [u64],
        queued: &mut [bool],
        queue: &mut MinHeap<(u64, usize)>,
    ) {
        for &i in rows.into_iter().flatten() {
            if trigger_w > row_weight[i] {
                row_weight[i] = trigger_w;
            }
            if !queued[i] {
                queued[i] = true;
                queue.push((row_weight[i], i));
            }
        }
    }
    while let Some((_, i)) = queue.pop() {
        queued[i] = false;
        let c = &top_cons[i];
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
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
            if !lin.constant.mod_floor(&d).is_zero() {
                return Some(None);
            }
            let val = if k.is_positive() {
                (-&lin.constant).div_floor(&d)
            } else {
                lin.constant.div_floor(&d)
            };
            if let Some(old) = fixed.get(a) {
                if *old != val {
                    return Some(None);
                }
            } else {
                let w_val = val.bits();
                fixed.insert(a.clone(), val);
                requeue(
                    class_rows.get(a),
                    w_val,
                    &mut row_weight,
                    &mut queued,
                    &mut queue,
                );
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
                let w_d = d.bits();
                // `a` and `b` are tree roots of two classes, neither fixed (`rewrite_lin_full`).
                let joined = uf.union(a, b, s, &d);
                let root = uf.tree_root(a);
                let (small, large) = {
                    let ra = class_rows.remove(a).unwrap_or_default();
                    let rb = class_rows.remove(b).unwrap_or_default();
                    if ra.len() < rb.len() {
                        (ra, rb)
                    } else {
                        (rb, ra)
                    }
                };
                requeue(Some(&small), w_d, &mut row_weight, &mut queued, &mut queue);
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
                            let w_val = val.bits();
                            fixed.insert(fixed_root, val);
                            requeue(
                                Some(&large),
                                w_val,
                                &mut row_weight,
                                &mut queued,
                                &mut queue,
                            );
                        }
                    }
                    Ok(None) => {}
                }
                class_rows.insert(root, large);
            }
        }
    }

    // Step 2: Identify 1-term bounds on root atoms to help recognize 3-term division remainders
    // (`x_root + c - m * q_root - r_root == 0` with `0 <= r <= m - 1`).
    let mut root_bounds: HashMap<Atom, (Option<Int>, Option<Int>)> = HashMap::new();
    for c in &top_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
        if lin.terms.len() == 1 {
            let (a, k) = lin.terms.iter().next()?;
            let d = k.abs();
            let entry = root_bounds.entry(a.clone()).or_insert((None, None));
            match c.rel {
                Rel::Ge if k.is_positive() => {
                    let lo = -&lin.constant.div_floor(&d);
                    entry.0 = max_lo(entry.0.take(), Some(lo));
                }
                Rel::Ge => {
                    let hi = lin.constant.div_floor(&d);
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
    // `c_u * u + c_v * v + c_q * q_root + k == 0` where `|c_u| == 1`, `|c_v| == 1`,
    // `|c_q| = m >= 2`, and at least one of `u`, `v` is bounded to an interval of width `< m`.
    // Every eliminated remainder `r` has 1-term bounds in `top_cons` that rewrite in step 4 to
    // 2-term constraints on `(x_root, q_root)`. Step 4 requires all such constraints to share a
    // single primary root `x_root` (never itself eliminated). Hence `x_root` must lie in the
    // intersection over all candidate remainder rows of `{w in {u, v} | partner bounded < m}`.
    // Since each row contributes at most 2 atoms, this intersection has size 0, 1, or 2, and
    // depends only on step 1's classes and step 2's bound widths (never atom names or row order).
    struct RemRow {
        u: Atom,
        c_u: Int,
        v: Atom,
        c_v: Int,
        q_root: Atom,
        c_q: Int,
        m: Int,
        k: Int,
        u_can_be_rem: bool,
        v_can_be_rem: bool,
    }
    let bounded_lt_m = |a: &Atom, m: &Int| -> bool {
        matches!(
            root_bounds.get(a),
            Some((Some(lo), Some(hi))) if lo <= hi && (hi - lo) < *m
        )
    };
    let mut rem_rows: Vec<RemRow> = Vec::new();
    for c in &top_cons {
        if c.rel != Rel::Eq {
            continue;
        }
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
        if lin.terms.len() != 3 {
            continue;
        }
        let mut non_unit: Option<(&Atom, &Int)> = None;
        let mut units: Vec<(&Atom, &Int)> = Vec::with_capacity(2);
        let mut ok = true;
        for (a, k) in &lin.terms {
            if k.is_unit() {
                units.push((a, k));
            } else if non_unit.is_none() {
                non_unit = Some((a, k));
            } else {
                ok = false;
                break;
            }
        }
        if !ok || units.len() != 2 {
            continue;
        }
        let Some((q_root, c_q)) = non_unit else {
            continue;
        };
        let m = c_q.abs();
        let u_can_be_rem = bounded_lt_m(units[0].0, &m);
        let v_can_be_rem = bounded_lt_m(units[1].0, &m);
        if !u_can_be_rem && !v_can_be_rem {
            continue;
        }
        rem_rows.push(RemRow {
            u: units[0].0.clone(),
            c_u: units[0].1.clone(),
            v: units[1].0.clone(),
            c_v: units[1].1.clone(),
            q_root: q_root.clone(),
            c_q: c_q.clone(),
            m,
            k: lin.constant.clone(),
            u_can_be_rem,
            v_can_be_rem,
        });
    }

    let run_with_rems = |rem_defs: HashMap<Atom, FullRemDef>| -> Option<Option<Model>> {
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

        // Step 5: Collect top-level bounds on `(x_root, q_root)` to identify GlobalQuot vs
        // LocalQuot.
        // A constraint with terms `{x_root: c_x, q_root: c_q}` and `|c_x| == 1`, `|c_q| = m >= 2`:
        // Normalize by dividing by `|c_x|`: wait, if `|c_x| > 1` in a 1-term constraint on
        // `q_root`, `c_x == 0`. In a 2-term constraint, `|c_x| == 1` (already checked above).
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
            // Express `lin` as `t * (entry.s_x * x - entry.sigma_q * m * q) + constant`, where
            // `t = ±1`.
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
                    // `lo <= x - sigma_q * m * q <= hi`  <=>
                    // `0 <= (x - lo) - sigma_q * m * q <= w`.
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

        // Verify every 1-term constraint in `all_cons` is either on `x_root` or on a `global_quots`
        // key.
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

        // Step 7: Add top-level narrowed windows of `global_quots` (`w < m - 1`) as unit
        // congruences, and separate `root_node.clauses` into global bounds, global unit
        // congruences, and clauses.
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

        // Step 8: Merge clauses sharing the same modular part `D` via
        // `(D || B1) && (D || B2) <=> D || (B1 && B2)`.
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
        // Only needed when an unbounded span `(None, None)` exists in `regimes`, and computed by
        // `min_offsets_of` in O(S) bit work (touching each tree edge at most twice).
        let free: Vec<(i8, Int)> = if regimes.first().is_some_and(|(l, _)| l.is_none())
            && regimes.last().is_some_and(|(_, h)| h.is_none())
        {
            let [plus, minus] = uf.min_offsets_of(&x_root);
            plus.map(|d| (1, -&d))
                .into_iter()
                .chain(minus.map(|d| (-1, d)))
                .collect()
        } else {
            Vec::new()
        };
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

        // Complexity tradeoff: naive version, branching over the residues of every base,
        // exponential in the number of bases (a conjunction of clauses of residues under several
        // coprime moduli encodes CNF-SAT, so no exact polynomial method is known for all of them).
        // Used: the CRT fixpoint, hole cutting on segments shorter than a modulus, the
        // forbidden-box share bound with conditional expectations, and one level of single-base
        // splitting, each O(n log n) on one segment. The segments are walked by `walk_segments`,
        // whose cost is bounded there. What is given up: nothing is refused here; a segment these
        // steps leave undecided sends the whole formula to the solver's general path, which then
        // answers, or refuses, as it did before, at its own cost. Tests:
        // `one_scope::easy_clause_systems_over_several_moduli_keep_their_answers`,
        // `one_scope::one_variable_modular_formulas_match_enumeration`,
        // `one_scope::the_questions_of_negated_residues_over_distinct_bounds_scale`.
        if undecided { None } else { Some(None) }
    };

    if rem_rows.is_empty() {
        return run_with_rems(HashMap::new());
    }
    let mut candidates: Vec<Atom> = Vec::with_capacity(2);
    if rem_rows[0].v_can_be_rem {
        candidates.push(rem_rows[0].u.clone());
    }
    if rem_rows[0].u_can_be_rem {
        candidates.push(rem_rows[0].v.clone());
    }
    for row in &rem_rows[1..] {
        candidates
            .retain(|x| (*x == row.u && row.v_can_be_rem) || (*x == row.v && row.u_can_be_rem));
        if candidates.is_empty() {
            return None;
        }
    }
    if candidates.len() == 2 {
        // Order the two candidates so the one appearing in more multi-term constraints is tried
        // first; because both candidates are tried if the first refuses, the verdict and refusal
        // do not depend on this order.
        let (mut u0, mut u1) = (0usize, 0usize);
        for c in &all_cons {
            let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
            if lin.terms.len() >= 2 {
                if lin.terms.contains_key(&candidates[0]) {
                    u0 += 1;
                }
                if lin.terms.contains_key(&candidates[1]) {
                    u1 += 1;
                }
            }
        }
        if u1 > u0 {
            candidates.swap(0, 1);
        }
    }
    for x_cand in candidates {
        let mut rem_defs: HashMap<Atom, FullRemDef> = HashMap::new();
        for row in &rem_rows {
            let (r_root, c_r, c_x) = if row.u == x_cand {
                (&row.v, &row.c_v, &row.c_u)
            } else {
                (&row.u, &row.c_u, &row.c_v)
            };
            let replace = match rem_defs.get(r_root) {
                None => true,
                Some(prev) => row.m < prev.c_q.abs(),
            };
            if replace {
                rem_defs.insert(
                    r_root.clone(),
                    FullRemDef {
                        c_r: if c_r.is_positive() { 1 } else { -1 },
                        x_root: x_cand.clone(),
                        c_x: c_x.clone(),
                        q_root: row.q_root.clone(),
                        c_q: row.c_q.clone(),
                        k: row.k.clone(),
                    },
                );
            }
        }
        if let Some(ans) = run_with_rems(rem_defs) {
            return Some(ans);
        }
    }
    None
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
                .all(|(m, s)| res_contains(s, &x.mod_floor(m)))
            && clauses.iter().all(|cl| {
                (!cl.bounds.is_empty() && cl.bounds.contains_span(&at, &at))
                    || cl
                        .mods
                        .iter()
                        .any(|(m, s)| res_contains(s, &x.mod_floor(m)))
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
        // `ql <= floor((s_x * x + c_lo) / m) <= qh` <=>
        // `m * ql <= s_x * x + c_lo <= m * qh + m - 1`.
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
        Rel::Ge if k.is_positive() => Domain::ge(-&c.div_floor(&d)),
        Rel::Ge => Domain::le(c.div_floor(&d)),
        Rel::Eq => {
            if !c.mod_floor(&d).is_zero() {
                Domain::empty()
            } else {
                let v = if k.is_positive() {
                    (-c).div_floor(&d)
                } else {
                    c.div_floor(&d)
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
        zed_collections::sorted::sort_dedup(&mut next);
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
    zed_collections::sorted::sort_dedup(&mut cuts);

    let mut out = Vec::new();
    // Complexity tradeoff: scanning every cut for every disjoint global span
    // costs O(g c). Binary searches select only the cuts inside each span,
    // O(g log c + c) comparisons in total; disjoint spans cannot share a cut.
    // Nothing is given up. Test: r4_tests::bench::pncx_bound_partition_scale.
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
    // A clause with a literal `x mod m in s` whose set `s` holds the unit's set for `m` is true
    // at every point of the regime, so it is dropped: the regime's points are the same with it
    // and without it, and a point found without it satisfies the unit and so the clause. Kept,
    // its modulus joined the coprime base, and a literal on a lower power of a base whose
    // allowed set spans more than two blocks of that power is left to the general path
    // (`intersect_mod_divisor`; FAIL-modular-unbounded-regime-undecided: `x mod 10 != 8` with
    // the clause `x mod 8 != 4 || x mod 10 != 8` lifted `x mod 2 != 0` over `[0, 7]` modulo 8).
    // Complexity tradeoff: naive version, none (every clause kept). Used: per literal one
    // lookup of its modulus among the units and a test of each gap of `s` against the unit's
    // runs by binary search, O(g log u) for `g` gaps and `u` runs, so O(L log U) for `L` runs
    // written in the clauses. What is given up: nothing. Tests:
    // `r7_tests::an_unbounded_regime_whose_clause_repeats_its_unit_is_decided`,
    // `bench::absorbed_clauses_scale`.
    let clauses: Vec<BTreeMap<Int, ResidueSet>> = clauses
        .into_iter()
        .filter(|cl| {
            !cl.iter()
                .any(|(m, s)| unit_mods.get(m).is_some_and(|unit| res_within(unit, s, m)))
        })
        .collect();
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

    // A bounded regime that the coprime base leaves undecided is decided by `sweep_bounded`,
    // whichever step of the base left it so. Before
    // FAIL-omega-negations-slow-7837918895420161952 only the last step, `solve_coprime_system`,
    // fell back to the sweep; the steps before it (`consolidate_prime_powers`, and
    // `literal_to_base_cnf` on a residue set over a composite modulus that is no product of sets
    // over its prime powers, as `x mod 6 != 1`, and a clause whose literals would multiply out)
    // returned `Undecided` at once, which sent the whole formula to the general path. On the
    // chains of that seed this was `[0, 20]` and `[0, 12]` under `x mod 6 in {0, 2..5}`, and the
    // general path, eliminating `x` and asking its parts again, ran past 60 s.
    //
    // Proof that the answer is the regime's: the base steps and `sweep_bounded` take the same
    // regime (`lo`, `hi`, `unit_mods`, `clauses`, after the filter at the start of this
    // function, which keeps the points: its proof is there). `sweep_bounded` gives the least
    // point of `[lo, hi]` that every unit and every clause holds, or `Empty` when there is none
    // (the proof at `sweep_split`), so its answer is exact; it is `Undecided` only where a
    // cover's meter refuses its work.
    //
    // Complexity tradeoff: naive version (before): a bounded regime the base cannot write goes to
    // the general path, whose cost is not bounded in these terms (60 s on the seed's chains, from
    // the general elimination asking the parts of a formula with a dozen moduli). Used: the sweep,
    // whose work is at most that of cutting each modulus into its pieces on one period of the
    // window, `O(N_0 log N_0)` with `N_0 = sum |s| ((e - l) div m + 2)` (the bound at
    // `cheapest_split`), the bound the sweep already has where `solve_coprime_system` falls back to
    // it. What is given up: nothing is answered differently (both answers are exact); a regime the
    // general path answered quickly but whose window is wide against its moduli now pays the
    // sweep's pseudo-polynomial bound instead. The window is cut to one period of the moduli
    // (`sweep_window`), so that bound is at most `O(L p)` for `L` literals and the lcm `p`; the
    // same holds at the fallback after `solve_coprime_system`, which no measurement has shown to
    // be worse than the general path (unproved in general: marked here, ASSUME-sweep-not-worse).
    // Tests: `r7_tests::a_bounded_regime_the_base_cannot_write_is_decided` (against testing each
    // point; undecided before), `l01_38_omega_test::one_scope::
    // no_question_of_a_random_chain_with_negations_is_refused_at_seed_7837918895420161952` (past
    // 60 s before).
    //
    // A regime with one bound or none is swept on one period. With one bound it is the period past the bound, `[l, l + p - 1]` or
    // `[h - p + 1, h]`, with `p` the lcm of its moduli. Proof that this is exact for `[l, inf)`
    // (the case `(-inf, h]` is its mirror): every unit and every literal of a clause reads `x mod
    // m` for a modulus `m` of the regime, and `m` divides `p`, so `x mod m = (x - k p) mod m` for
    // every integer `k`, and `x` and `x - k p` meet the same units and clauses. If `x >= l` is a
    // point of the regime, then `k = (x - l) div p >= 0` gives `y = x - k p` with `0 <= y - l < p`,
    // so `y` is a point in `[l, l + p - 1]`; the window is a part of the regime (it has no upper
    // bound), so it holds a point exactly when the regime does, and a point it gives is one of the
    // regime. Before this, a one-bound regime the base left undecided sent its formula to the
    // general path, which refused the 4 formulas of
    // `bench::one_scope::the_5000_one_variable_modular_formulas_of_seed_0x70dec1de_match_enumeration`
    // still refused (each one variable, a lower bound, and residue conditions), and the program of
    // `checker::a_question_over_one_variable_and_its_remainders_is_decided` (once refused) before
    // it was decided as a bounded regime.
    //
    // A regime with no bound is swept on `[0, p - 1]`. Exact by the same argument with `l = 0`
    // and `k = x div p` (any integer now, since `x` may be negative): `y = x - k p` lies in
    // `[0, p - 1]` and meets the same units and clauses. Why the start 0 does not depend on the
    // names, although the rule above forbids a fixed point of the line such as `x = 1` as a
    // witness: a step with no bound runs only in the coordinate `solve_regime` writes, never in
    // the coordinate of the root. (1) `solve_regime` writes a regime with no bound in the
    // coordinate `t` of one of `free` (I5.3): `x = c + s * t` with `t` the alias of `x` of least
    // offset of its sign, and the aliases of `x` are the same atoms under every name, so a
    // renaming leaves `free`, the chosen writing and so `t = 0` the same point of the program
    // (see `solve_regime`'s doc). (2) `free` is never empty when a regime has no bound:
    // `UnionFind::min_offsets_of` starts each node's best positive offset at `Some(0)`, the node
    // itself, so the root gives `plus = Some(..)`; the fallback in `solve_regime` that solves in
    // the root's coordinate is not reached with no bound. (3) The steps put only bounded tasks
    // on the stack (`solve_short_x_interval`, the one user of `stack`, takes `[l, h]`), so the
    // only task with no bound is the first one, in the coordinate of (1). So the window, and the
    // witness the sweep returns in it, are the same under every name; where the two writings of
    // `free` tie, `solve_regime` returns both mirror points as before. Before this, such a
    // regime was refused (test
    // `checker::a_question_over_one_variable_with_no_bound_and_its_remainders_is_decided`, refused
    // before; row PRES-one-variable-no-bound-witness). Still refused: a formula whose remainders
    // are taken of a multiple or a quotient of `x`, which does not reach this regime (row
    // PRES-one-variable-scaled-and-nested-residues; test
    // `checker::a_refused_question_over_one_scaled_variable_names_its_moduli`).
    //
    // Complexity tradeoff: naive version (before), as for the bounded regime above, the general
    // path, which refused these. Used: the lcm `p`, M - 1 steps of `Int::lcm` over the M moduli
    // (O(M^2 b^2) bit operations for `b`-bit moduli that share no factor), and the sweep on a
    // window of `p` points, whose work is at most `O(L p)` for `L` literals (the bound at
    // `cheapest_split`), refused past the limit under a cover's meter. What is given up: nothing
    // is answered differently; where `p` is huge the sweep is costly, the same tradeoff as the
    // bounded fallback (ASSUME-sweep-not-worse). Tests:
    // `r7_tests::a_regime_with_one_bound_the_base_cannot_write_is_decided` (against testing each
    // point of the period; undecided before), the 5,000-formula test above (4 refusals before, 0
    // after), `r7_tests::bench::a_regime_with_one_bound_and_n_clauses_scales`.
    let out = solve_on_bases(lo, hi, &unit_mods, &clauses);
    match (out, lo, hi) {
        (RegimeOut::Undecided, Some(l), Some(h)) => sweep_bounded(l, h, &unit_mods, &clauses),
        (RegimeOut::Undecided, Some(l), None) => {
            let e = &(l + &period_of(&unit_mods, &clauses)) - &Int::ONE;
            sweep_bounded(l, &e, &unit_mods, &clauses)
        }
        (RegimeOut::Undecided, None, Some(h)) => {
            let s = &(h - &period_of(&unit_mods, &clauses)) + &Int::ONE;
            sweep_bounded(&s, h, &unit_mods, &clauses)
        }
        (RegimeOut::Undecided, None, None) => {
            let e = &period_of(&unit_mods, &clauses) - &Int::ONE;
            sweep_bounded(&Int::ZERO, &e, &unit_mods, &clauses)
        }
        (out, _, _) => out,
    }
}

/// The lcm of the moduli of `unit_mods` and `clauses`, 1 where there are none.
fn period_of(unit_mods: &BTreeMap<Int, ResidueSet>, clauses: &[BTreeMap<Int, ResidueSet>]) -> Int {
    unit_mods
        .keys()
        .chain(clauses.iter().flat_map(|cl| cl.keys()))
        .fold(Int::ONE, |p, m| p.lcm(m))
}

/// The regime `[lo, hi]` under `unit_mods` and `clauses`, solved on the pairwise coprime base of
/// its moduli: each residue set written on the base's prime powers, then
/// `solve_coprime_system`. `Undecided` where a set cannot be written so, or the system is not
/// decided; [`solve_regime_step`] then sweeps a bounded regime.
fn solve_on_bases(
    lo: &Option<Int>,
    hi: &Option<Int>,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> RegimeOut {
    // Build the pairwise coprime base of all moduli appearing in `unit_mods` and `clauses`.
    let mut all_moduli: BTreeSet<Int> = unit_mods.keys().cloned().collect();
    for cl in clauses {
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
    let mod_base = coprime_factorization(&all_moduli);
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

    for (m, s) in unit_mods {
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
                let rq = r.mod_floor(q);
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
            // A clause with no literal is the empty disjunction, false: `literal_to_base_cnf`
            // gives one when every factor of `m` is already fixed to one residue and their CRT
            // combination lies outside `s`. Skipping it, as this loop did, dropped the
            // conjunct, so a point outside `s` was returned (FAIL-omega-boundary-modes-flake:
            // `x mod 6 == 2 && x mod 12 in {5, 6}` on `[0, 16]` gave 2). Proof of `Empty`: the
            // unit `x mod m in s` is a conjunct of the regime and is false at every point.
            if cl.is_empty() {
                return RegimeOut::Empty;
            }
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
    for cl in clauses {
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
            // A product clause with no literal is false (each literal it was built from gave the
            // empty clause, as above), so the clause `cl` is false: every one of its literals is
            // false wherever `allowed` holds, and `cl` is a conjunct of the regime.
            if c.is_empty() {
                return RegimeOut::Empty;
            }
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
        let r = x.mod_floor(&self.max_q);
        if r.mod_floor(&self.stride) != self.u {
            return None;
        }
        Some((&r - &self.u).div_floor(&self.stride))
    }
}

/// Projects a residue set `s` modulo `q` onto `z in [0, q / stride - 1]` under
/// `r = u + stride * z`.
fn project_stride(s: &[(Int, Int)], u: &Int, stride: &Int) -> ResidueSet {
    if *stride == Int::ONE {
        return s.to_vec();
    }
    let mut out = Vec::with_capacity(s.len());
    let step_m1 = stride - &Int::ONE;
    for (a, b) in s {
        let num_a = &(a - u) + &step_m1;
        let za = num_a.div_floor(stride);
        let zb = (b - u).div_floor(stride);
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
        let rem = info.u.mod_floor(q);
        return if res_contains(s_q, &rem) {
            Some(allowed_i.to_vec())
        } else {
            Some(Vec::new())
        };
    }
    let q_z = q.div_floor(&info.stride);
    let proj = project_stride(s_q, &info.u, &info.stride);
    if proj.is_empty() {
        return Some(Vec::new());
    }
    intersect_mod_divisor(allowed_i, &proj, &q_z, &info.z_max_q)
}

/// Returns `Some(rq)` if `info` and `allowed_i` fix `x mod q` to a single residue `rq`.
fn single_residue_mod_q(info: &BaseInfo, allowed_i: &[(Int, Int)], q: &Int) -> Option<Int> {
    if *q <= info.stride {
        return Some(info.u.mod_floor(q));
    }
    if allowed_i.is_empty() {
        return None;
    }
    let q_z = q.div_floor(&info.stride);
    let first = &allowed_i.first()?.0;
    let last = &allowed_i.last()?.1;
    if last == first {
        let r = info.r_from_z(first);
        return Some(r.mod_floor(q));
    }
    // Also check if all intervals in `allowed_i` are singletons with the same residue mod `q_z`.
    let z0 = first.mod_floor(&q_z);
    for (a, b) in allowed_i {
        if a != b || a.mod_floor(&q_z) != z0 {
            return None;
        }
    }
    Some((&info.u + &(&info.stride * &z0)).mod_floor(q))
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
    let step = m_fixed.mod_floor(q_rem);
    let shift = u_fixed.mod_floor(q_rem);
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
                let r = (&shift + &(&step * &y)).mod_floor(q_rem);
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
                let r = (&shift + &(&step * &y)).mod_floor(q_rem);
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
            let rq = r.mod_floor(q);
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
                let rq = r.mod_floor(q);
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

/// The bounded regime `[l, h]` that the coprime path left undecided, decided by a sweep over
/// the points of one period: the first point of `[l, h]` that satisfies every unit and every
/// clause, or `Empty` (FAIL-omega-negations-slow-13254895221319191796).
///
/// Why the coprime path leaves it: its witnesses (`score_witness`, `graph_coloring_witness`,
/// conditional expectations) choose residues on the bases and then place a point of their CRT
/// class in `[l, h]`, which exists only when `[l, h]` holds a whole period or the class happens
/// to meet it; and Stage C stops after one split. A chain of negated conditions at seed
/// 13254895221319191796 gave the regime `[12, 23]` with 11 clauses over the moduli 2 to 8: 12
/// points against a period of 840, left undecided, so each question went to the general path,
/// which spent 4 to 15 s on it and refused (`Shadows`).
///
/// Why one period is enough: each unit and each literal is `x mod m in s` with `m` dividing
/// the lcm `p` of the moduli, so `x` and `x + p` satisfy the same units and clauses. A point
/// `x` of `[l, h]` above `e = min(h, l + p - 1)` has `e = l + p - 1`, and `x - k p` with `k =
/// (x - l) div p` lies in `[l, e]` and satisfies the same; so `[l, h]` has a point exactly when
/// `[l, e]` has one, and the least point of `[l, e]` is the least of `[l, h]` (any smaller point
/// of `[l, h]` lies in `[l, e]`). The point is placed by `l`, so it moves with the coordinate as
/// the other witnesses do (I4.15); `solve_regime` gives the walk both ends.
///
/// How `[l, e]` is searched (PERF-sweep-bounded-wide-interval): the moduli are split in two,
/// the `k` smallest (the set `A`, lcm `q`) and the rest (`B`), with `k` from
/// [`cheapest_split`]; [`sweep_split`] decides the regime for any split, by its own proof. The
/// moduli of `B` are cut into pieces on `[l, e]` and those of `A` are read modulo `q`, so a
/// wide window over large moduli and a few small ones (`x mod 2 == 0 && x mod 991 == 5 && x
/// mod 997 == 1` on `[0, 10^6]`: about 2,000 pieces of the large moduli and `q = 2`, where
/// cutting every modulus made 500,000 pieces of modulus 2) is decided by the pieces of the
/// large moduli alone.
///
/// The class decided in time polynomial in the written bits: the regimes with a split whose
/// `B` moduli cut `[l, e]` into polynomially many pieces (each `B` modulus at least the width
/// of `[l, e]` over a polynomial in the bits) and whose `A` moduli have an lcm `q` of
/// polynomial size; then the bound of [`cheapest_split`] is polynomial, and so is the work. The
/// rest, where every split has many pieces or a large `q`, holds the simultaneous
/// incongruences (units `x mod b_i in [0, b_i) - {a_i}`, an empty set of points exactly when
/// no `x` misses every `a_i mod b_i`): problem AN2 of Garey and Johnson, "Computers and
/// Intractability" (1979), Appendix, sec. A7.1, p. 249, NP-complete, read 2026-11-20 in a
/// scan: "Is there an integer x such that, for 1 <= i <= n, x !≡ a_i (mod b_i)?" (the whole
/// entry, and the proof that the window `[l, e]` keeps it as hard, are in the crate's
/// `lib.rs`, References). So deciding that the set is empty is co-NP-complete. Also read
/// 2026-11-20 (allpapers, full text): Deppert, Jansen and Klein, "Fuzzy Simultaneous
/// Congruences", arXiv:2002.07746, which states that k-Simultaneous Congruences, a point
/// meeting `k` of `n` congruences, "is NP-complete in the weak sense" (Leung and Whitehead)
/// and "also is NP-complete in the strong sense" (Baruah et al.); Campercholi, Castaño and
/// Zigarán, "The complexity of the Chinese Remainder Theorem", arXiv:2307.02617 (deciding
/// whether a system of congruences is solvable in general algebras is coNP-complete);
/// Bliznets, Nederlof and Szilágyi, arXiv:2312.06393 (covering a set by `k` arithmetic
/// progressions in 2^{O(k^2)} poly(n), parameterized by `k`, not by the bits); Ziller and
/// Morack, arXiv:1611.03310 (Jacobsthal's function, the longest run that a residue class of
/// each prime misses: computed by search). None gives a method polynomial in the bits for
/// this problem, so the rest is decided by the same method at the bound of [`cheapest_split`],
/// which is at most that of cutting every modulus into pieces, and under a cover's meter it is
/// refused past the meter's limit (`Refusal::Questions`: "Here those questions would take more
/// work than the checker allows"), as before. Outside a cover nothing limits it, as nothing
/// limits the rest of the solver there: a refusal by size there would be a threshold.
///
/// Complexity tradeoff: the naive way tests each of the `e - l + 1` points against every
/// clause, O((e - l + 1) L) for `L` literals. Before this change every literal was cut into
/// its pieces on `[l, e]`, `N_0 = sum |s| ((e - l) div m + 2)`, sorted once: O(N_0 log N_0),
/// which a wide window over a small modulus makes pseudo-polynomial in the bits. Used: the
/// split of [`cheapest_split`], whose bound is at most a constant times `N_0` (its `k = 0`), so
/// no input costs more than a constant factor more than before, and the work is that of
/// [`sweep_split`] below. Under a cover's meter each part of the work is charged before it is
/// done (`meter::charge_pieces`, `meter::PIECE` units each), so a cover's question stays within
/// its limit (`r7_tests::a_sweep_past_the_limit_is_refused_under_the_meter`). Tests:
/// `r7_tests::a_short_interval_over_many_moduli_is_decided_by_the_sweep` and
/// `r7_tests::every_split_of_the_moduli_decides_a_regime_as_testing_each_point_does` (against
/// testing each point), `r7_tests::a_wide_window_cut_by_large_moduli_is_answered_under_the_meter`
/// and `r7_tests::a_window_of_200_bits_is_answered_under_the_meter` (refused by the meter
/// before this change),
/// `l01_38_omega_test::one_scope::no_question_of_a_random_chain_with_negations_is_refused_at_seed_13254895221319191796`
/// and `one_scope::a_chain_over_a_short_window_of_many_moduli_has_no_question_refused` (each past
/// 60 s without this sweep); the choice of split: `r7_tests::the_split_is_the_one_of_least_bound`;
/// scaling: `bench::one_scope::the_questions_of_a_chain_over_a_short_window_of_many_moduli_scale`,
/// `r7_tests::bench::clauses_over_a_window_of_200_bits_scale` and
/// `r7_tests::bench::a_window_of_n_periods_scale`.
fn sweep_bounded(
    l: &Int,
    h: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> RegimeOut {
    if l > h {
        return RegimeOut::Empty;
    }
    let (e, weights) = sweep_window(l, h, unit_mods, clauses);
    let lists = (unit_mods.len() + clauses.len()) as u128;
    let (k, q) = cheapest_split(&(&e - l), &weights, lists);
    let small: BTreeSet<&Int> = weights.keys().take(k).collect();
    sweep_split(l, &e, unit_mods, clauses, &small, q)
}

/// The end `e = min(h, l + p - 1)` of the one period [`sweep_bounded`] searches, `p` the lcm of
/// the moduli, and the weight of each modulus: the number of intervals of residues its literals
/// hold, which [`cheapest_split`] reads.
fn sweep_window(
    l: &Int,
    h: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> (Int, BTreeMap<Int, u128>) {
    let mut weights: BTreeMap<Int, u128> = BTreeMap::new();
    for (m, s) in unit_mods
        .iter()
        .chain(clauses.iter().flat_map(|cl| cl.iter()))
    {
        let w = weights.entry(m.clone()).or_insert(0);
        *w = w.saturating_add(s.len() as u128);
    }
    // The lcm of a prefix of the moduli divides the lcm `p` of all of them, so it is at most
    // `p`. Once it reaches `h - l + 1`, then `p >= h - l + 1`, so `l + p - 1 >= h` and `e = h`,
    // and the lcm of the rest is not needed. Before that stop each prefix's lcm is below
    // `(h - l + 1) * max m`, so its bits stay O(bits(h - l) + bits(max m)) and each step costs
    // the same at every number of moduli.
    //
    // Complexity tradeoff: forming the whole lcm, as this did before
    // PERF-sweep-bounded-wide-interval, costs Theta(M^2 b^2) bit operations and Theta(M^2 b)
    // bytes for `M` moduli of `b` bits each that share no factor (the lcm grows by `b` bits a
    // modulus), which `r7_tests::bench::clauses_over_a_window_of_200_bits_scale` measured at
    // 34.7 times the bytes at 8n. Used: stop at the window's length, O(M (b + bits(h - l))^2).
    let len = &(h - l) + &Int::ONE;
    let mut period = Int::ONE;
    for m in weights.keys() {
        if period >= len {
            break;
        }
        period = period.lcm(m);
    }
    let e = if period >= len {
        h.clone()
    } else {
        &(l + &period) - &Int::ONE
    };
    (e, weights)
}

/// A count as a `u128`, saturated at `u128::MAX` (a count is never negative here).
fn count_u128(v: &Int) -> u128 {
    v.to_i128()
        .and_then(|v| u128::try_from(v).ok())
        .unwrap_or(u128::MAX)
}

/// The number `k` of the smallest moduli that [`sweep_split`] reads modulo their lcm `q`, and
/// `q`, for a regime on a window `[l, l + span]` whose moduli have the weights `weights` (the
/// number of intervals of residues their literals hold) and which has `lists` units and clauses.
///
/// For each `k` from 0 to the number `M` of moduli, with `A` the `k` smallest, `B` the rest,
/// `w_m` the weight of `m`, the bound
///
/// `U_k = P + q + (2 P + lists + 1) D`, `P = sum over B of w_m (span div m + 2)`,
/// `D = 1 + sum over A of w_m (q div m + 2)`,
///
/// is an upper bound on the work of [`sweep_split`] in units of one piece or one tree step
/// (each times a factor `log` of the sizes, the same for every `k`): `P` bounds its pieces of
/// the moduli of `B`, so at most `2 P` events and `2 P + 1` segments; `q` its tree; `D` the
/// intervals of residues that any one unit or clause forbids modulo `q` (each `A` literal
/// lifted modulo `q` has at most `w (q div m + 2)` intervals, and the complement of `c`
/// intervals at most `c + 1`), so each unit or clause put in the tree at the start (`lists`)
/// and each event costs at most `D` tree steps, and each segment one search. The `k` with the
/// least bound is taken, the least `k` at a tie, so the choice is fixed by the input. `U_0 =
/// 3 P + lists + 2` with `P = N_0`, the pieces of cutting every modulus: no choice is more
/// than a constant factor above that. The same holds for space: the chosen `q` is at most its
/// bound, at most `U_0`, so the tree's `4 q` items are never more than a constant times the
/// pieces that cutting every modulus held. This compares exact counts of work and changes no
/// answer: every `k` is decided exactly (no threshold; P196/P197).
///
/// `q` must have an item for each residue, so a `k` whose `q` is past `usize` cannot be run;
/// `q` only grows with `k`, so the scan stops there. Cost: O(M) steps of arithmetic on the
/// moduli, after their sort (the keys of `weights`).
///
/// Complexity tradeoff: the naive way runs [`sweep_split`] at each `k` and keeps the fastest,
/// O(M) times its work. Used: the bound, kept up to date as `k` grows (`q` by the lcm with the
/// next modulus, the sum `sum over A of w_m (q div m)` scaled by the factor `q` grew by, the
/// sum over `B` from a suffix sum), O(M) in all. Test:
/// `r7_tests::the_split_is_the_one_of_least_bound`.
fn cheapest_split(span: &Int, weights: &BTreeMap<Int, u128>, lists: u128) -> (usize, usize) {
    let ms: Vec<(&Int, u128)> = weights.iter().map(|(m, w)| (m, *w)).collect();
    // `after[i]`: the pieces of the moduli from the `i`-th on, `P` at `k = i`.
    let mut after = vec![0u128; ms.len() + 1];
    for (i, (m, w)) in ms.iter().enumerate().rev() {
        let per = count_u128(&span.div_floor(m)).saturating_add(2);
        after[i] = after[i + 1].saturating_add(w.saturating_mul(per));
    }
    let bound = |p: u128, q: u128, d: u128| {
        p.saturating_add(q).saturating_add(
            p.saturating_mul(2)
                .saturating_add(lists)
                .saturating_add(1)
                .saturating_mul(d),
        )
    };
    let mut best = (bound(after[0], 1, 1), 0, 1usize);
    let mut q = Int::ONE;
    // `sum over A of w_m (q div m)` and `sum over A of w_m`.
    let (mut lifted, mut weight) = (0u128, 0u128);
    for (k, (m, w)) in ms.iter().enumerate().map(|(i, x)| (i + 1, x)) {
        let grow = m.div_floor(&q.gcd(m));
        q = &q * &grow;
        let Some(q_items) = q.to_i128().and_then(|v| usize::try_from(v).ok()) else {
            break;
        };
        lifted = lifted
            .saturating_mul(count_u128(&grow))
            .saturating_add(w.saturating_mul(count_u128(&q.div_floor(m))));
        weight = weight.saturating_add(*w);
        let d = lifted
            .saturating_add(weight.saturating_mul(2))
            .saturating_add(1);
        let u = bound(after[k], q_items as u128, d);
        if u < best.0 {
            best = (u, k, q_items);
        }
    }
    (best.1, best.2)
}

/// The least point of `[l, e]` that every unit and every clause holds, or `Empty`, where `e -
/// l` is below the lcm of the moduli ([`sweep_bounded`]), and `small` (lcm `q`, which fits
/// `usize`) holds the moduli read modulo `q`; every other modulus is large. `Undecided` where a
/// cover's meter refuses the work.
///
/// Proof. (1) A literal `x mod m in s` with `m` small holds at `x` exactly when `x mod q`
/// lies in the residues `r` of `[0, q)` with `r mod m in s`, since `m` divides `q`, so `x mod
/// m = (x mod q) mod m`; those residues are `concrete_intervals_in_span(0, q - 1, m, ...)`.
/// (2) The pieces on `[l, e]` of each unit over a large modulus, and of the literals over
/// large moduli of each clause, joined where they overlap or touch, are normal lists: disjoint
/// and not adjacent, so `x` enters a list's set at the low end `a` of a joined piece and leaves
/// it at `b + 1`, and at no other place. [`LargeMerge`] yields exactly those places, in order,
/// with the lists whose state changes there (its proof). Between two consecutive places where
/// some list is entered or left (the events), every unit over a large modulus holds everywhere
/// or nowhere, and so does every clause's part over large moduli: the events cut `[l, e]` into
/// segments, each with one state. (3) On a segment where a large unit fails, or a clause with no
/// small literal has its large part false, no point lies.
/// Elsewhere `x` of the segment is a point exactly when each
/// small unit holds and each clause whose large part is false there (an active clause) has a
/// small literal that holds, all of which depend on `x mod q` alone, by (1). The tree holds, for
/// each residue `r`, the number of small units and active clauses that forbid it (whose
/// residues, by (1), miss `r`); it is kept exact by adding 1 over a clause's forbidden
/// residues when the clause becomes active and taking it off when it stops (in its own list
/// the two alternate, by (2), and the clause is active before `l`, where no piece lies). So `x`
/// is a point exactly when the count at `x mod q` is 0. (4) The least point at or after the
/// segment's start `t` with `r_0 = t mod q`: a residue `r >= r_0` with count 0 gives `t + (r -
/// r_0) < t + q - r_0`, below every point `t + (q - r_0) + r'` from a residue below `r_0`, so
/// the least is from the first `r >= r_0` with count 0, else from the first `r` with count 0
/// overall, by `MinAdd::first_at_most` (the counts are never below 0); it is a point of the
/// segment when it is at most the segment's end. (5) The segments are taken in order along
/// `[l, e]`, which they cover, so the first point found is the least, and none found is `Empty`.
///
/// Complexity tradeoff: the naive way, testing each point, is O((e - l + 1) L) for `L`
/// literals; cutting every modulus into pieces is O(N_0 log N_0) ([`sweep_bounded`]). Used: `P`
/// pieces of the large moduli, made in order by [`LargeMerge`], O(P log S) for the `S`
/// intervals of residues of the large literals (`S <= P`); the small literals read modulo `q`,
/// O(q + sum over them of |s| (q div m + 2)); and for each of the at most `2 P` events and each
/// clause and unit at the start, one addition to the tree for each interval of residues that
/// clause or unit forbids, `I_j` of them, plus one search for each segment, O(log q) each. In
/// all O(P log S + q + (sum over clauses j of (2 P_j + 1) I_j + sum over small units of I_u +
/// P) log q), with `P_j` the pieces of clause `j`'s large part: linear in the number of
/// clauses when each has few pieces and few forbidden intervals, where meeting each active
/// clause on each segment is O(P L). Under a cover's meter each part is charged before it is
/// done: the walk's events and tree steps are counted by a first pass of [`LargeMerge`] with no
/// tree, so the charge is the exact count the walk then makes (the same as when the pieces were
/// all made and sorted first), at twice the merge's time and only while a meter runs.
///
/// Space (PERF-sweep-lazy-pieces): before, the `P` pieces were all made, joined and sorted as
/// up to `2 P` events, Theta(P) space, which `r7_tests::bench::a_window_of_n_periods_scale`
/// grew with the number of periods of its window. Used: the pieces made lazily in order of
/// their ends, one waiting event per interval of residues, so space is O(S + L + q + sum I_j)
/// for `L` units and clauses, whatever the width of `[l, e]`; the time bound is unchanged up
/// to the factor `log S <= log P` in place of `log P`.
fn sweep_split(
    l: &Int,
    e: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
    small: &BTreeSet<&Int>,
    q: usize,
) -> RegimeOut {
    let span = e - l;
    let q_int = Int::from(q);
    let charge =
        |count: u128| super::meter::charge_pieces(u64::try_from(count).unwrap_or(u64::MAX));
    // The pieces of the large moduli and the residues of the small ones, charged first.
    let mut cut: u128 = 0;
    let mut lift: u128 = q as u128;
    for (m, s) in unit_mods
        .iter()
        .chain(clauses.iter().flat_map(|cl| cl.iter()))
    {
        let wide = if small.contains(m) { &q_int } else { &span };
        let per = count_u128(&wide.div_floor(m)).saturating_add(2);
        let n = per.saturating_mul(s.len() as u128);
        if small.contains(m) {
            lift = lift.saturating_add(n);
        } else {
            cut = cut.saturating_add(n);
        }
    }
    if charge(cut.saturating_add(lift)).is_err() {
        return RegimeOut::Undecided;
    }
    let top = Int::from(q - 1);
    // The residues of `[0, q)` a set of small literals does not allow, as items of the tree:
    // O(q) intervals at most, as the tree has items.
    let forbidden = |lits: &mut dyn Iterator<Item = (&Int, &ResidueSet)>| -> Vec<(usize, usize)> {
        let mut allowed = Vec::new();
        for (m, s) in lits {
            for (ra, rb) in s {
                allowed.extend(concrete_intervals_in_span(&Int::ZERO, &top, m, ra, rb));
            }
        }
        intervals::complement(&intervals::coalesce(allowed), Int::ZERO, top.clone())
            .into_iter()
            .map(|(a, b)| (residue_item(&a), residue_item(&b)))
            .collect()
    };
    let mut tree = zed_collections::min_add::MinAdd::new(q);
    // The lists of [`LargeMerge`]: each unit over a large modulus, then each clause's literals
    // over large moduli (none for a clause with no large literal, whose large part is false
    // everywhere).
    let mut lists: Vec<Vec<(&Int, &ResidueSet)>> = Vec::new();
    for (m, s) in unit_mods {
        if small.contains(m) {
            for (a, b) in forbidden(&mut std::iter::once((m, s))) {
                tree.add(a, b, 1);
            }
        } else {
            lists.push(vec![(m, s)]);
        }
    }
    let large_units = lists.len();
    // Each clause's forbidden residues, `None` for a clause with no small literal; every clause
    // is active before `l`.
    let mut clause_forbids: Vec<Option<Vec<(usize, usize)>>> = Vec::with_capacity(clauses.len());
    let mut dead = 0usize;
    for cl in clauses {
        let has_small = cl.keys().any(|m| small.contains(m));
        let forbids =
            has_small.then(|| forbidden(&mut cl.iter().filter(|(m, _)| small.contains(m))));
        lists.push(cl.iter().filter(|(m, _)| !small.contains(m)).collect());
        match &forbids {
            Some(f) => {
                for &(a, b) in f {
                    tree.add(a, b, 1);
                }
            }
            None => dead += 1,
        }
        clause_forbids.push(forbids);
    }
    // The tree's work for the events and searches, charged before the walk: each event (a list
    // entered or left) once, and for clause `j`, entered `c_j` times, `(2 c_j + 1)` times the
    // intervals it forbids (1 with none). These are the counts of the walk below, which makes
    // the same events (by the proof of [`LargeMerge`]); a first merge with no tree counts them.
    // With no meter the charge does nothing, so the count is made only under one.
    if super::meter::running() {
        let mut count = LargeMerge::new(l, e, &lists);
        let (mut events, mut entered) = (0u128, vec![0u128; clauses.len()]);
        while count.next_change().is_some() {
            for &j in &count.changed {
                events += 1;
                if j >= large_units && count.holds[j] {
                    entered[j - large_units] += 1;
                }
            }
        }
        let toggles = clause_forbids
            .iter()
            .zip(&entered)
            .fold(0u128, |t, (f, c)| {
                let width = f.as_ref().map_or(1, |f| f.len() as u128);
                t.saturating_add((2 * c + 1).saturating_mul(width))
            });
        if charge(toggles.saturating_add(events + 1)).is_err() {
            return RegimeOut::Undecided;
        }
    }
    let mut merge = LargeMerge::new(l, e, &lists);
    let mut at = merge.next_change();
    let (mut start, mut inside) = (l.clone(), 0usize);
    loop {
        if at.as_ref() == Some(&start) {
            for &j in &merge.changed {
                let holds = merge.holds[j];
                if j < large_units {
                    if holds {
                        inside += 1;
                    } else {
                        inside -= 1;
                    }
                    continue;
                }
                let d = if holds { -1 } else { 1 };
                match &clause_forbids[j - large_units] {
                    Some(f) => {
                        for &(a, b) in f {
                            tree.add(a, b, d);
                        }
                    }
                    None if holds => dead -= 1,
                    None => dead += 1,
                }
            }
            at = merge.next_change();
        }
        let end = match &at {
            Some(next) => next - &Int::ONE,
            None => e.clone(),
        };
        if inside == large_units && dead == 0 {
            let r0 = residue_item(&start.mod_floor(&q_int));
            let step = match tree.first_at_most(r0, 0) {
                Some(r) => Some(r - r0),
                None => tree.first_at_most(0, 0).map(|r| q - r0 + r),
            };
            if let Some(step) = step {
                let x = &start + &Int::from(step);
                if x <= end {
                    return RegimeOut::Found(x);
                }
            }
        }
        match &at {
            Some(next) => start = next.clone(),
            None => return RegimeOut::Empty,
        }
    }
}

/// One interval of residues `[ra, rb]` of a literal `x mod m in s` over a large modulus, read
/// along `[l, e]` one block `[base, base + m)` at a time: its pieces are `[max(base + ra, l),
/// min(base + rb, e)]` where not empty.
struct ResidueRun<'a> {
    /// The list of [`LargeMerge`] the literal belongs to.
    list: usize,
    m: &'a Int,
    ra: &'a Int,
    rb: &'a Int,
    /// The low end of the current block, a multiple of `m`.
    base: Int,
    /// The high end of the current piece.
    end: Int,
    /// Whether the event waiting in the heap is the current piece's low end (else its high
    /// end plus one).
    entering: bool,
}

/// The places along `[l, e]` where a list of residue literals over large moduli (each a unit,
/// or a clause's large part, of [`sweep_split`]) is entered or left, in increasing order, each
/// with the lists whose state changes there ([`LargeMerge::next_change`]), made lazily: a
/// k-way merge, by a heap, of the pieces of each interval of residues, one event of each
/// waiting (PERF-sweep-lazy-pieces).
///
/// Proof. (1) Order: each run's events are the low end `a` of a piece, then its high end plus
/// one `b + 1 > a` (where `b < e`), then the low end of its next block's piece, at least `b +
/// 1`, since `(base + m) + ra >= base + rb + 1` as `ra >= 0` and `rb <= m - 1`; only the first
/// block is clipped by `l`,
/// and every later low end `base + ra` is above `l`, as `base > l`. So each event pushed is at or
/// after the one just popped, and the heap pops all events in increasing order of place (a
/// k-way merge); `next_change` takes every event at one place before it looks at the lists, an
/// event pushed at the same place included (`a = b + 1` when `[ra, rb]` is all of `[0, m)`).
/// (2) Counts: after the events at places up to `x`, `count[j]` is the number of pieces of list
/// `j` with `a <= x` less those with `b + 1 <= x`, that is (as `a <= b`) the number holding
/// `x`, so list `j` holds at `x` exactly when `count[j] > 0`. (3) Changes: `holds[j]` is kept
/// equal to `count[j] > 0` after each place, for the lists an event there touched (no other
/// count changed), so it changes exactly where the union of the list's pieces is entered or left,
/// the low ends of its joined pieces and their high ends plus one, at most `e`: the events of
/// [`sweep_split`]'s proof (2). A place where counts change and no list's state does is passed
/// over, so the walk's segments and tree steps are those of the joined pieces.
///
/// Complexity tradeoff: making every piece on `[l, e]`, joining each list's and sorting the ends
/// (as before) takes O(P log P) time and Theta(P) space for `P` pieces. Used: O(log S) a piece
/// for the `S` runs, with space O(S + lists): the window's width changes the time only.
struct LargeMerge<'a> {
    l: &'a Int,
    e: &'a Int,
    runs: Vec<ResidueRun<'a>>,
    /// The waiting event of each run not done, by place and then run.
    heap: MinHeap<(Int, usize)>,
    /// For each list, the number of its pieces that hold the place last taken.
    count: Vec<usize>,
    /// For each list, whether it holds at the place last taken: `count > 0`.
    holds: Vec<bool>,
    /// The lists whose state changed at the place [`LargeMerge::next_change`] last gave.
    changed: Vec<usize>,
    /// The lists an event touched at the place being taken, with repeats.
    touched: Vec<usize>,
}

impl<'a> LargeMerge<'a> {
    /// The merge of `lists`, every list not holding before `l`.
    fn new(l: &'a Int, e: &'a Int, lists: &[Vec<(&'a Int, &'a ResidueSet)>]) -> LargeMerge<'a> {
        let mut merge = LargeMerge {
            l,
            e,
            runs: Vec::new(),
            heap: MinHeap::new(),
            count: vec![0; lists.len()],
            holds: vec![false; lists.len()],
            changed: Vec::new(),
            touched: Vec::new(),
        };
        for (list, lits) in lists.iter().enumerate() {
            for &(m, s) in lits {
                for (ra, rb) in s {
                    // The block of `l`, or the next one where the interval ends before `l`.
                    let mut base = &l.div_floor(m) * m;
                    if &(&base + rb) < l {
                        base = &base + m;
                    }
                    merge.runs.push(ResidueRun {
                        list,
                        m,
                        ra,
                        rb,
                        base,
                        end: Int::ZERO,
                        entering: true,
                    });
                    merge.enter(merge.runs.len() - 1);
                }
            }
        }
        merge
    }

    /// Makes run `i`'s piece in its current block and pushes its low end, or ends the run where
    /// the block starts past `e`. The piece is empty only then: its block ends at or after `l`
    /// (`base + rb >= l`, by [`LargeMerge::new`] for the first and `base > l` after), so
    /// `max(base + ra, l) <= min(base + rb, e)` fails only where `base + ra > e`, and every
    /// later block starts further on.
    fn enter(&mut self, i: usize) {
        let (l, e) = (self.l, self.e);
        let run = &mut self.runs[i];
        let a = (&run.base + run.ra).max(l.clone());
        let b = (&run.base + run.rb).min(e.clone());
        if a <= b {
            run.end = b;
            run.entering = true;
            self.heap.push((a, i));
        }
    }

    /// The next place where some list is entered or left, with those lists in `changed` and
    /// their new states in `holds`; `None` past the last.
    fn next_change(&mut self) -> Option<Int> {
        loop {
            let at = self.heap.peek()?.0.clone();
            self.touched.clear();
            while self.heap.peek().is_some_and(|(place, _)| *place == at) {
                let (_, i) = self.heap.pop().expect("an event was peeked");
                let run = &mut self.runs[i];
                let list = run.list;
                if run.entering {
                    self.count[list] += 1;
                    if run.end < *self.e {
                        run.entering = false;
                        self.heap.push((&run.end + &Int::ONE, i));
                    }
                } else {
                    self.count[list] -= 1;
                    run.base = &run.base + run.m;
                    self.enter(i);
                }
                self.touched.push(list);
            }
            self.changed.clear();
            for &j in &self.touched {
                if (self.count[j] > 0) != self.holds[j] {
                    self.holds[j] = !self.holds[j];
                    self.changed.push(j);
                }
            }
            if !self.changed.is_empty() {
                return Some(at);
            }
        }
    }
}

/// A residue of `[0, q)` with `q` an item count, as the index of its item.
fn residue_item(r: &Int) -> usize {
    r.to_i128()
        .and_then(|v| usize::try_from(v).ok())
        .expect("a residue below an item count fits usize")
}

/// Concrete sub-intervals `[il, ih] subseteq [l, h]` where `x mod m in [ra, rb]`.
fn concrete_intervals_in_span(l: &Int, h: &Int, m: &Int, ra: &Int, rb: &Int) -> Vec<(Int, Int)> {
    let q_l = l.div_floor(m);
    let r_l = l.mod_floor(m);
    let q_h = h.div_floor(m);
    let r_h = h.mod_floor(m);
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
        if !res_contains(s, &x.mod_floor(m)) {
            return false;
        }
    }
    for cl in clauses {
        if !cl.iter().any(|(m, s)| res_contains(s, &x.mod_floor(m))) {
            return false;
        }
    }
    true
}

// The product and remainder trees here are the kernel's (`zed_kernel::num::trees`, shared with
// `zedc-int` and `zedc-check`), over `BigUint`. This file had its own copy over `Int`; the two
// took the same time (DRY-number-theory-wide, 2026-11-19, opt-level 2, load 40 to 50: ratio
// kernel/own 0.94 and 1.07 for `shares_a_factor_by_tree` on 512 and 4096 word values, 1.00
// and 1.03 on 32 and 256 values of 40 words; 0.68 to 1.08 for `batch_remainders`), so the
// copy was removed. The values reaching the trees are at least 1, so their magnitudes are the
// values.

/// `vals` (each at least 1) as `BigUint`, the kernel's trees' leaves.
fn uint_leaves(vals: &[Int]) -> Vec<BigUint> {
    vals.iter().map(Int::magnitude).collect()
}

/// A `BigUint` from the kernel back as an `Int`.
fn from_uint(v: BigUint) -> Int {
    Int::from(BigInt::from(v))
}

/// Each modulus with its factors `(b, b^e)` over one set of pairwise coprime bases `b`, by
/// increasing `b`; `b^e` is the largest power of `b` that divides the modulus.
type ModBase = BTreeMap<Int, Vec<(Int, Int)>>;

/// Factors every modulus in `moduli` over their natural coprime base, by zed-kernel's
/// `num::coprime::coprime_base` (D. J. Bernstein, "Factoring into coprimes in essentially
/// linear time", J. Algorithms 54(1), 2005, doi:10.1016/j.jalgor.2004.04.009; the method, the
/// proof that its base is the natural one, and its cost are in that module's comment). That is
/// the one copy for zedc-int, zedc-check and this crate (DRY-coprime-bases-one, 2026-11-20).
/// This file had its own copy over `Int` (Algorithms 11.3, 11.4, 13.2, 16.2, 17.3, 18.1 and
/// 21.2), which gave no answer where a product tree was not as built; the kernel's has no
/// such path, so every set of moduli is factored. The natural coprime base is unique
/// (Bernstein, Theorem 7.3), so both copies give the same factors.
///
/// A modulus coprime to all the others is its own base; the kernel finds these first by
/// `num::coprime::shares_a_factor`: from a table of least prime factors, in O(N) word
/// operations, when the largest modulus is at most `N`, and otherwise by one product tree and
/// one remainder tree, in O(M(N) log k) for `k` moduli of `N` bits in all, where `M` is the
/// cost of multiplying numbers of `N` bits.
///
/// Complexity tradeoff: pairwise refinement and scanning each base per modulus cost O(k^2)
/// arithmetic operations; the kernel's product trees cost O(M(N) log N log k) a merge, with a
/// factor `log k` for the halves (a polylogarithmic factor, not a proved O(n log n) bound).
/// Before it, `common_factorization` recognizes moduli `g q_i` with the `q_i` coprime to each
/// other and to `g` in O(N) or O(M(N) log k), where the kernel's halves would merge all `k`
/// moduli, as every one shares `g`. No modulus or answer is given up. Tests:
/// pncx_common_factors_reconstruct_inputs, pncx_coprime_factorization_has_its_answers;
/// benches pncx_common_factor_scale and pncx_coprime_dense_scale (table side), and
/// pncx_shared_formula_scale through `solve_modular`'s private quotient consistency check.
/// The tree side (pncx_common_factor_tree_side_scale and
/// the kernel's the_coprime_base_of_distinct_primes_scales) is deferred to plan row
/// PERF-negated-chain-unsolved in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
fn coprime_factorization(moduli: &BTreeSet<Int>) -> ModBase {
    let ms: Vec<Int> = moduli.iter().filter(|m| **m > Int::ONE).cloned().collect();
    // A modulus 1 (if any) has no factors.
    let mut out: ModBase = moduli
        .iter()
        .filter(|m| **m <= Int::ONE)
        .map(|m| (m.clone(), Vec::new()))
        .collect();
    if ms.is_empty() {
        return out;
    }
    if let Some(complete) = common_factorization(&ms) {
        out.extend(complete);
        return out;
    }
    let cb = coprime::coprime_base(&uint_leaves(&ms));
    let bases: Vec<Int> = cb.elements.into_iter().map(from_uint).collect();
    for (m, fs) in ms.into_iter().zip(cb.factors) {
        let mut fs: Vec<(Int, Int)> = (fs.into_iter())
            .map(|(e, q)| (bases[e as usize].clone(), from_uint(q)))
            .collect();
        fs.sort();
        out.insert(m, fs);
    }
    out
}

/// A shared factor with independent cofactors needs no base refinement.
// Complexity tradeoff: pairwise refinement is quadratic on g p_i. A running
// gcd, followed by the kernel's `num::coprime::shares_a_factor` on the cofactors (each at
// least 1, as `g` divides every modulus), recognizes the complete
// factorization in O(B) word operations when the largest cofactor is at most
// the cofactors' B bits (the table method), and in O(M(B) log k) otherwise (one
// product/remainder tree). Failure gives no verdict and Bernstein's general
// method continues (doi:10.1016/j.jalgor.2004.04.009; the full comment is in zed-kernel
// `num/coprime.rs`, at its head). Bench: pncx_common_factor_scale (table side); the tree side
// is over the limit of 10.5 at every size that fits in 60 s (plan row
// PERF-negated-chain-unsolved, U1; its bench pncx_common_factor_tree_side_scale is
// deferred in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs).
fn common_factorization(ms: &[Int]) -> Option<ModBase> {
    let mut g = ms.first()?.clone();
    for m in &ms[1..] {
        g = g.gcd(m);
        if g == Int::ONE {
            return None;
        }
    }
    let qs: Vec<_> = ms.iter().map(|m| m.div_floor(&g)).collect();
    if qs.iter().any(|q| q.gcd(&g) != Int::ONE) {
        return None;
    }
    if coprime::shares_a_factor(&uint_leaves(&qs)).contains(&true) {
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
        let ql = lo.div_floor(q_z);
        let qh = hi.div_floor(q_z);
        if ql == qh {
            let rl = lo.mod_floor(q_z);
            let rh = hi.mod_floor(q_z);
            let base = &ql * q_z;
            for (sl, sh) in res_intersect(&[(rl, rh)], s_z) {
                out.push((&base + &sl, &base + &sh));
            }
        } else if qh == &ql + &Int::ONE {
            let rl = lo.mod_floor(q_z);
            let base_l = &ql * q_z;
            for (sl, sh) in res_intersect(&[(rl, q_z - &Int::ONE)], s_z) {
                out.push((&base_l + &sl, &base_l + &sh));
            }
            let rh = hi.mod_floor(q_z);
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
            let q_z = q.div_floor(&stride);
            rem_powers.push((q_z, proj));
        }
    }

    let z_max_q = max_q.div_floor(&stride);
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
/// `allowed[0..t]` (in `z_i in [0, bases_info[i].z_max_q - 1]`) and clauses `clauses` on
/// `[lo, hi]`.
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
///
/// Proof that a point given meets every clause: each clause holds two atoms `i`, `j`, each
/// allowed three values, and is false exactly at the one pair of the values each leaves out,
/// so the clauses of an edge exclude pairs of values, here three forming a perfect matching
/// (`perm`). The labels are permutations of the colors 0, 1, 2 carried across each edge so
/// that the two values of every excluded pair get one color, checked on every edge. The
/// colors are a proper 3-coloring: the core (every vertex of degree 3 or more among those
/// left) is colored two ways if bipartite, else by [`brooks::color`] (Baetz and Wood,
/// doi:10.48550/arXiv.1401.8023, Lemmata 1-3) or [`brooks::universal`], and `None` if
/// neither colors it; the vertices taken out, each with at most 2 neighbors left when taken
/// out, are colored in the reverse order, so at most 2 colors are used next to each. Each
/// atom takes the value labeled by its color, so the two ends of an edge take values of
/// different colors, which is no excluded pair. A `None` is no verdict; the caller checks
/// every point found ([`solve_modular_whole`]), so this proof bears on whether a point is
/// found, and not on whether one given is right.
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
            choices.push((point.mod_floor(&base.max_q), base.max_q));
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

        // Check if the progression `x = r0 + m0 * y` meets `[lo, hi]`, and if `m0` reduces
        // `[lo, hi]` so that some unfixed base `z_max_q > hi_y - lo_y` has single-residue
        // exclusions!
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
            // `bases_info[i].z_max_q > hy - ly` whose forbidden set consists of single residues
            // `z_f`, each forbidden `z_f` maps to a single residue `r_y` modulo `z_max_q`, cutting
            // at most 1 integer out of `[ly, hy]`! Why: `z = r0_z + m0_z * y`, and when `m0_z` has
            // an inverse modulo `z_q` (the only case cut below), `z == z_f (mod z_q)` holds exactly
            // when `y == (z_f - r0_z) * inv_m0 (mod z_q)`, one class; `[ly, hy]` holds
            // `width_y + 1 <= z_q` integers, so it meets that class at most once. The cut below
            // does not rely on this: it cuts every interval `concrete_intervals_in_span` returns.
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
                    let u_inv = (-&(&r0_z * &inv_m0)).mod_floor(z_q);
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
        zed_collections::sorted::sort_dedup(&mut clauses);

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
            let g = num.gcd(&den);
            let sh = (num.div_floor(&g), den.div_floor(&g));
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
    let g = num.gcd(&den);
    (num.div_floor(&g), den.div_floor(&g))
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
                            let g = num.gcd(&den);
                            w_sum = rat_add(&w_sum, &(num.div_floor(&g), den.div_floor(&g)));
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
                        let g = num.gcd(&den);
                        weights[b_idx] = (num.div_floor(&g), den.div_floor(&g));
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
        let u_inv = (-&(&r_cur_z * &inv_m)).mod_floor(z_q);
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
    zed_collections::sorted::sort_dedup(&mut cuts);

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
    let g = m1.gcd(m2);
    let diff = r2 - r1;
    if !diff.mod_floor(&g).is_zero() {
        return None;
    }
    let m2_g = m2.div_floor(&g);
    let u = inverse_mod(&m1.div_floor(&g), &m2_g)?;
    let lcm = m1 * &m2_g;
    let step = (&diff.div_floor(&g) * &u).mod_floor(&m2_g);
    let r = (r1 + &(m1 * &step)).mod_floor(&lcm);
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
/// `r4_tests::the_crt_tree_solves_its_congruences`; bench `pncx_fibonacci_crt_scale`
/// (tests/steps/l01_38_presburger/bench/pncx_probe.rs).
fn combine_crt_tree(mut pairs: Vec<(Int, Int)>) -> Option<(Int, Int)> {
    if pairs.is_empty() {
        return Some((Int::ZERO, Int::ONE));
    }
    pairs.retain(|(_, m)| *m != Int::ONE);
    if pairs.is_empty() {
        return Some((Int::ZERO, Int::ONE));
    }
    // The moduli are above 1 here, so their magnitudes are the moduli.
    let leaves: Vec<BigUint> = pairs.iter().map(|(_, m)| m.magnitude()).collect();
    let levels = trees::product_tree(&leaves);
    let cof = trees::cofactors_mod_leaves(&leaves, &levels);
    let mut vals: Option<Vec<BigUint>> = Some(Vec::with_capacity(pairs.len()));
    for ((r, m), e) in pairs.iter().zip(cof) {
        let Some(inv) = inverse_mod(&from_uint(e), m) else {
            vals = None;
            break;
        };
        if let Some(v) = vals.as_mut() {
            // `mod_floor` by `m > 0` is in `[0, m)`, so its magnitude is the value.
            v.push((&r.mod_floor(m) * &inv).mod_floor(m).magnitude());
        }
    }
    if let Some(mut vals) = vals {
        // Up the tree, the leaves first and every level below the root: each node's value is
        // `v_left P_right + v_right P_left`; an odd node carried up keeps its value.
        // Complexity tradeoff: the products and the last remainder go through the kernel's
        // `mul_uint` and `rem_uint` (transforms and Newton's reciprocal past 512 words), so a
        // level costs O(M(N)) and the whole O(M(N) log k). num-bigint's own `*` and `%`, used
        // here before (PERF-negated-chain-unsolved, negchain1), are Karatsuba and schoolbook
        // division, O(N^1.58) and O(N^2) at the root. Measured 2026-11-20 (load 42, the first
        // 2048 and 16384 odd primes): 23.673 before, 23.279 after, still over the limit 10.5
        // and open on that row. By phase at those sizes (instructions): the product tree 23x,
        // the cofactor descent of `trees::cofactors_mod_leaves` 31x (72% of the work at
        // 16384), the leaf inverses 9.1x, this step up the tree 9.0x. The excess is the
        // multiplication's own growth between about 100 and 2000 words (a squaring costs 83 k
        // instructions at 111 words, 2.8 M at 1100 and 4.3 M at 2173), where the top levels at
        // 16384 lie and none at 2048 do. The method's order does not meet the limit either:
        // `N` grows about 9.6 times at 8 times the primes, and O(M(N) log k) with `M(N) = N log
        // N` predicts about 9.6 (ln 9.6 N / ln N)^2 = 14 here; no method of lower order is known.
        let below_root = &levels[..levels.len().saturating_sub(1)];
        for prods in std::iter::once(&leaves).chain(below_root) {
            vals = (vals.chunks(2).zip(prods.chunks(2)))
                .map(|(v, p)| match (v, p) {
                    ([v0, v1], [p0, p1]) => mul_uint(v0, p1) + mul_uint(v1, p0),
                    _ => v[0].clone(),
                })
                .collect();
        }
        let big_m = trees::tree_product(&leaves, &levels).into_owned();
        let x = rem_uint(vals.first()?, &big_m);
        return Some((from_uint(x), from_uint(big_m)));
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
    let lo_y = lo.as_ref().map(|l| -(&(r0 - l).div_floor(m0)));
    let hi_y = hi.as_ref().map(|h| (h - r0).div_floor(m0));
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
        let x = l + &(r0 - l).mod_floor(m0);
        return hi.as_ref().is_none_or(|h| x <= *h).then_some(x);
    }
    if let Some(h) = hi
        && *h < Int::ZERO
    {
        let x = h - &(h - r0).mod_floor(m0);
        return lo.as_ref().is_none_or(|l| x >= *l).then_some(x);
    }
    let r_pos = r0.mod_floor(m0);
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
        let q_div = (&sx_val + &gq.c_lo).div_floor(&gq.m);
        let q_val = if gq.sigma_q > 0 { q_div } else { -&q_div };
        model.insert(q_root.clone(), q_val);
    }

    // Local existential quotients `q_root`:
    for (q_root, wins) in local_windows {
        let mut chosen_q = Int::ZERO;
        for lw in wins {
            let sx_val = if lw.s_x > 0 { x_val.clone() } else { -x_val };
            let u = &sx_val + &lw.c_lo;
            if u.mod_floor(&lw.m) <= lw.w {
                let q_div = u.div_floor(&lw.m);
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
        let (root, s, d) = uf.tree_get(a);
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
/// `x mod a == a_j || x mod b == b_j || x in D`, with one interval or empty `D`, the three `a_j`
/// distinct and the three `b_j` distinct, force `x` into `D`, since outside `D` the one value of
/// `x mod a` and the one of `x mod b` satisfy at most two of them. Clauses are grouped by
/// `(D, a, b)`; a group tests for a matching of three pairs, independently of the order in which
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
    // the root the names choose (I4.15). With no bound every choice gives a point: when CRT
    // combines the choices to `r mod m`, `pick_in_span` with both ends `None` returns a
    // member of that class, and every point returned is checked by `holds_modular_point`, so
    // the choice can only lose a witness (which this function does not claim to find), never
    // give a wrong one.
    let anchored = |pick: &dyn Fn(&Int, &ResidueSet) -> Option<Int>| -> Option<Int> {
        let mut choices = Vec::with_capacity(2 * pairs.len());
        for (a, sa, b, sb) in &pairs {
            choices.push((pick(a, sa)?.mod_floor(a), (*a).clone()));
            choices.push((pick(b, sb)?.mod_floor(b), (*b).clone()));
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
                if u.mod_floor(&lw.m) <= lw.w {
                    let q = u.div_floor(&lw.m);
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
            let q = (&sx + &gq.c_lo).div_floor(&gq.m);
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
        let (root, s, d) = self.uf.tree_get(a);
        let v = self.root(&root);
        if s > 0 { &v + &d } else { &d - &v }
    }

    fn holds(&self, f: &Formula) -> bool {
        // Complexity tradeoff: reconstructing k quotients of a B-bit point
        // writes O(k B) temporary bits even for a Boolean answer. Batch the
        // remainders in a product/remainder tree, then cancel quotient terms
        // algebraically when their coefficients are multiples of the divisor.
        // The tree costs O(M(B + S) log k) bit operations for S modulus bits;
        // unmatched constraints use LCA cancellation via `rewrite_lin_full`
        // before evaluating root values when all special roots are UF tree roots
        // (avoiding crossing wide UF edges on cancelling aliases), with direct
        // evaluation as the final fallback and no verdict lost.
        // Tests: pncx_pairs_scale, pncx_wide_affine_alias_scale, enumeration suites.
        let specs = self.quotient_specs();
        let empty_rems: HashMap<Atom, FullRemDef> = HashMap::new();
        let roots_clean = self.uf.tree_root(self.x_root) == *self.x_root
            && self
                .rem_defs
                .keys()
                .chain(self.global_quots.keys())
                .chain(self.local_windows.keys())
                .chain(self.fixed.keys())
                .all(|a| self.uf.tree_root(a) == *a);
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
                    let v = if roots_clean {
                        let lin = rewrite_lin_full(&c.lin, self.fixed, self.uf, &empty_rems);
                        lin.terms
                            .iter()
                            .fold(lin.constant, |v, (a, k)| &v + &(k * &self.root(a)))
                    } else {
                        c.lin
                            .terms
                            .iter()
                            .fold(c.lin.constant.clone(), |v, (a, k)| {
                                &v + &(k * &self.atom(a))
                            })
                    };
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
            if self.fixed.contains_key(a) || self.uf.tree_root(a) != *a {
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
            let r = (&sx + &q.c_lo).mod_floor(&q.m);
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
                let r = (&sx + &q.c_lo).mod_floor(&q.m);
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
            if !k.mod_floor(&divisor).is_zero() {
                return None;
            }
            let t = k.div_floor(&divisor);
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
    // The kernel's remainder tree on `|x|` (moduli at least 1, so `uint_leaves` gives them
    // unchanged), then `-|x| mod m` is `m - (|x| mod m)` when that is not 0. O(M(N) log k).
    let leaves = uint_leaves(moduli);
    let rems = trees::remainders(&x.magnitude(), &leaves, &trees::product_tree(&leaves));
    (rems.into_iter().zip(&leaves))
        .map(|(r, m)| match x.is_negative() && !r.is_zero() {
            true => from_uint(m - r),
            false => from_uint(r),
        })
        .collect()
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
    let a = a.mod_floor(m);
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
    let r = lo.mod_floor(m);
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
    let r = hi.mod_floor(m);
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

#[cfg(test)]
mod complement_tests {
    use super::*;

    /// An interval inside an earlier one (DRY-sorted-structures, D2): without the greatest end
    /// kept, `(2, 3)` brought the next gap's start back to 4 and gave `[(4, 9)]`.
    #[test]
    fn the_complement_of_nested_intervals() {
        let i = |l: i64, h: i64| (Int::from(l), Int::from(h));
        let s = [i(0, 5), i(2, 3)];
        assert_eq!(res_complement(&s, &Int::from(10)), [i(6, 9)]);
        assert_eq!(
            res_complement(&[i(1, 2), i(4, 4)], &Int::from(6)),
            [i(0, 0), i(3, 3), i(5, 5)]
        );
        assert_eq!(res_complement(&[], &Int::from(3)), [i(0, 2)]);
    }
}
