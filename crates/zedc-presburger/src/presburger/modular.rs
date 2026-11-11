//! One-variable modular Presburger formulas decided by regime decomposition, Chinese Remainder
//! Theorem reduction, short-period hole cutting, and forbidden-box share analysis.
//!
//! After eliminating top-level constant equalities, two-term unit equalities (`x_i = ±x + d_i`),
//! and three-term Euclidean division remainder equalities (`r = ±x + c - m * q`), a formula over
//! a single primary integer variable `x` and its Euclidean or existential congruence quotients
//! reduces to a boolean combination of interval bounds on `x` and residue constraints
//! `x mod m in S`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use zedc_int::int::Int;

use super::bezout;
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
        for (l, h) in &self.pieces {
            let le_lo = match (l, lo) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(a), Some(b)) => a <= b,
            };
            let ge_hi = match (h, hi) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(a), Some(b)) => a >= b,
            };
            if le_lo && ge_hi {
                return true;
            }
        }
        false
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
                if !rel_d.mod_floor(&two).is_zero() {
                    return Err(());
                }
                return Ok(Some((ra, rel_d.div_floor(&two))));
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
pub fn solve_modular(f: &Formula, want_model: bool) -> Option<Option<Model>> {
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
            Formula::Or(_) | Formula::Not(_) => top_clauses.push(g),
        }
    }

    // Check all constraints in the DAG for products, at least one non-unit coefficient, and collect all atoms.
    let all_cons = f.cons();
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

    // Step 1: Constant equalities propagation (`k * a + c == 0`) and Unit equalities (`a = ±b + d`).
    let mut fixed: HashMap<Atom, Int> = HashMap::new();
    let mut uf = UnitUf::new();
    for a in &all_atoms {
        uf.ensure(a);
    }

    loop {
        let mut progress = false;
        for c in &top_cons {
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
                let (a, k) = lin.terms.iter().next().expect("one term");
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
                    fixed.insert(a.clone(), val);
                    progress = true;
                }
            } else if c.rel == Rel::Eq && lin.terms.len() == 2 {
                let mut it = lin.terms.iter();
                let (a, ka) = it.next().expect("first");
                let (b, kb) = it.next().expect("second");
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
                    match uf.union(a, b, s, &d) {
                        Err(()) => return Some(None),
                        Ok(Some((root, val))) => {
                            if let Some(old) = fixed.get(&root) {
                                if *old != val {
                                    return Some(None);
                                }
                            } else {
                                fixed.insert(root, val);
                                progress = true;
                            }
                        }
                        Ok(None) => {
                            if uf.find(a).0 != a.clone() || uf.find(b).0 != b.clone() {
                                // Check if they were already in the same component before.
                            }
                        }
                    }
                }
            }
        }
        if !progress {
            break;
        }
    }

    // Step 2: Identify 1-term bounds on root atoms to help recognize 3-term division remainders
    // (`x_root + c - m * q_root - r_root == 0` with `0 <= r <= m - 1`).
    let empty_rems: HashMap<Atom, FullRemDef> = HashMap::new();
    let mut root_bounds: HashMap<Atom, (Option<Int>, Option<Int>)> = HashMap::new();
    for c in &top_cons {
        let lin = rewrite_lin_full(&c.lin, &fixed, &uf, &empty_rems);
        if lin.terms.len() == 1 {
            let (a, k) = lin.terms.iter().next().expect("one");
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
        // Check which of `units[0]` or `units[1]` is bounded to width < m (`r_root`).
        let is_rem = |a: &Atom| -> bool {
            if let Some((Some(lo), Some(hi))) = root_bounds.get(a) {
                lo <= hi && &(hi - lo) < &m
            } else {
                false
            }
        };
        let ((r_root, c_r), (x_root, c_x)) = match (is_rem(units[0].0), is_rem(units[1].0)) {
            (true, false) => (units[0], units[1]),
            (false, true) => (units[1], units[0]),
            (true, true) => {
                // Prefer the one with larger unit-class size or smaller Atom as x_root.
                if units[0].0 > units[1].0 {
                    (units[0], units[1])
                } else {
                    (units[1], units[0])
                }
            }
            (false, false) => continue,
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
            let (a1, k1) = it.next().expect("1");
            let (a2, k2) = it.next().expect("2");
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
        let Some(c_x) = lin.terms.get(&x_root) else {
            return None;
        };
        if !c_x.is_unit() {
            return None;
        }
        let (q_root, c_q) = lin
            .terms
            .iter()
            .find(|(a, _)| *a != &x_root)
            .expect("other term");
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
            let a = lin.terms.keys().next().expect("one");
            if *a != x_root && !global_quots.contains_key(a) {
                return None;
            }
        }
    }

    // Step 6: Fold the formula DAG bottom-up with polarity `negated: bool`.
    let mut local_windows: HashMap<Atom, Vec<LocalWindow>> = HashMap::new();
    let folded: Result<FoldNode, ()> = f.fold(
        false,
        |g, negated| negated != matches!(g, Formula::Not(_)),
        |g, negated, parts: Vec<Result<FoldNode, ()>>| match g {
            Formula::Not(_) => parts.into_iter().next().expect("one child"),
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
    let mut unit_mods: BTreeMap<Int, ResidueSet> = BTreeMap::new();
    for gq in global_quots.values() {
        if gq.w < &gq.m - &Int::ONE {
            let s = shift_residue_interval(&Int::ZERO, &gq.w, gq.s_x, &gq.c_lo, &gq.m);
            let e = unit_mods
                .entry(gq.m.clone())
                .or_insert_with(|| vec![(Int::ZERO, &gq.m - &Int::ONE)]);
            *e = res_intersect(e, &s);
            if e.is_empty() {
                return Some(None);
            }
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
            let (m, s) = cl.mods.into_iter().next().expect("one");
            let e = unit_mods
                .entry(m.clone())
                .or_insert_with(|| vec![(Int::ZERO, &m - &Int::ONE)]);
            *e = res_intersect(e, &s);
            if e.is_empty() {
                return Some(None);
            }
        } else {
            raw_clauses.push(cl);
        }
    }

    // Step 8: Merge clauses sharing the same modular part `D` via `(D || B1) && (D || B2) <=> D || (B1 && B2)`.
    let mut by_mods: BTreeMap<BTreeMap<Int, ResidueSet>, Domain> = BTreeMap::new();
    for mut cl in raw_clauses {
        // Restrict `cl.bounds` to `global_bounds`; if it covers all of `global_bounds`, `cl` is true.
        let b_in_global = cl.bounds.intersect(&global_bounds);
        if b_in_global == global_bounds {
            continue;
        }
        cl.bounds = b_in_global;
        let entry = by_mods
            .entry(cl.mods)
            .or_insert_with(|| global_bounds.clone());
        *entry = entry.intersect(&cl.bounds);
    }

    let mut mixed_clauses: Vec<FlatClause> = Vec::new();
    for (mods, bounds) in by_mods {
        if bounds.is_empty() {
            if mods.len() == 1 {
                let (m, s) = mods.into_iter().next().expect("one");
                let e = unit_mods
                    .entry(m.clone())
                    .or_insert_with(|| vec![(Int::ZERO, &m - &Int::ONE)]);
                *e = res_intersect(e, &s);
                if e.is_empty() {
                    return Some(None);
                }
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

    // Step 9: Partition `global_bounds` at all bound endpoints of `mixed_clauses` into
    // bound-homogeneous regimes `[lo_r, hi_r]`.
    let regimes = partition_into_regimes(&global_bounds, &mixed_clauses);
    if regimes.is_empty() {
        return Some(None);
    }

    let walked = walk_segments(&regimes, &global_bounds, &unit_mods, &mixed_clauses);
    let undecided = match walked {
        RegimeOut::Found(x_val) => {
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
            if !f.holds(&model) {
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
    // The tree: node `k` covers `[lo, hi)`, children `2k + 1` and `2k + 2`.
    let mut lists: Vec<Vec<usize>> = vec![Vec::new(); 4 * r];
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
            let mut stack = vec![(0usize, 0usize, r)];
            while let Some((k, lo, hi)) = stack.pop() {
                if b <= lo || hi <= a {
                    continue;
                }
                if a <= lo && hi <= b {
                    lists[k].push(ci);
                    continue;
                }
                let mid = (lo + hi) / 2;
                stack.push((2 * k + 1, lo, mid));
                stack.push((2 * k + 2, mid, hi));
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
        Enter(usize, usize, usize),
        Exit,
    }
    let mut path: Vec<usize> = Vec::new();
    let mut todo = vec![Step::Enter(0, 0, r)];
    let mut undecided = false;
    while let Some(step) = todo.pop() {
        let (k, lo, hi) = match step {
            Step::Exit => {
                path.pop();
                continue;
            }
            Step::Enter(k, lo, hi) => (k, lo, hi),
        };
        path.push(k);
        // The clauses on the path, as the regime loop built them for one segment.
        let mut units = unit_mods.clone();
        let mut multi: Vec<BTreeMap<Int, ResidueSet>> = Vec::new();
        let mut empty = false;
        'path: for &n in &path {
            for &ci in &lists[n] {
                let cl = &clauses[ci];
                if cl.mods.len() == 1 {
                    let (m, s) = cl.mods.iter().next().expect("one");
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
        let out = if empty {
            RegimeOut::Empty
        } else {
            solve_regime(&segs[lo].0, &segs[hi - 1].1, units, multi)
        };
        let leaf = hi - lo == 1;
        match out {
            RegimeOut::Empty => {
                path.pop();
                continue;
            }
            // A point of a leaf satisfies all that applies on its segment.
            RegimeOut::Found(x) if leaf || holds_everywhere(&x) => return RegimeOut::Found(x),
            RegimeOut::Undecided if leaf => {
                undecided = true;
                path.pop();
                continue;
            }
            // A point found at an inner node that is not a witness, or an inner node left
            // undecided: its children are solved.
            _ => {}
        }
        let mid = (lo + hi) / 2;
        todo.push(Step::Exit);
        todo.push(Step::Enter(2 * k + 2, mid, hi));
        todo.push(Step::Enter(2 * k + 1, lo, mid));
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
        let (a, k) = lin.terms.iter().next().expect("one");
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
        let (q_root, c_q) = lin.terms.iter().find(|(a, _)| *a != x_root).expect("other");
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
    let mut pure_bounds = Domain::all();
    let mut has_pure_bounds = false;
    let mut pure_mods: BTreeMap<Int, ResidueSet> = BTreeMap::new();
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
            pure_bounds = pure_bounds.intersect(&cl.bounds);
            has_pure_bounds = true;
            if pure_bounds.is_empty() {
                return Ok(FoldNode {
                    clauses: vec![FlatClause::falsum()],
                    half_wins: Vec::new(),
                    local_quots,
                });
            }
        } else if cl.bounds.is_empty() && cl.mods.len() == 1 {
            let (m, s) = cl.mods.into_iter().next().expect("one");
            let e = pure_mods
                .entry(m.clone())
                .or_insert_with(|| vec![(Int::ZERO, &m - &Int::ONE)]);
            *e = res_intersect(e, &s);
            if e.is_empty() {
                return Ok(FoldNode {
                    clauses: vec![FlatClause::falsum()],
                    half_wins: Vec::new(),
                    local_quots,
                });
            }
        } else {
            other_clauses.push(cl);
        }
    }

    let mut out_clauses = Vec::with_capacity(other_clauses.len() + pure_mods.len() + 1);
    if has_pure_bounds && !pure_bounds.is_all() {
        out_clauses.push(FlatClause {
            bounds: pure_bounds,
            mods: BTreeMap::new(),
        });
    }
    for (m, s) in pure_mods {
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
            let c = node.clauses.into_iter().next().expect("one");
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
    for (g_lo, g_hi) in &global_bounds.pieces {
        let mut cur_lo = g_lo.clone();
        for c in &cuts {
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
fn solve_regime(
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
            if cl.len() == 1 {
                let (i, s_i) = cl.into_iter().next().expect("one");
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
            let mut next_dist = Vec::with_capacity(dist.len() * lit_cnf.len());
            for c1 in &dist {
                for c2 in &lit_cnf {
                    let mut merged = c1.clone();
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
                let (i, s_i) = c.into_iter().next().expect("one");
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

/// Projects a residue set `s` modulo `q` onto `z in [0, q / stride - 1]` under `r = u + stride * z`.
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
    let first = &allowed_i[0].0;
    let last = &allowed_i.last().expect("non-empty").1;
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
                let (m, s) = cl.mods.iter().next().expect("one");
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

/// The product tree of `leaves` (nonempty), leaves first: each level holds the products of
/// adjacent pairs of the level below. O(M(N) log k) for `k` leaves of `N` bits in all.
fn product_tree(leaves: Vec<Int>) -> Vec<Vec<Int>> {
    let mut tree: Vec<Vec<Int>> = vec![leaves];
    while tree.last().expect("nonempty").len() > 1 {
        let next: Vec<Int> = tree
            .last()
            .expect("nonempty")
            .chunks(2)
            .map(|c| if c.len() == 2 { &c[0] * &c[1] } else { c[0].clone() })
            .collect();
        tree.push(next);
    }
    tree
}

/// `(P / m) mod m` for each leaf `m` of `tree`, where `P` is the root: the remainder tree takes
/// `P mod v^2` from each node `v` to its children (`v^2` divides the parent's square), and
/// `(P mod m^2) / m` is `(P / m) mod m`. O(M(N) log k).
fn cofactors_mod_leaves(tree: &[Vec<Int>]) -> Vec<Int> {
    let mut rems: Vec<Int> = tree.last().expect("nonempty").clone();
    for level in (0..tree.len() - 1).rev() {
        rems = tree[level]
            .iter()
            .enumerate()
            .map(|(j, v)| rems[j / 2].mod_floor(&(v * v)))
            .collect();
    }
    rems.iter()
        .zip(&tree[0])
        .map(|(r, m)| r.div_floor(m))
        .collect()
}

/// Each modulus with its factors `(b, b^e)` over one set of pairwise coprime bases `b`.
type ModBase = BTreeMap<Int, Vec<(Int, Int)>>;

/// Factors every modulus in `moduli` over a pairwise coprime base. A modulus coprime to all the
/// others is its own base; these are found together by one product tree and one remainder tree
/// (`P mod m^2` for the product `P` of all moduli gives `gcd(m, P / m)`), in O(M(N) log k) for
/// `k` moduli of `N` bits in all, where `M` is the cost of multiplying numbers of `N` bits.
///
/// Complexity tradeoff: the moduli that share a factor with another one go to `coprime_base`,
/// which is pairwise, O(r^2) GCDs and O(r b) divisions for `r` such moduli and `b` bases.
/// Bernstein's algorithm ("Factoring into coprimes in essentially linear time", J. Algorithms
/// 54 (2005)) gives the same base in O(N (log N)^O(1)) and is not implemented. What is given up:
/// time only, when many moduli share factors (for example `2 p_i` for `k` primes `p_i`); the
/// answers are the same. Moduli that are pairwise coprime, the common case, cost O(M(N) log k).
/// Test: `one_scope::the_coprime_base_of_distinct_primes_scales`.
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
    let cof = cofactors_mod_leaves(&product_tree(ms.clone()));
    let mut rest: Vec<Int> = Vec::new();
    for (m, c) in ms.iter().zip(&cof) {
        if m.gcd(c) == Int::ONE {
            out.insert(m.clone(), vec![(m.clone(), m.clone())]);
        } else {
            rest.push(m.clone());
        }
    }
    let bases = coprime_base(rest.clone());
    for m in rest {
        let mut rem = m.clone();
        let mut facs = Vec::new();
        for b in &bases {
            if rem.mod_floor(b).is_zero() {
                let mut q = b.clone();
                rem = rem.div_floor(b);
                while rem.mod_floor(b).is_zero() {
                    q = &q * b;
                    rem = rem.div_floor(b);
                }
                facs.push((b.clone(), q));
            }
        }
        out.insert(m, facs);
    }
    out
}

/// Computes a pairwise coprime base from `moduli` by repeated GCD refinement:
/// whenever `g = gcd(a, b) > 1`, replace `(a, b)` with `(a/g, g, b/g)`.
fn coprime_base(moduli: Vec<Int>) -> Vec<Int> {
    let mut basis: Vec<Int> = Vec::new();
    let mut queue: VecDeque<Int> = moduli.into_iter().filter(|m| *m > Int::ONE).collect();
    while let Some(mut x) = queue.pop_front() {
        if x <= Int::ONE {
            continue;
        }
        let mut i = 0;
        while i < basis.len() && x > Int::ONE {
            let b = &basis[i];
            if *b == x {
                x = Int::ONE;
                break;
            }
            let g = b.gcd(&x);
            if g > Int::ONE {
                let b_rem = b.div_floor(&g);
                let x_rem = x.div_floor(&g);
                basis.swap_remove(i);
                queue.push_back(g);
                if b_rem > Int::ONE {
                    queue.push_back(b_rem);
                }
                x = x_rem;
            } else {
                i += 1;
            }
        }
        if x > Int::ONE {
            basis.push(x);
        }
    }
    basis.sort();
    basis.dedup();
    basis
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

    // Pass 1: Propagate single-residue constraints downward from higher powers `q_hi` to lower
    // powers `q_lo`.
    for hi_idx in (0..work.len()).rev() {
        if work[hi_idx].1.len() == 1 && work[hi_idx].1[0].0 == work[hi_idx].1[0].1 {
            let r_hi = work[hi_idx].1[0].0.clone();
            for lo_idx in 0..hi_idx {
                let rq = r_hi.mod_floor(&work[lo_idx].0);
                work[lo_idx].1 = res_intersect(&work[lo_idx].1, &[(rq.clone(), rq)]);
                if work[lo_idx].1.is_empty() {
                    return ConsolidateOut::Empty;
                }
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
/// `allowed[0..t]` (in `z_i in [0, bases_info[i].z_max_q - 1]`) and clauses `clauses` on `[lo, hi]`.
fn solve_coprime_system(
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
                    let (i, s_i) = cl.into_iter().next().expect("one");
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
        // `(bases_info[i].u, bases_info[i].stride)` via CRT (`bezout` balanced tree).
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
                let (g, inv_m0, _) = bezout(&m0_z, z_q);
                if g == Int::ONE {
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
                    let first_y = y_dom.pieces[0].0.as_ref().expect("finite ly");
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
            let g = num.gcd(&den);
            let sh = (num.div_floor(&g), den.div_floor(&g));
            total_share = rat_add(&total_share, &sh);
            shares.push(sh);
        }

        // Check if `total_share < 1`:
        if total_share.0 < total_share.1 {
            if let Some(x_val) = find_point_by_conditional_expectations(
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
            ) {
                return RegimeOut::Found(x_val);
            }
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
        if cl.len() == 2 {
            let mut it = cl.into_iter();
            let (i1, s1) = it.next().expect("1");
            let (i2, s2) = it.next().expect("2");
            let e = by_first
                .entry((i1, i2, s1))
                .or_insert_with(|| allowed[i2].clone());
            *e = res_intersect(e, &s2);
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
            let z_i = chosen[i].as_ref().expect("chosen");
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
                let z_i = chosen[i].as_ref().expect("chosen");
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
        let (g, inv_m, _) = bezout(&m_cur_z, z_q);
        if g != Int::ONE {
            continue;
        }
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
    let (g, u, _) = bezout(m1, m2);
    let diff = r2 - r1;
    if !diff.mod_floor(&g).is_zero() {
        return None;
    }
    let m2_g = m2.div_floor(&g);
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
/// bits, plus one inverse modulo each `m_i`.
///
/// Complexity tradeoff: when one modulus is not coprime to the product of the others, the pairs
/// are combined two at a time up a tree, each by the Euclidean `bezout` on the merged moduli,
/// O(N^2) bit operations at the top. What is given up: time only, on moduli that share
/// factors; the answer is the same. Test: `one_scope::the_coprime_base_of_distinct_primes_scales`.
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
        let (g, inv, _) = bezout(e, m);
        if g != Int::ONE {
            vals = None;
            break;
        }
        if let Some(v) = vals.as_mut() {
            v.push((&r.mod_floor(m) * &inv).mod_floor(m));
        }
    }
    if let Some(mut vals) = vals {
        for level in 0..tree.len() - 1 {
            let prods = &tree[level];
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
        let big_m = tree.last().expect("nonempty")[0].clone();
        return Some((vals[0].mod_floor(&big_m), big_m));
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
    let mut choices = Vec::with_capacity(2 * groups.len());
    for ((a, b), cs) in groups {
        if cs.len() != 2 || !used.insert(a) || !used.insert(b) {
            return None;
        }
        choices.push((cs[0][a].first()?.0.clone(), a.clone()));
        choices.push((cs[1][b].first()?.0.clone(), b.clone()));
    }
    let (r, m) = combine_crt_tree(choices)?;
    let x = pick_in_span(lo, hi, &r, &m)?;
    holds_modular_point(&x, unit_mods, clauses).then_some(x)
}
