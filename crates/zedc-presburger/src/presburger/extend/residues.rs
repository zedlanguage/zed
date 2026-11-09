//! The intervals and residues left to the atoms of a formula read with holes (LOAD-holes-mod):
//! a face whose holes leave gaps that its tests of one modulus exclude, as in the chain whose
//! call moves `q(x) = (x < 10 || x > 20) && x mod 4 != 1` by 3, holds nowhere, and that is
//! seen from the holes, the bounds and the residues alone, without the solver, which is
//! refused (`Shadows`) on such a face with its holes written as clauses.
//!
//! Each rule below reads a subset of the conjuncts and takes each quotient as free, so the set
//! of points it describes contains every point of the formula: where it is empty, so is the
//! formula. The atoms that two-term unit equalities link are read as one class, each atom
//! `s * r + d` of the class's least atom `r` ([`unit_classes`]); for each class:
//!
//! - one-term rows bound `r`, and one whose equality has no integer solution empties it;
//! - one-term clauses that say an atom lies outside an interval (`x < 10 || x > 20`, [`hole_of`]),
//!   one-term negated equalities (`!(r == 1)`), and the holes given are holes of `r`;
//! - a clause each of whose disjuncts bounds `a - m * q` for one atom `a`, one modulus `|m|`
//!   and some quotient `q` (`x mod 4 == 1 || x mod 4 == 3`, as the faces write it) keeps `a`
//!   in the residues modulo `|m|` of the intervals its disjuncts leave; a two-term row is such
//!   a clause with one disjunct;
//! - an equality `v == m * w + u + c` (a division, `u` its remainder; the signs of `u` and `v`
//!   free) keeps `v` in the residues modulo `|m|` of the values the class of `u` has left when
//!   they are bounded: `x mod 4 != 1` is `x == 4 * q + r`, `0 <= r <= 3`, `!(r == 1)`.
//!
//! The residues kept by each modulus are intersected, each modulus apart. The class holds
//! nowhere when its bounds cross, a modulus keeps no residue, or no interval between its holes
//! meets the residues each modulus keeps: an interval at least as long as the modulus meets
//! every residue, and a shorter one is a cyclic range of residues, met or not by a binary
//! search. Two moduli are never combined, so a class emptied only by both (`x mod 2 == 1 &&
//! x mod 3 == 1` between holes leaving `3..=4`) is left to the solver.
//!
//! Time: the conjuncts, near linear ([`unit_classes`]); each holes given merged into its
//! class's, the smaller into the larger; each clause's ranges sorted; and the intervals
//! between each class's holes walked once, and once for each division whose remainder the
//! class holds.

use std::borrow::Borrow;
use std::collections::{BTreeMap, HashMap, HashSet};

use super::holes::{Holes, hole_of};
use super::{Atom, Con, Formula, Id, Lin, Rel};
use zedc_int::int::Int;

/// What the intervals and residues left say of a formula read with holes.
pub(super) enum Reading {
    /// The formula holds nowhere with the holes.
    Empty,
    /// For each class of atoms holes are given over, its root bounded to the first interval
    /// between its holes that meets the residues left to it: bounds that, with the formula's
    /// equalities, keep every atom outside the holes given. A point of the formula with these
    /// bounds is a point of the formula with the holes; none may exist there although one
    /// exists in a later interval.
    Within(Vec<Formula>),
}

/// An interval that may be unbounded at either end.
type Span = (Option<Int>, Option<Int>);

/// One class of atoms, over its root.
struct Line {
    lo: Option<Int>,
    hi: Option<Int>,
    holes: Holes,
    /// Whether holes were given over an atom of the class, so that the class is bounded to an
    /// interval between them for the solver.
    given: bool,
    /// For each modulus, the residues of the root excluded, as intervals of `0..modulus`.
    out: BTreeMap<Int, Vec<(Int, Int)>>,
}

impl Line {
    fn new() -> Line {
        Line {
            lo: None,
            hi: None,
            holes: Holes::new(),
            given: false,
            out: BTreeMap::new(),
        }
    }

    /// The root bounded by `k * r + e >= 0` or `== 0`: `false` where that has no integer
    /// solution.
    fn bound(&mut self, rel: Rel, k: &Int, e: &Int) -> bool {
        let (lo, hi) = match rel {
            Rel::Ge if k.is_positive() => (Some(-&e.div_floor(k)), None),
            Rel::Ge => (None, Some(e.div_floor(&-k))),
            Rel::Eq => {
                if !e.mod_floor(k).is_zero() {
                    return false;
                }
                let v = (-e).div_floor(k);
                (Some(v.clone()), Some(v))
            }
        };
        if let Some(l) = lo {
            self.lo = Some(self.lo.take().map_or(l.clone(), |o| o.max(l)));
        }
        if let Some(h) = hi {
            self.hi = Some(self.hi.take().map_or(h.clone(), |o| o.min(h)));
        }
        true
    }

    /// The intervals of `lo..=hi` outside the holes, in increasing order. Time of the holes.
    fn gaps(&self) -> Vec<Span> {
        let mut out: Vec<Span> = Vec::new();
        let mut from = self.lo.clone();
        for (a, b) in self.holes.intervals() {
            if self.hi.as_ref().is_some_and(|h| &a > h) {
                break;
            }
            if from.as_ref().is_some_and(|f| &b < f) {
                continue;
            }
            let to = &a - &Int::ONE;
            if from.as_ref().is_none_or(|f| *f <= to) {
                out.push((from, Some(to)));
            }
            from = Some(&b + &Int::ONE);
        }
        if let (Some(f), Some(h)) = (&from, &self.hi)
            && f > h
        {
            return out;
        }
        out.push((from, self.hi.clone()));
        out
    }
}

/// An atom, a modulus and intervals of the atom read modulo it.
type Kept<A> = (A, Int, Vec<(Int, Int)>);

/// The key of a clause of residues: its atom, its modulus and the residues it keeps
/// ([`key`]).
pub(super) type Key = Kept<Atom>;

/// The classes of the atoms, each with what the rules read of it.
struct Lines {
    /// Each atom outside its class's root, as `s * root + d`.
    to: HashMap<Atom, Lin>,
    by: BTreeMap<Atom, Line>,
}

impl Lines {
    /// The root of `a`'s class, and `s` and `d` with `a == s * root + d`, `s` 1 or -1.
    fn on(&self, a: &Atom) -> (Atom, Int, Int) {
        match self.to.get(a) {
            Some(l) => {
                let (r, s) = l.terms.iter().next().expect("a class's root");
                (r.clone(), s.clone(), l.constant.clone())
            }
            None => (a.clone(), Int::ONE, Int::ZERO),
        }
    }

    fn line(&mut self, r: Atom) -> &mut Line {
        self.by.entry(r).or_insert_with(Line::new)
    }

    /// The hole `lo..=hi` of `a`, added to its class's.
    fn cut(&mut self, a: &Atom, lo: &Int, hi: &Int) {
        let (r, s, d) = self.on(a);
        let (lo, hi) = back(&s, &d, lo, hi);
        self.line(r).holes.cut(&lo, &hi);
    }

    /// `a` kept in the residues modulo `m` of the intervals `ys`, each shorter than `m`.
    fn keep(&mut self, a: &Atom, m: &Int, ys: Vec<(Int, Int)>) {
        let (r, s, d) = self.on(a);
        let ys = ys.into_iter().map(|(lo, hi)| back(&s, &d, &lo, &hi));
        let out = complement(&modulo(ys, m), m);
        self.line(r).out.entry(m.clone()).or_default().extend(out);
    }

    /// The values the atom `u` has left, as intervals of at most `m - 1` values, where its
    /// class is bounded and each interval between its holes is shorter than `m`: `None`
    /// otherwise, when they would meet every residue modulo `m` or are not bounded.
    fn values(&self, u: &Atom, m: &Int) -> Option<Vec<(Int, Int)>> {
        let (r, s, d) = self.on(u);
        let line = self.by.get(&r)?;
        let mut out: Vec<(Int, Int)> = Vec::new();
        for (a, b) in line.gaps() {
            let (a, b) = (a?, b?);
            if &(&b - &a) + &Int::ONE >= *m {
                return None;
            }
            let (x, y) = (&(&s * &a) + &d, &(&s * &b) + &d);
            out.push(match x <= y {
                true => (x, y),
                false => (y, x),
            });
        }
        Some(out)
    }
}

/// The residues modulo `m` of the intervals `ys`, each shorter than `m`, as sorted intervals
/// of `0..m`, which may overlap.
fn modulo(ys: impl Iterator<Item = (Int, Int)>, m: &Int) -> Vec<(Int, Int)> {
    let mut out: Vec<(Int, Int)> = Vec::new();
    for (lo, hi) in ys {
        let start = lo.mod_floor(m);
        let end = &start + &(&hi - &lo);
        match end < *m {
            true => out.push((start, end)),
            false => {
                out.push((start, m - &Int::ONE));
                out.push((Int::ZERO, &end - m));
            }
        }
    }
    out.sort();
    out
}

/// The values `r` with `s * r + d` in `lo..=hi`, `s` 1 or -1.
fn back(s: &Int, d: &Int, lo: &Int, hi: &Int) -> (Int, Int) {
    match s.is_positive() {
        true => (lo - d, hi - d),
        false => (d - hi, d - lo),
    }
}

/// The residues of `0..m` outside the sorted intervals `rs`, as sorted disjoint intervals.
fn complement(rs: &[(Int, Int)], m: &Int) -> Vec<(Int, Int)> {
    let mut out: Vec<(Int, Int)> = Vec::new();
    let mut next = Int::ZERO;
    for (lo, hi) in rs {
        if *lo > next {
            out.push((next.clone(), lo - &Int::ONE));
        }
        next = next.max(hi + &Int::ONE);
    }
    if next < *m {
        out.push((next, m - &Int::ONE));
    }
    out
}

/// Whether the interval `g` holds a value whose residue modulo `m` is in `left`, sorted
/// disjoint intervals of `0..m`. O(log of `left`).
fn meets(g: &Span, m: &Int, left: &[(Int, Int)]) -> bool {
    let (Some(a), Some(b)) = g else {
        return !left.is_empty();
    };
    if &(b - a) + &Int::ONE >= *m {
        return !left.is_empty();
    }
    let hit = |lo: &Int, hi: &Int| {
        let i = left.partition_point(|(_, h)| h < lo);
        i < left.len() && left[i].0 <= *hi
    };
    let start = a.mod_floor(m);
    let end = &start + &(b - a);
    match end < *m {
        true => hit(&start, &end),
        false => hit(&start, &(m - &Int::ONE)) || hit(&Int::ZERO, &(&end - m)),
    }
}

/// The disjuncts of a clause as constraints, each a constraint or a conjunction of them:
/// `None` for any other disjunct.
fn disjuncts(f: &Formula) -> Option<Vec<Vec<&Con>>> {
    let Formula::Or(ds) = f else {
        return None;
    };
    (ds.iter())
        .map(|d| match d {
            Formula::Con(c) => Some(vec![c]),
            Formula::And(gs) => (gs.iter())
                .map(|g| match g {
                    Formula::Con(c) => Some(c),
                    _ => None,
                })
                .collect(),
            _ => None,
        })
        .collect()
}

/// The atom `a`, the modulus `|m|` and the intervals left to `a - m * q` by each disjunct of a
/// clause that bounds `a - m * q` alone in each, `q` one atom in each disjunct and `|m|` one in
/// the clause: `None` where the clause is not of that form, or a disjunct leaves an interval
/// unbounded or as long as the modulus, so that every residue is left, or a quotient is not
/// one `free` allows. The intervals of the disjuncts that hold nowhere are left out.
fn residues<'c>(ds: &[Vec<&'c Con>], free: &dyn Fn(&Atom) -> bool) -> Option<Kept<&'c Atom>> {
    let first = ds.first()?.first()?;
    // Either atom of the first constraint may be `a`; the other is its quotient.
    let mut tried = first.lin.terms.keys();
    let (x, y) = (tried.next()?, tried.next()?);
    [x, y]
        .into_iter()
        .find_map(|a| over(ds, a, free).map(|(m, ys)| (a, m, ys)))
}

/// [`residues`] with `a` given.
fn over(
    ds: &[Vec<&Con>],
    a: &Atom,
    free: &dyn Fn(&Atom) -> bool,
) -> Option<(Int, Vec<(Int, Int)>)> {
    let mut modulus: Option<Int> = None;
    let mut ys: Vec<(Int, Int)> = Vec::new();
    for d in ds {
        let mut q: Option<&Atom> = None;
        let (mut lo, mut hi): Span = (None, None);
        let mut nowhere = false;
        for c in d {
            let mut terms = c.lin.terms.iter();
            let (Some(t), Some(u), None) = (terms.next(), terms.next(), terms.next()) else {
                return None;
            };
            let ((_, ka), (b, kb)) = match (t.0 == a, u.0 == a) {
                (true, _) => (t, u),
                (_, true) => (u, t),
                _ => return None,
            };
            if q.is_some_and(|q| q != b) || !free(b) || !kb.mod_floor(ka).is_zero() {
                return None;
            }
            q = Some(b);
            let m = kb.div_floor(ka).abs();
            if modulus.as_ref().is_some_and(|o| *o != m) {
                return None;
            }
            modulus = Some(m);
            // `ka * (a + (kb / ka) * q) + c0`, compared with zero.
            let c0 = &c.lin.constant;
            match c.rel {
                Rel::Ge if ka.is_positive() => {
                    let l = -&c0.div_floor(ka);
                    lo = Some(lo.map_or(l.clone(), |o| o.max(l)));
                }
                Rel::Ge => {
                    let h = c0.div_floor(&-ka);
                    hi = Some(hi.map_or(h.clone(), |o| o.min(h)));
                }
                Rel::Eq if !c0.mod_floor(ka).is_zero() => nowhere = true,
                Rel::Eq => {
                    let v = (-c0).div_floor(ka);
                    lo = Some(lo.map_or(v.clone(), |o| o.max(v.clone())));
                    hi = Some(hi.map_or(v.clone(), |o| o.min(v)));
                }
            }
        }
        // A disjunct with no constraint holds everywhere.
        q?;
        match (lo, hi) {
            _ if nowhere => {}
            (Some(l), Some(h)) if l > h => {}
            (Some(l), Some(h)) if &h - &l < *modulus.as_ref().expect("a modulus") => {
                ys.push((l, h))
            }
            _ => return None,
        }
    }
    Some((modulus?, ys))
}

/// The atom `a`, the modulus `m` and the residues modulo `m`, sorted disjoint intervals of
/// `0..m`, that the clause `f` keeps `a` in when each quotient it reads is one `free` allows
/// and so stands for any integer: `f` is then exactly `a mod m` in those residues, since the
/// existential of each quotient distributes over the disjuncts, and that of `lo <= a - m * q
/// <= hi` with `hi - lo < m` is `a mod m` in the residues of `lo..=hi`. Two such clauses with
/// one key say the same, though their quotients and windows differ (the windows by a multiple
/// of `m`). `None` where `f` is not of the form [`residues`] reads. Time of `f` and a sort.
pub(super) fn key(f: &Formula, free: &dyn Fn(&Atom) -> bool) -> Option<Key> {
    let ds = disjuncts(f)?;
    let (a, m, ys) = residues(&ds, free)?;
    let left = complement(&complement(&modulo(ys.into_iter(), &m), &m), &m);
    Some((a.clone(), m, left))
}

/// What the intervals and residues left to the atoms of `f` read with `holes` say
/// ([`Reading`]). Time near linear in `f` and the holes, as the module says.
pub(super) fn read(f: &Formula, holes: &[(&Atom, &Holes)]) -> Reading {
    // The conjuncts, nested conjunctions flattened, each shared one read once.
    let mut rows: Vec<&Con> = Vec::new();
    let mut clauses: Vec<&Formula> = Vec::new();
    let mut seen: HashSet<Id> = HashSet::new();
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        match g {
            Formula::And(gs) => {
                if seen.insert(Id::any(g)) {
                    stack.extend(gs.iter().rev());
                }
            }
            Formula::Con(c) => rows.push(c),
            Formula::Or(ds) if ds.is_empty() => return Reading::Empty,
            Formula::Or(_) | Formula::Not(_) => clauses.push(g),
        }
    }
    let none: HashSet<Atom> = HashSet::new();
    let (to, _) = unit_classes(&rows, &none, &none);
    let mut lines = Lines {
        to,
        by: BTreeMap::new(),
    };
    // Bounds and holes.
    for c in &rows {
        let c0 = &c.lin.constant;
        let fails = match c.rel {
            Rel::Ge => c0.is_negative(),
            Rel::Eq => !c0.is_zero(),
        };
        if c.lin.terms.is_empty() && fails {
            return Reading::Empty;
        }
        let mut terms = c.lin.terms.iter();
        let (Some((a, k)), None) = (terms.next(), terms.next()) else {
            continue;
        };
        let (r, s, d) = lines.on(a);
        // `k * (s * r + d) + c0`.
        let (k, e) = (k * &s, &(k * &d) + &c.lin.constant);
        if !lines.line(r).bound(c.rel, &k, &e) {
            return Reading::Empty;
        }
    }
    for g in &clauses {
        match g {
            Formula::Not(h) => {
                let Formula::Con(c) = &**h else { continue };
                let mut terms = c.lin.terms.iter();
                let (Rel::Eq, Some((a, k)), None) = (c.rel, terms.next(), terms.next()) else {
                    continue;
                };
                let c0 = &c.lin.constant;
                if c0.mod_floor(k).is_zero() {
                    let v = (-c0).div_floor(k);
                    lines.cut(a, &v, &v);
                }
            }
            _ => {
                if let Some((a, Some((lo, hi)))) = hole_of(g) {
                    lines.cut(&a, &lo, &hi);
                }
            }
        }
    }
    for (a, h) in holes {
        let (r, s, d) = lines.on(a);
        let line = lines.line(r);
        let mine = std::mem::replace(&mut line.holes, Holes::new());
        line.holes = mine.merged(h.through(&s, &d));
        line.given = true;
    }
    // Residues: of the clauses and two-term rows, then of the divisions.
    let mut kept: Vec<Kept<&Atom>> = Vec::new();
    for g in &clauses {
        if let Some(ds) = disjuncts(g)
            && let Some(r) = residues(&ds, &|_| true)
        {
            kept.push(r);
        }
    }
    for c in &rows {
        if c.lin.terms.len() == 2
            && let Some(r) = residues(&[vec![*c]], &|_| true)
        {
            kept.push(r);
        }
    }
    for c in rows
        .iter()
        .filter(|c| c.rel == Rel::Eq && c.lin.terms.len() == 3)
    {
        let t: Vec<(&Atom, &Int)> = c.lin.terms.iter().collect();
        for (i, j, l) in [
            (0, 1, 2),
            (0, 2, 1),
            (1, 0, 2),
            (1, 2, 0),
            (2, 0, 1),
            (2, 1, 0),
        ] {
            let ((u, cu), (v, cv), (_, cw)) = (t[i], t[j], t[l]);
            let m = cw.abs();
            if !cu.is_unit() || !cv.is_unit() || m <= Int::ONE {
                continue;
            }
            // `cu * u + cv * v + cw * w + c0 == 0`, so `v == al * u + be` modulo `m`.
            let (al, be) = (-&(cv * cu), -&(cv * &c.lin.constant));
            let Some(us) = lines.values(u, &m) else {
                continue;
            };
            let ys = (us.into_iter())
                .map(|(x, y)| {
                    let (x, y) = (&(&al * &x) + &be, &(&al * &y) + &be);
                    match x <= y {
                        true => (x, y),
                        false => (y, x),
                    }
                })
                .collect();
            kept.push((v, m, ys));
        }
    }
    for (a, m, ys) in kept {
        lines.keep(a, &m, ys);
    }
    // Each class: the first interval between its holes that meets the residues left by each
    // modulus.
    let mut within: Vec<Formula> = Vec::new();
    for (r, line) in &mut lines.by {
        let mut left: Vec<(Int, Vec<(Int, Int)>)> = Vec::with_capacity(line.out.len());
        for (m, out) in std::mem::take(&mut line.out) {
            let mut out = out;
            out.sort();
            let l = complement(&out, &m);
            if l.is_empty() {
                return Reading::Empty;
            }
            left.push((m, l));
        }
        let gaps = line.gaps();
        let Some((lo, hi)) = (gaps.iter()).find(|g| left.iter().all(|(m, l)| meets(g, m, l)))
        else {
            return Reading::Empty;
        };
        if line.given {
            let y = Lin::atom(r.clone());
            if let Some(lo) = lo {
                within.push(Formula::Con(Con::ge(&y, &Lin::constant(lo.clone()))));
            }
            if let Some(hi) = hi {
                within.push(Formula::Con(Con::ge(&Lin::constant(hi.clone()), &y)));
            }
        }
    }
    Reading::Within(within)
}

/// What each atom of `read` equals by the two-term equalities among `rows`, for
/// [`split`](super::split): the
/// atoms that equalities `a == b + c` and `a == -b + c` link form classes, each written as
/// `s * r + d` (`s` 1 or -1) of one atom `r` of its class, an atom of `keep` where the class
/// holds one, else the least; an atom of `read` that is the `r` of its class, or in none, and
/// that an equality `k * a + e * b + c == 0` with `k` 1 or -1 sets, equals `-k * (e * b + c)`,
/// `b` written as its class's, by the first such row. So the clauses of a chain whose links
/// bind `x@{i-1} == x@i + 12` read the caller's atom however deep the chain, and not that of
/// the link below (LOAD-bound-holes). Exact, since the rows stay. Time of the rows, near
/// linear: a union of the classes by their atoms, each path compressed on the way.
pub(super) fn unit_classes(
    rows: &[impl Borrow<Con>],
    read: &HashSet<Atom>,
    keep: &HashSet<Atom>,
) -> (HashMap<Atom, Lin>, HashMap<Atom, Lin>) {
    // Each atom's index, and for each index the one it is set by: `(s, up, d)`, the atom
    // equal to `s` times that at `up` plus `d`.
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut atoms: Vec<&Atom> = Vec::new();
    let mut up: Vec<(Int, usize, Int)> = Vec::new();
    type Term<'c> = (&'c Atom, &'c Int);
    fn unit(c: &Con) -> Option<(Term<'_>, Term<'_>)> {
        let mut terms = c.lin.terms.iter();
        match (c.rel, terms.next(), terms.next(), terms.next()) {
            (Rel::Eq, Some(x), Some(y), None) => Some((x, y)),
            _ => None,
        }
    }
    for c in rows.iter().map(Borrow::<Con>::borrow) {
        let Some(((a, _), (b, _))) = unit(c) else {
            continue;
        };
        for x in [a, b] {
            if !index.contains_key(x) {
                index.insert(x, atoms.len());
                up.push((Int::ONE, atoms.len(), Int::ZERO));
                atoms.push(x);
            }
        }
    }
    // The root of `i`, as `(s, r, d)`: the atom at `i` equals `s` times that at `r` plus `d`.
    fn find(up: &mut [(Int, usize, Int)], i: usize) -> (Int, usize, Int) {
        let (mut s, mut r, mut d) = (Int::ONE, i, Int::ZERO);
        let mut path: Vec<usize> = Vec::new();
        while up[r].1 != r {
            path.push(r);
            let (t, n, e) = up[r].clone();
            // x == s·r + d and r == t·n + e, so x == s·t·n + s·e + d.
            d = &(&s * &e) + &d;
            s = &s * &t;
            r = n;
        }
        // Each atom on the path set by the root directly, its value as above.
        let (mut t, mut e) = (Int::ONE, Int::ZERO);
        for &p in path.iter().rev() {
            let (u, _, f) = up[p].clone();
            // p == u·next + f and next == t·root + e.
            e = &(&u * &e) + &f;
            t = &u * &t;
            up[p] = (t.clone(), r, e.clone());
        }
        (s, r, d)
    }
    let prefer = |x: &Atom, y: &Atom| (!keep.contains(x), x) < (!keep.contains(y), y);
    for c in rows.iter().map(Borrow::<Con>::borrow) {
        let Some(((a, k), (b, e))) = unit(c) else {
            continue;
        };
        if k.abs() != Int::ONE || e.abs() != Int::ONE {
            continue;
        }
        // k·a + e·b + c0 == 0, so a == -k·e·b - k·c0.
        let (m, c0) = (-&(k * e), -&(k * &c.lin.constant));
        let (sa, ra, da) = find(&mut up, index[a]);
        let (sb, rb, db) = find(&mut up, index[b]);
        if ra == rb {
            continue;
        }
        // sa·ra + da == m·(sb·rb + db) + c0.
        match prefer(atoms[ra], atoms[rb]) {
            // rb == m·sb·(sa·ra + da - m·db - c0).
            true => {
                let f = &m * &sb;
                let d = &f * &(&(&da - &(&m * &db)) - &c0);
                up[rb] = (&f * &sa, ra, d);
            }
            // ra == sa·(m·sb·rb + m·db + c0 - da).
            false => {
                let d = &sa * &(&(&(&m * &db) + &c0) - &da);
                up[ra] = (&(&sa * &m) * &sb, rb, d);
            }
        }
    }
    let lin = |s: Int, r: usize, d: Int| Lin {
        terms: std::iter::once((atoms[r].clone(), s)).collect(),
        constant: d,
    };
    let mut to: HashMap<Atom, Lin> = HashMap::new();
    for (i, &a) in atoms.iter().enumerate() {
        let (s, r, d) = find(&mut up, i);
        if r != i && !keep.contains(a) {
            to.insert(a.clone(), lin(s, r, d));
        }
    }
    let mut also: HashMap<Atom, Lin> = HashMap::new();
    for c in rows.iter().map(Borrow::<Con>::borrow) {
        let Some(((x, kx), (y, ky))) = unit(c) else {
            continue;
        };
        for ((a, k), (b, e)) in [((x, kx), (y, ky)), ((y, ky), (x, kx))] {
            if k.abs() != Int::ONE
                || !read.contains(a)
                || to.contains_key(a)
                || also.contains_key(a)
            {
                continue;
            }
            let (s, r, d) = find(&mut up, index[b]);
            if r == index[a] {
                continue;
            }
            // k·a + e·(s·r + d) + c0 == 0, so a == -k·e·s·r - k·(e·d + c0).
            let set = Lin {
                terms: std::iter::once((atoms[r].clone(), -&(&(k * e) * &s))).collect(),
                constant: -&(k * &(&(e * &d) + &c.lin.constant)),
            };
            also.insert(a.clone(), set);
        }
    }
    (to, also)
}

#[cfg(test)]
mod tests {
    use super::super::Shared;
    use super::*;

    fn a(n: u32) -> Atom {
        Atom::Aux(n)
    }

    /// `k1 * a1 + k2 * a2 + ... + c` related to 0 by `rel`.
    fn con(terms: &[(u32, i64)], c: i64, rel: Rel) -> Formula {
        Formula::Con(Con {
            lin: Lin {
                terms: (terms.iter()).map(|&(n, k)| (a(n), Int::from(k))).collect(),
                constant: Int::from(c),
            },
            rel,
        })
    }

    fn and(fs: Vec<Formula>) -> Formula {
        Formula::And(Shared::new(fs))
    }

    fn or(fs: Vec<Formula>) -> Formula {
        Formula::Or(Shared::new(fs))
    }

    /// `lo <= a0 <= hi`.
    fn between(lo: i64, hi: i64) -> Vec<Formula> {
        vec![con(&[(0, 1)], -lo, Rel::Ge), con(&[(0, -1)], hi, Rel::Ge)]
    }

    /// `a0 mod m` in `lo..=hi` through the quotient `a{q}`, as a face writes it:
    /// `lo <= a0 - m * a{q} <= hi`.
    fn window(q: u32, m: i64, lo: i64, hi: i64) -> Formula {
        and(vec![
            con(&[(0, 1), (q, -m)], -lo, Rel::Ge),
            con(&[(0, -1), (q, m)], hi, Rel::Ge),
        ])
    }

    fn holes(cuts: &[(i64, i64)]) -> Holes {
        let mut h = Holes::new();
        for &(lo, hi) in cuts {
            h.cut(&Int::from(lo), &Int::from(hi));
        }
        h
    }

    fn is_empty(f: &Formula, given: &[(&Atom, &Holes)]) -> bool {
        matches!(read(f, given), Reading::Empty)
    }

    fn within(f: &Formula, given: &[(&Atom, &Holes)]) -> Vec<Formula> {
        match read(f, given) {
            Reading::Empty => panic!("{f} read empty"),
            Reading::Within(w) => w,
        }
    }

    #[test]
    fn residues_that_no_interval_between_the_holes_meets_are_empty() {
        // 0 <= x <= 6 outside 2..=5 leaves 0, 1 and 6, residues 0, 1 and 2 by 4; `x == 4q + 3`
        // keeps residue 3 alone.
        let mut fs = between(0, 6);
        fs.push(or(vec![
            con(&[(0, -1)], 1, Rel::Ge),
            con(&[(0, 1)], -6, Rel::Ge),
        ]));
        fs.push(con(&[(0, 1), (1, -4)], -3, Rel::Eq));
        assert!(is_empty(&and(fs.clone()), &[]));
        // Up to 7, which is 3 by 4: a point is left.
        fs[1] = con(&[(0, -1)], 7, Rel::Ge);
        assert!(within(&and(fs), &[]).is_empty());
    }

    #[test]
    fn crossed_bounds_and_an_empty_clause_are_empty() {
        // The empty face: 5 <= x <= 3, and the empty disjunction.
        assert!(is_empty(&and(between(5, 3)), &[]));
        assert!(is_empty(&and(vec![or(Vec::new())]), &[]));
        // An equality of no atoms that fails.
        assert!(is_empty(&and(vec![con(&[], 1, Rel::Eq)]), &[]));
    }

    #[test]
    fn a_clause_keeping_every_residue_leaves_the_face_full() {
        // The full face: `x mod 4` in 0..=1 or in 2..=3 keeps every residue, and a window as
        // long as the modulus reads as no clause of residues.
        let mut fs = between(0, 100);
        fs.push(or(vec![window(1, 4, 0, 1), window(2, 4, 2, 3)]));
        fs.push(or(vec![window(3, 4, 0, 3)]));
        assert!(within(&and(fs), &[]).is_empty());
    }

    #[test]
    fn modulus_one_keeps_every_value() {
        // `x == 1 * q + r` and `x - q == 2` divide by 1: every residue is kept; a hole leaves 7.
        let mut fs = between(5, 7);
        fs.push(con(&[(0, 1), (1, -1), (2, -1)], 0, Rel::Eq));
        fs.push(con(&[(0, 1), (3, -1)], -2, Rel::Eq));
        fs.push(or(vec![
            con(&[(0, -1)], 4, Rel::Ge),
            con(&[(0, 1)], -7, Rel::Ge),
        ]));
        within(&and(fs), &[]);
    }

    #[test]
    fn holes_at_the_ends_bound_the_point_to_the_interval_between_them() {
        // 0 <= x <= 10 with the holes 0..=2 and 8..=10 given, x odd: the first interval
        // between the holes, 3..=7, holds 3, and bounds the point to it.
        let mut fs = between(0, 10);
        fs.push(con(&[(0, 1), (1, -2)], -1, Rel::Eq));
        let h = holes(&[(0, 2), (8, 10)]);
        let x = a(0);
        let w = within(&and(fs.clone()), &[(&x, &h)]);
        assert_eq!(
            w,
            vec![con(&[(0, 1)], -3, Rel::Ge), con(&[(0, -1)], 7, Rel::Ge)]
        );
        // Holes that cover the interval at both ends and between leave nothing.
        let h = holes(&[(0, 2), (3, 7), (8, 10)]);
        assert!(is_empty(&and(fs.clone()), &[(&x, &h)]));
        // A hole given below the lower bound and one above the upper leave it whole.
        let h = holes(&[(-5, -1), (11, 20)]);
        let w = within(&and(fs), &[(&x, &h)]);
        assert_eq!(
            w,
            vec![con(&[(0, 1)], 0, Rel::Ge), con(&[(0, -1)], 10, Rel::Ge)]
        );
    }

    #[test]
    fn holes_given_over_a_bound_atom_are_read_on_its_class() {
        // x1 == x0 + 4, holes over x1 at 4..=9 are x0's at 0..=5; with 0 <= x0 <= 7 and
        // `x0 mod 4 == 1` the interval 6..=7 meets no residue 1.
        let mut fs = between(0, 7);
        fs.push(con(&[(1, 1), (0, -1)], -4, Rel::Eq));
        fs.push(con(&[(0, 1), (2, -4)], -1, Rel::Eq));
        let h = holes(&[(4, 9)]);
        let x1 = a(1);
        assert!(is_empty(&and(fs), &[(&x1, &h)]));
    }

    #[test]
    fn a_division_whose_remainder_is_excluded_keeps_its_residues() {
        // `x mod 4 != 1`: x == 4q + r, 0 <= r <= 3, !(r == 1); with x in 5..=5, empty.
        let division = |lo: i64, hi: i64| {
            let mut fs = between(lo, hi);
            fs.push(con(&[(0, 1), (1, -4), (2, -1)], 0, Rel::Eq));
            fs.push(con(&[(2, 1)], 0, Rel::Ge));
            fs.push(con(&[(2, -1)], 3, Rel::Ge));
            fs.push(Formula::Not(Shared::new(con(&[(2, 1)], -1, Rel::Eq))));
            and(fs)
        };
        assert!(is_empty(&division(5, 5), &[]));
        assert!(is_empty(&division(9, 9), &[]));
        within(&division(5, 6), &[]);
    }

    #[test]
    fn residues_of_two_moduli_are_never_combined() {
        // 3..=4 with `x mod 2 == 1` and `x mod 3 == 1`: each modulus alone meets the interval
        // (3 is odd, 4 is 1 by 3), though no value meets both; left to the solver.
        let mut fs = between(3, 4);
        fs.push(con(&[(0, 1), (1, -2)], -1, Rel::Eq));
        fs.push(con(&[(0, 1), (2, -3)], -1, Rel::Eq));
        within(&and(fs.clone()), &[]);
        // Each alone empties 4..=4 (4 is even) and 3..=3 (3 is 0 by 3).
        fs[0] = con(&[(0, 1)], -4, Rel::Ge);
        assert!(is_empty(&and(fs.clone()), &[]));
        fs[0] = con(&[(0, 1)], -3, Rel::Ge);
        fs[1] = con(&[(0, -1)], 3, Rel::Ge);
        assert!(is_empty(&and(fs), &[]));
    }

    #[test]
    fn clauses_of_one_residue_set_share_a_key() {
        let free = |b: &Atom| *b != a(9);
        // `x mod 4` in 2..=3 or 0, as two links write it, the windows 4 apart and the
        // quotients their own.
        let first = or(vec![window(1, 4, -110, -109), window(1, 4, -112, -112)]);
        let next = or(vec![window(2, 4, -106, -105), window(3, 4, -108, -108)]);
        let key = key(&first, &free).expect("a key");
        assert_eq!(
            key,
            (
                a(0),
                Int::from(4),
                vec![(Int::from(0), Int::from(0)), (Int::from(2), Int::from(3))]
            )
        );
        assert_eq!(super::key(&next, &free), Some(key.clone()));
        // A window across the modulus is split and merged the same way: 3..=4 is 3 and 0.
        let wraps = or(vec![window(4, 4, 3, 4)]);
        let got = super::key(&wraps, &free).expect("a key");
        assert_eq!(
            got.2,
            vec![(Int::from(0), Int::from(0)), (Int::from(3), Int::from(3))]
        );
        // Another residue set, a quotient not free, and a clause of another form have none.
        let other = or(vec![window(5, 4, 1, 1)]);
        assert_ne!(super::key(&other, &free), Some(key));
        assert_eq!(super::key(&or(vec![window(9, 4, 1, 1)]), &free), None);
        let hole = or(vec![
            con(&[(0, -1)], 1, Rel::Ge),
            con(&[(0, 1)], -6, Rel::Ge),
        ]);
        assert_eq!(super::key(&hole, &free), None);
        // Two moduli in one clause have none.
        let mixed = or(vec![window(6, 4, 1, 1), window(7, 6, 1, 1)]);
        assert_eq!(super::key(&mixed, &free), None);
    }
}
