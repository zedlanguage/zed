//! The rule that removes a top-level disjunction which changes no answer once the atoms private
//! to one of its disjuncts are projected away. Two callers read it: the solver, on the parts of
//! a formula (`absorb` in `presburger.rs`, which holds the proof and the cost), and the exact
//! cover, on the conjuncts of a formula (`exact::reduced`). It is a module of its own, below
//! both, so that the cover does not import the solver (`s_01f_import_graph`, as module `meter`).

use std::collections::{BTreeMap, HashMap, HashSet};

use zedc_int::int::Int;

use super::{Atom, Con, Rel};

/// A disjunct as [`removable`] reads it: its own rows, whether it holds a disjunction of its
/// own, and the atoms it reads at any depth.
pub(super) struct Arm<'a> {
    pub(super) rows: Vec<&'a Con>,
    pub(super) nested: bool,
    pub(super) atoms: Vec<&'a Atom>,
}

/// The rows over one atom on one side, read by [`removable`]: each row `x + r >= 0` (a lower
/// bound) or `-x + r >= 0` (an upper bound) by its rest `r`, written as its terms and its
/// constant.
#[derive(Default)]
enum Side<'a> {
    /// No row.
    #[default]
    Empty,
    /// Every row has these terms; the least constant among them.
    Shared(Vec<(&'a Atom, &'a Int)>, &'a Int),
    /// Two rows differ in their terms.
    Mixed,
}

impl<'a> Side<'a> {
    /// Adds the row whose rest has the terms `terms` and the constant `k`.
    fn add(&mut self, terms: Vec<(&'a Atom, &'a Int)>, k: &'a Int) {
        match self {
            Side::Empty => *self = Side::Shared(terms, k),
            Side::Shared(t, least) if *t == terms => *least = (*least).min(k),
            Side::Shared(..) => *self = Side::Mixed,
            Side::Mixed => {}
        }
    }

    /// Whether every lower bound of `self` and upper bound of `upper` sum to a constant at
    /// least zero: their terms cancel, and the least constants sum to zero or more.
    fn fits(&self, upper: &Side<'_>) -> bool {
        match (self, upper) {
            (Side::Empty, _) | (_, Side::Empty) => true,
            (Side::Shared(l, kl), Side::Shared(u, ku)) => {
                l.len() == u.len()
                    && l.iter().zip(u).all(|((a, k), (b, j))| a == b && **k == -*j)
                    && !(*kl + *ku).is_negative()
            }
            _ => false,
        }
    }
}

/// The row `c` read as a bound on `x` ([`Side`]): whether it is a lower bound, and the terms of
/// its rest; `None` when it is an equality or the coefficient of `x` is not 1 or -1.
fn unit_bound<'a>(c: &'a Con, x: &Atom) -> Option<(bool, Vec<(&'a Atom, &'a Int)>)> {
    let k = c.lin.terms.get(x)?;
    let lower = *k == Int::ONE;
    if c.rel != Rel::Ge || !(lower || *k == -&Int::ONE) {
        return None;
    }
    let rest = c.lin.terms.iter().filter(|(a, _)| *a != x).collect();
    Some((lower, rest))
}

/// For the conjunction of the rows `base` and the disjunctions `ors`, which of `ors` may be
/// removed, each changing no answer read over the atoms outside the private atoms of the
/// disjunct that shows it (the rule and its proof: `absorb` in `presburger.rs`), and, for each
/// such atom, the rows over it (the base's and that disjunct's). An atom `keep` holds is never
/// private. A conjunct that is not a disjunction of rows is given as a disjunction of one arm
/// marked `nested`: it removes nothing, and its atoms are held by it.
pub(super) fn removable(
    base: &[&Con],
    ors: &[Vec<Arm<'_>>],
    keep: &dyn Fn(&Atom) -> bool,
) -> (Vec<bool>, Vec<(Atom, Vec<Con>)>) {
    // The top-level disjunction that holds each atom of a disjunction, or `None` when two or
    // more do.
    let mut owner: HashMap<&Atom, Option<usize>> = HashMap::new();
    for (j, ds) in ors.iter().enumerate() {
        for &a in ds.iter().flat_map(|d| &d.atoms) {
            let o = owner.entry(a).or_insert(Some(j));
            if *o != Some(j) {
                *o = None;
            }
        }
    }
    let mut factors: HashSet<Atom> = HashSet::new();
    for a in (base.iter().flat_map(|c| c.lin.terms.keys())).chain(owner.keys().copied()) {
        if let Atom::Product(x, y) = a {
            factors.insert(x.atom());
            factors.insert(y.atom());
        }
    }
    // The disjunction that alone holds `a`, when `a` may be private to one of its disjuncts.
    let held_by = |a: &Atom| match (a, owner.get(a)) {
        (Atom::Product(..), _) => None,
        (_, Some(Some(j))) if !keep(a) && !factors.contains(a) => Some(*j),
        _ => None,
    };
    // The base's bounds on each such atom, its rows, and whether a row over it is not a unit
    // inequality with no other such atom.
    #[derive(Default)]
    struct Bounds<'a> {
        lower: Side<'a>,
        upper: Side<'a>,
        rows: Vec<&'a Con>,
        bad: bool,
    }
    let mut bounds: HashMap<&Atom, Bounds<'_>> = HashMap::new();
    for &c in base {
        let mut own = c.lin.terms.keys().filter(|a| held_by(a).is_some());
        let Some(x) = own.next() else {
            continue;
        };
        if own.next().is_some() {
            for a in c.lin.terms.keys().filter(|a| held_by(a).is_some()) {
                bounds.entry(a).or_default().bad = true;
            }
            continue;
        }
        let b = bounds.entry(x).or_default();
        b.rows.push(c);
        match unit_bound(c, x) {
            Some((true, rest)) => b.lower.add(rest, &c.lin.constant),
            Some((false, rest)) => b.upper.add(rest, &c.lin.constant),
            None => b.bad = true,
        }
    }
    let none = Bounds::default();
    // The rows of each private atom of `d`, a disjunct of disjunction `j`, when `d` shows that
    // `j` removes no point.
    let serves = |j: usize, d: &Arm<'_>| -> Option<Vec<(Atom, Vec<Con>)>> {
        if d.nested {
            return None;
        }
        let mut own: BTreeMap<&Atom, (Side<'_>, Side<'_>, Vec<&Con>)> = BTreeMap::new();
        for &c in &d.rows {
            let mut xs = (c.lin.terms.keys()).filter(|a| held_by(a) == Some(j));
            let (Some(x), None) = (xs.next(), xs.next()) else {
                return None;
            };
            let (lower, rest) = unit_bound(c, x)?;
            let (dl, du, rows) = own.entry(x).or_default();
            (if lower { dl } else { du }).add(rest, &c.lin.constant);
            rows.push(c);
        }
        let mut out = Vec::new();
        for (x, (dl, du, rows)) in own {
            let b = bounds.get(x).unwrap_or(&none);
            if b.bad || !(b.lower.fits(&du) && dl.fits(&du) && dl.fits(&b.upper)) {
                return None;
            }
            let all = b.rows.iter().chain(&rows).map(|&c| c.clone());
            out.push((x.clone(), all.collect()));
        }
        Some(out)
    };
    let mut removed = vec![false; ors.len()];
    let mut gone = Vec::new();
    for (j, ds) in ors.iter().enumerate() {
        if let Some(rows) = ds.iter().find_map(|d| serves(j, d)) {
            removed[j] = true;
            gone.extend(rows);
        }
    }
    (removed, gone)
}
