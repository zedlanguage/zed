//! The making of formulas: `true`, `false`, conjunctions and disjunctions ([`Joining`]), the
//! maps that rebuild a formula through them, and the formula of a set ([`member`], [`within`]).
//! They are kept in a file below `presburger.rs`, so that the cover (module `exact`), which
//! builds formulas and which `presburger.rs` calls, does not import `presburger.rs`; and apart
//! from `formula.rs`, which `deep.rs` reads and which `fold` below needs, so that no two of
//! these files import each other (the import graph of `s_01f_import_graph`, row PRES-cover-wire).

#[cfg(feature = "two-at-a-time")]
use std::cell::Cell;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use rustc_hash::FxHashMap;
use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet};

use super::formula::{Atom, Con, Formula, Lin, Model, Rel, Shared};

/// The set `s` of a symbol as a formula: the disjunction of its pieces. The solver and the
/// cover (`exact.rs`) both write sets as formulas.
pub fn member(sym: &Atom, s: &IntervalSet) -> Formula {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Formula {
    let mut pieces = Vec::new();
    for (lo, hi) in s.pieces() {
        let mut both = Vec::new();
        if let End::Fin(v) = lo {
            both.push(Formula::Con(Con::ge(l, &Lin::constant(v))));
        }
        if let End::Fin(v) = hi {
            both.push(Formula::Con(Con::ge(&Lin::constant(v), l)));
        }
        pieces.push(Formula::and(both));
    }
    Formula::or(pieces)
}

impl Formula {
    /// `true`.
    pub fn top() -> Formula {
        Formula::And(Shared::new(Vec::new()))
    }

    /// `false`.
    pub fn bottom() -> Formula {
        Formula::Or(Shared::new(Vec::new()))
    }

    /// The conjunction, flattened, `true` dropped and `false` absorbing.
    pub fn and(fs: Vec<Formula>) -> Formula {
        Formula::and_keeping(fs, |_| false)
    }

    /// [`Formula::and`], with each conjunction at an index of `fs` where `keep` holds kept
    /// whole, as one conjunct, and not flattened into this one. The translator keeps the
    /// formula of a name used as an operand of `&&` (`preimage::Tx::chain`), and the
    /// maps of a formula keep a conjunction that was kept in the node they rebuild
    /// (`Formula::rebuild`), so whether a part is kept follows the program and never how
    /// many handles hold it. A kept conjunction is read as flattened by compare, hash
    /// and show (`deep::Flat`), and, each kept part at its first place alone, by
    /// `Formula::conjuncts`, by `Conjuncts::and` and by `Parts::of`.
    // Complexity tradeoff: a kept conjunction is not merged into this one, so the tightening
    // below (one constraint per left-hand side) does not reach the constraints inside it, and a
    // constraint written both inside it and beside it is kept twice. No point is given up and
    // no answer changes; the printed relation lists the named part's constraints as written.
    // Merging would copy the named part's k constraints into each of the d places that use it,
    // O(d k), quadratic in the size of the program when k is about d. Trigger: a name of a
    // conjunction used as an operand of `&&`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete merge needs the conjunction as a persistent map from each
    // left-hand side to its constraint, shared with the named part and extended at each place.
    pub fn and_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(feature = "two-at-a-time")]
        if TWO_AT_A_TIME.get() {
            return before::and_keeping_before(fs, keep);
        }
        let mut j = Joining::new(true);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
    }

    /// The disjunction, flattened, `false` dropped and `true` absorbing, and `true` when two
    /// disjuncts are complements (`Formula::complementary`).
    pub fn or(fs: Vec<Formula>) -> Formula {
        Formula::or_keeping(fs, |_| false)
    }

    /// [`Formula::or`], with each disjunction at an index of `fs` where `keep` holds kept
    /// whole, as one disjunct, as [`Formula::and_keeping`] keeps a conjunction: the formula of
    /// a name used as an operand of `||`, and a disjunction kept in the node a map rebuilds.
    // Complexity tradeoff: a kept disjunction is not merged into this one, so `complementary`
    // does not find a constraint inside it beside its complement outside it, and the disjunction
    // stays one, which holds at the same points: no answer changes, but each later test splits
    // into its cases. Merging would copy the named part's k disjuncts into each of the d places
    // that use it, O(d k). Trigger: a name of a disjunction used as an operand of `||`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete check needs each kept part's constraints indexed in its
    // node, so that the lookup across it costs O(1) per disjunct.
    pub fn or_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(feature = "two-at-a-time")]
        if TWO_AT_A_TIME.get() {
            return before::or_keeping_before(fs, keep);
        }
        let mut j = Joining::new(false);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
    }

    /// Whether two of `fs` are each other's complements, so that their disjunction is `true`:
    /// a constraint `c` and `!c`, or `t >= 0` and `s >= 0` with `t + s` a constant of at least
    /// `-1`, since at an integer point `t <= -1` makes `s >= 0`. Each disjunct that is a
    /// constraint or the negation of one is looked up once by its content, so the check costs
    /// the size of the constraints in `fs` and never the depth of a compound disjunct.
    // Complexity tradeoff: a compound `g || !g`, with `g` a conjunction or disjunction, is not
    // found and stays a disjunction. That is sound, since the disjunction holds at every point,
    // but each later test splits into its cases, as before this check (COMPLEXITY.md S20).
    // Looking `g` up by its content hashes it through its whole depth on every `Formula::or`,
    // and `map_cons`, `nnf` and `forget` call `or` once per `Or` node, so a nested or/and
    // formula would cost its size times its depth (62 times the work for 8 times the depth,
    // measured at d = 500 to 4000). The trigger is a disjunct that is not a constraint. Tests
    // in `l01_39_scope_relations::linked`: `a_disjunction_of_a_constraint_and_its_complement_is_true`
    // and `a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size`. A complete check
    // needs a hash of each formula kept in its node when it is built, so that the lookup costs
    // O(1) per disjunct.
    fn complementary(fs: &[Formula]) -> bool {
        if fs.len() < 2 {
            return false;
        }
        let mut ge: HashMap<&BTreeMap<Atom, Int>, &Int> = HashMap::new();
        let mut whole: std::collections::HashSet<&Con> = std::collections::HashSet::new();
        for f in fs {
            let Formula::Con(c) = f else { continue };
            whole.insert(c);
            if c.rel == Rel::Ge {
                // Of two disjuncts on one term, the weaker, the larger constant, decides.
                let k = ge.entry(&c.lin.terms).or_insert(&c.lin.constant);
                if c.lin.constant > **k {
                    *k = &c.lin.constant;
                }
            }
        }
        fs.iter().any(|f| match f {
            Formula::Not(g) => matches!(&**g, Formula::Con(c) if whole.contains(c)),
            Formula::Con(c) if c.rel == Rel::Ge => {
                let neg: BTreeMap<Atom, Int> =
                    c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect();
                ge.get(&neg)
                    .is_some_and(|k| &c.lin.constant + *k >= Int::from(-1i64))
            }
            _ => false,
        })
    }

    /// The disjunction of `a` and `b` with the conjuncts they share taken out of it, so that
    /// joining two narrowings of one relation does not copy the relation into each disjunct.
    /// Each constraint of the rest of each side is replaced by `rest` of it. When the rest of
    /// one side is one constraint `c`, a conjunct `d` of the other with `c || d` true
    /// (`complements`) is dropped, since `c || (d && r)` is `(c || d) && (c || r)`, that is
    /// `c || r`: the two cases of `!(x >= n && x >= m)`, `x < n` and `x >= n && x < m`, join
    /// to `x < n || x < m`, which bounds `x` on one side alone
    /// ([`crate::conjuncts::Conjuncts::star`]).
    pub fn either(a: &Formula, b: &Formula, rest: &dyn Fn(&Con) -> Formula) -> Formula {
        fn parts(f: &Formula) -> &[Formula] {
            match f {
                Formula::And(gs) => gs,
                g => std::slice::from_ref(g),
            }
        }
        let (pa, pb) = (parts(a), parts(b));
        let in_b: std::collections::HashSet<&Formula> = pb.iter().collect();
        let shared: std::collections::HashSet<&Formula> =
            pa.iter().filter(|g| in_b.contains(g)).collect();
        let oa: Vec<&Formula> = pa.iter().filter(|g| !shared.contains(g)).collect();
        let ob: Vec<&Formula> = pb.iter().filter(|g| !shared.contains(g)).collect();
        let (ca, cb) = (
            (oa.len() == 1).then(|| oa[0]),
            (ob.len() == 1).then(|| ob[0]),
        );
        let left = |o: &[&Formula], other: Option<&Formula>| {
            Formula::and(
                o.iter()
                    .filter(|g| other.is_none_or(|c| !complements(c, g)))
                    .map(|g| g.map_cons(rest))
                    .collect(),
            )
        };
        let (la, lb) = (left(&oa, cb), left(&ob, ca));
        let mut out: Vec<Formula> = pa.iter().filter(|g| shared.contains(g)).cloned().collect();
        out.push(Formula::or(vec![la, lb]));
        Formula::and(out)
    }

    /// The formula with every constraint that mentions `sym`, alone or in a product,
    /// replaced by `true` where it occurs under an even number of negations and by `false`
    /// where under an odd number: a formula implied by `self` that says nothing of `sym`.
    pub fn forget(&self, sym: &Arc<str>) -> Formula {
        // The context is whether the part is under an even number of negations.
        self.fold(
            true,
            |g, pos| pos != matches!(g, Formula::Not(_)),
            |g, pos, parts| match g {
                Formula::Con(c) => {
                    let mentions = c.lin.terms.keys().any(|a| match a {
                        Atom::Sym(n) => n == sym,
                        Atom::Product(x, y) => x.is(sym) || y.is(sym),
                        Atom::Aux(_) => false,
                    });
                    match (mentions, pos) {
                        (false, _) => g.clone(),
                        (true, true) => Formula::top(),
                        (true, false) => Formula::bottom(),
                    }
                }
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The formula with each constraint `c` replaced by `f(c)`.
    pub fn map_cons(&self, f: &dyn Fn(&Con) -> Formula) -> Formula {
        self.fold(
            (),
            |_, ()| (),
            |g, (), parts| match g {
                Formula::Con(c) => f(c),
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The node `self` with `parts` in place of its parts, through [`Formula::negate`],
    /// [`Formula::and_keeping`] or [`Formula::or_keeping`]; a constraint has no parts and is
    /// copied. A part in the place of a conjunction kept in a conjunction, or of a disjunction
    /// kept in a disjunction ([`Formula::kept`]), is kept whole.
    pub(super) fn rebuild(&self, mut parts: Vec<Formula>) -> Formula {
        match self {
            Formula::Con(c) => Formula::Con(c.clone()),
            Formula::Not(_) => Formula::negate(parts.pop().expect("one part")),
            Formula::And(_) => Formula::and_keeping(parts, |i| self.kept(i)),
            Formula::Or(_) => Formula::or_keeping(parts, |i| self.kept(i)),
        }
    }

    /// Whether the part at `i` of `self` is a conjunction kept whole in a conjunction, or a
    /// disjunction kept whole in a disjunction.
    pub(super) fn kept(&self, i: usize) -> bool {
        match self {
            Formula::And(gs) => matches!(gs[i], Formula::And(_)),
            Formula::Or(gs) => matches!(gs[i], Formula::Or(_)),
            Formula::Con(_) | Formula::Not(_) => false,
        }
    }

    /// The negation, with double negations and constants removed.
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::Not(_) => f.into_negated().expect("a negation"),
            Formula::And(ref gs) if gs.is_empty() => Formula::bottom(),
            Formula::Or(ref gs) if gs.is_empty() => Formula::top(),
            g => Formula::Not(Shared::new(g)),
        }
    }

    /// Whether the formula holds at `values`; an absent atom is zero, and a product atom is
    /// read as the product of its factors' values.
    /// Each product is read where it is met, so a disjunct that is decided by its first part is
    /// not walked through.
    pub fn holds(&self, values: &Model) -> bool {
        self.holds_as(values)
    }
}

/// Whether `f || g` holds at every integer point, by their forms: a constraint and its
/// negation, or `t >= 0` and `s >= 0` with `t + s` a constant of at least `-1`, as
/// [`Formula::complementary`] finds among many. In time near the constraints' size.
fn complements(f: &Formula, g: &Formula) -> bool {
    match (f, g) {
        (Formula::Con(c), Formula::Not(n)) | (Formula::Not(n), Formula::Con(c)) => {
            matches!(&**n, Formula::Con(d) if d == c)
        }
        (Formula::Con(c), Formula::Con(d)) if c.rel == Rel::Ge && d.rel == Rel::Ge => {
            c.lin.terms.len() == d.lin.terms.len()
                && c.lin
                    .terms
                    .iter()
                    .all(|(a, k)| d.lin.terms.get(a).is_some_and(|j| j == &-k))
                && &c.lin.constant + &d.lin.constant >= Int::from(-1i64)
        }
        _ => false,
    }
}

/// A conjunction or a disjunction made one operand at a time: [`Formula::and_keeping`] and
/// [`Formula::or_keeping`] give it their operands, and the translator gives it each operand of
/// a chain of `&&` or of `||` (`preimage::Tx::chain`), so that a chain of k operands costs
/// O(k log k), and not the O(k²) that making the conjunction of each prefix in turn costs,
/// which copied and tightened the prefix again at each operand (ST-formula-k2).
pub struct Joining {
    /// A conjunction, or a disjunction.
    and: bool,
    /// The parts so far.
    out: Vec<Formula>,
    /// Of a conjunction, the places in `out` of the constraints whose terms and comparison have
    /// each hash ([`Joining::key`]); one place per term and comparison, and more than one in a
    /// list only where two share a 64-bit hash by chance.
    // Complexity tradeoff: this was a `BTreeMap` keyed by a copy of each constraint's terms, so
    // each part cost a copy of its terms and O(log n) comparisons of terms, each comparing atom
    // names: 228 ms of 38,001 equations in `signed` (FAIL-rewrite-growth-both), more than the
    // whole decision after it. The hash costs one pass over the terms and no copy, O(k) for k
    // terms, and the terms are compared only within one list. Nothing iterates the map, so its
    // order plays no part. Test `bench::names::decide_scales_over_one_class_of_equalities`.
    at: FxHashMap<u64, Vec<usize>>,
    /// Whether an operand decided the whole: `false` met in a conjunction, two constraints on
    /// one term that cannot both hold, or `true` met in a disjunction.
    decided: bool,
    /// How many parts were added, a constraint merged into an earlier one counted too.
    added: usize,
}

/// Where a [`Joining`] was, from [`Joining::mark`].
#[derive(Clone, Copy)]
pub struct Mark {
    /// The count of parts added, a constraint merged into an earlier one counted too.
    added: usize,
    /// The length of `out`.
    len: usize,
}

impl Joining {
    /// An empty conjunction when `and`, otherwise an empty disjunction.
    pub fn new(and: bool) -> Joining {
        Joining {
            and,
            out: Vec::new(),
            at: FxHashMap::default(),
            decided: false,
            added: 0,
        }
    }

    /// Adds the operand `f`. A part of the joining's own kind is kept whole where `kept`, and
    /// otherwise its parts are added; the empty one of that kind is dropped, and the empty
    /// one of the other kind decides the whole.
    pub fn operand(&mut self, f: Formula, kept: bool) {
        if self.decided {
            return;
        }
        let (own, empty) = match &f {
            Formula::And(gs) => (self.and, gs.is_empty()),
            Formula::Or(gs) => (!self.and, gs.is_empty()),
            Formula::Con(_) | Formula::Not(_) => (false, false),
        };
        match (own, empty) {
            (true, true) => {}
            (false, true) => self.decided = true,
            (true, false) if !kept => {
                for g in f.into_parts().expect("a conjunction or a disjunction") {
                    self.part(g);
                }
            }
            _ => self.part(f),
        }
    }

    /// Adds `g` as a part. Of two constraints in a conjunction on one term and comparison,
    /// the tighter alone, in the place of the first.
    fn part(&mut self, g: Formula) {
        if self.decided {
            return;
        }
        self.added += 1;
        let Formula::Con(c) = &g else {
            self.out.push(g);
            return;
        };
        if !self.and {
            self.out.push(g);
            return;
        }
        let places = self.at.entry(Joining::key(c)).or_default();
        let same = places.iter().copied().find(|&i| match &self.out[i] {
            Formula::Con(old) => old.rel == c.rel && old.lin.terms == c.lin.terms,
            _ => unreachable!("a constraint"),
        });
        match same {
            Some(i) => {
                let Formula::Con(old) = &self.out[i] else {
                    unreachable!("a constraint")
                };
                if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                    self.out[i] = g;
                } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                    self.decided = true;
                }
            }
            None => {
                places.push(self.out.len());
                self.out.push(g);
            }
        }
    }

    /// The hash of the terms and the comparison of `c`, its constant left out.
    fn key(c: &Con) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = rustc_hash::FxHasher::default();
        c.rel.hash(&mut h);
        c.lin.terms.hash(&mut h);
        h.finish()
    }

    /// Where the joining is now, to pass to [`Joining::close`].
    pub fn mark(&self) -> Mark {
        Mark {
            added: self.added,
            len: self.out.len(),
        }
    }

    /// Ends an inner operand of the chain, one that is itself a `&&` in a chain of `&&` (or a
    /// `||` in one of `||`), whose operands are those added since `mark`. Made apart, such an
    /// operand is the formula `finish` gives, which is its one part where it has one, and
    /// the chain around it adds that part as an operand that is not kept: its parts when it
    /// is of the joining's kind, nothing when it is the empty one of that kind, and the whole
    /// decided when it is the empty one of the other. This does the same, so that the chain
    /// gives the formula of its operands joined two at a time as written.
    pub fn close(&mut self, mark: Mark) {
        // One part added since `mark` and one more in `out`: the operand made apart is that
        // part alone, the last of `out`. A constraint merged into an earlier one is counted in
        // `added` alone, and the operand made apart holds it as a part of its own.
        if self.decided || self.added - mark.added != 1 || self.out.len() - mark.len != 1 {
            return;
        }
        let unwraps = match self.out.last() {
            Some(Formula::And(gs)) => self.and || gs.is_empty(),
            Some(Formula::Or(gs)) => !self.and || gs.is_empty(),
            _ => false,
        };
        if !unwraps {
            return;
        }
        let last = self.out.pop().expect("the last part");
        self.added -= 1;
        self.operand(last, false);
    }

    /// The conjunction or disjunction: its one part where it has one, and `true` for a
    /// disjunction of two complementary parts (`Formula::complementary`).
    pub fn finish(mut self) -> Formula {
        if self.decided {
            return if self.and {
                Formula::bottom()
            } else {
                Formula::top()
            };
        }
        if !self.and && Formula::complementary(&self.out) {
            return Formula::top();
        }
        if self.out.len() == 1 {
            self.out.pop().expect("one")
        } else if self.and {
            Formula::And(Shared::new(self.out))
        } else {
            Formula::Or(Shared::new(self.out))
        }
    }
}

#[cfg(feature = "two-at-a-time")]
thread_local! {
    /// Whether [`Formula::and_keeping`] and [`Formula::or_keeping`] join as they did before
    /// [`Joining`], and the translator joins a chain of `&&` or `||` two at a time
    /// (`preimage::Tx::two_at_a_time`): for the tests that compare the two (ST-formula-k2). Only with
    /// the feature `two-at-a-time`, which the crate that holds `preimage` turns on for its tests.
    pub static TWO_AT_A_TIME: Cell<bool> = const { Cell::new(false) };
}

/// The joins as they were before [`Joining`], which [`TWO_AT_A_TIME`] selects and the tests compare
/// against.
#[cfg(any(test, feature = "two-at-a-time"))]
pub(super) mod before {
    use super::*;

    /// `Formula::and_keeping` as it was before `Joining`, to compare against.
    pub(in super::super) fn and_keeping_before(
        fs: Vec<Formula>,
        keep: impl Fn(usize) -> bool,
    ) -> Formula {
        let mut flat = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::And(ref gs) if gs.is_empty() => {}
                Formula::And(_) if keep(i) => flat.push(f),
                Formula::And(_) => flat.extend(f.into_parts().expect("a conjunction")),
                Formula::Or(ref gs) if gs.is_empty() => return Formula::bottom(),
                g => flat.push(g),
            }
        }
        // Of two constraints on one term, the tighter alone, in the place of the first.
        let mut out: Vec<Formula> = Vec::new();
        let mut at: BTreeMap<(BTreeMap<Atom, Int>, Rel), usize> = BTreeMap::new();
        for g in flat {
            let Formula::Con(c) = &g else {
                out.push(g);
                continue;
            };
            let key = (c.lin.terms.clone(), c.rel);
            match at.get(&key) {
                Some(&i) => {
                    let Formula::Con(old) = &out[i] else {
                        unreachable!("a constraint")
                    };
                    if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                        out[i] = g;
                    } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                        return Formula::bottom();
                    }
                }
                None => {
                    at.insert(key, out.len());
                    out.push(g);
                }
            }
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::And(Shared::new(out))
        }
    }

    /// `Formula::or_keeping` as it was before `Joining`, to compare against.
    pub(in super::super) fn or_keeping_before(
        fs: Vec<Formula>,
        keep: impl Fn(usize) -> bool,
    ) -> Formula {
        let mut out = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::Or(ref gs) if gs.is_empty() => {}
                Formula::Or(_) if keep(i) => out.push(f),
                Formula::Or(_) => out.extend(f.into_parts().expect("a disjunction")),
                Formula::And(ref gs) if gs.is_empty() => return Formula::top(),
                g => out.push(g),
            }
        }
        if Formula::complementary(&out) {
            return Formula::top();
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::Or(Shared::new(out))
        }
    }
}
