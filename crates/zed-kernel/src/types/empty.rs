//! Emptiness and subtyping (step L1.23, DESIGN.md sec:type_language): `a <: b` iff `a & !b`
//! is empty, decided by a memoized coinductive check.
//!
//! A type is empty when every part is. The scalar and struct parts are exact, so their
//! emptiness is read off. The tuple part of each length, a Boolean combination of tuple types
//! (module `bdd`), is decided on a box, one type per component, starting from the whole
//! product: each tuple type is known to hold the box, known to miss it, or open on it; the
//! part is evaluated in three-valued logic on what is known; a tuple type in every value of
//! the part narrows the box to it, and one in no value takes itself out of the one component
//! where it does not hold the box. What is known is kept in a table of cells: for each
//! component, one cell for each distinct type the tuple types take there, tested once for all
//! the tuple types that share it, and closed when it holds or misses the box in that component.
//! A cell that misses or holds a component still does when the box shrinks, so only the
//! components changed since they were last tested are tested again, against their open cells,
//! all tests of missing before any test of holding. When narrowing stops and every open tuple
//! type is open on a component whose cells fall into classes sharing no value, the box is split
//! by class, in halves, each half deciding the part with the other half's tuple types taken as
//! false. Otherwise a component whose pieces cut by the open tuple types are pairwise equal or
//! disjoint is split into those pieces, and each piece
//! decided; otherwise each piece on which narrowing alone proves the part empty is taken out
//! of the box; otherwise, once on each branch, when the part holds nothing outside the open
//! tuple types, the box is split into its meet with each of them. A box none of these steps
//! settles counts as inhabited. The morphism part is decided the same way, by the variance
//! law: contravariant in the guarantee, covariant in the permission and the value type.
//!
//! So `is_empty` is sound, never empty for an inhabited type, and its time is polynomial in
//! the types written; it is not complete, since emptiness of Boolean combinations of tuple
//! types is coNP-hard. A part that only a split of the box in more than one component at once
//! proves empty counts as inhabited: a subtyping check then fails, and the error names the
//! types, so the program states the case split itself (DESIGN.md L1.23).
//!
//! Complexity tradeoff: what is given up, why and the trigger are the paragraph above: a
//! part that only a split of the box in two or more components at once proves empty counts as
//! inhabited (a subtyping check fails; the representative search of `no_morphism` likewise
//! answers "none found", never "empty"). Test:
//! `l01_23_subtyping::scaling::a_type_not_proved_empty_promises_no_key` (four pigeons in three
//! holes, empty and not proved so). COMPLEXITY.md rows K1 and K2, and the Kept row
//! "emptiness and subtyping of tuple and morphism parts".
//! A complete solution would split the box in every component (a DPLL search over the tuple
//! types, exponential in them), or hand the part to a SAT solver.
//!
//! A query goes in this order, each step a function of the query alone: the simulation proves
//! `a <: b` for unions written without negation; a value built from the rows as written shows a
//! type inhabited; the residue rule speaks for pure cycles; a union of rows is empty row by row;
//! the search decides the rest. `Type::verdict` stops the search at a fork, two rows open on one
//! box that differ in a recursive column, and answers `Refused`.
//!
//! The answer is least on tuples and greatest on morphism values: a value is a finite closed
//! term, and each cycle in it passes through a closure, so `S = (int) -> S` is inhabited and
//! `E = (int, E)` is not. A morphism type with an empty value type holds nothing; the value
//! types are read as inhabited until a round proves them empty, and rounds repeat until none is
//! newly proved.
//!
//! The check is coinductive: a type met again while its own emptiness is being decided is
//! assumed empty. Values are finite, so a type whose every value would contain a smaller value
//! of the same type is empty, which is the answer the assumption gives; contractive, regular
//! and monotone definitions (module `rec`) make the set of types met finite. A result, empty
//! or inhabited, that rests on an assumption later found false is dropped, and only such a
//! result, so no result is decided again unless an assumption it read changed: a tuple type
//! wrongly assumed disjoint from the box leaves a clause, so a wrong assumption can make a
//! type count as inhabited too. Results are kept for the thread, until
//! `Type::forget_emptiness`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use super::bdd::Part;
use super::{Lits, Morphism, Parts, Row, Type};
use crate::value::Value;

thread_local! {
    static MEMO: RefCell<BTreeMap<Type, bool>> = const { RefCell::new(BTreeMap::new()) };
    /// The verdict of each type asked. A verdict is decided by a search that reads no kept
    /// result, so it is a function of the type alone, and keeping it changes no answer: these
    /// are the types proved empty and those with a checked value, and the refusals.
    static VERDICTS: RefCell<BTreeMap<Type, Verdict>> = const { RefCell::new(BTreeMap::new()) };
}

/// The outcomes of a check; each has its own message.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// No value is in the type.
    Empty,
    /// A value in the type was built and checked against it.
    Inhabited,
    /// Not proved empty, and no value built: nothing is claimed about the type.
    Refused(Refusal),
}

/// Why a check was refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// A tuple part holds two tuple types, both open on one box, that differ in a recursive
    /// component: following both is the subset construction.
    Fork,
    /// Negated lists of periodic lengths: whether they cover the lengths left is the covering
    /// problem for residues, which is NP-hard.
    Residues,
    /// A tuple part that only a split of the box in more than one component at once decides.
    TupleSplit,
    /// A morphism part that neither the meets it forces nor a split into its morphism types
    /// decides.
    MorphismSplit,
    /// The search ended with the type not proved empty, and no value of it was built.
    NoWitness,
}

impl Refusal {
    /// What the refusal says to the programmer.
    pub fn message(self) -> &'static str {
        match self {
            Refusal::Fork => {
                "two tuple types of it differ in a recursive component on one box; deciding it \
                 would follow both, which is the subset construction"
            }
            Refusal::Residues => {
                "its lengths are residues of periodic lists, and deciding whether the excluded \
                 lists cover them is the covering problem for residues (NP-hard)"
            }
            Refusal::TupleSplit => {
                "a tuple part is decided only by a case split in more than one component at \
                 once; write the case split as a union"
            }
            Refusal::MorphismSplit => {
                "a function part is decided neither by the types it forces nor by a split into \
                 its function types"
            }
            Refusal::NoWitness => "it was not proved empty, and no value of it could be built",
        }
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

impl Type {
    /// Drops the kept emptiness results. A unit's checker calls it first: a type equal to a
    /// kept one but built apart from it is compared with it in full, so a result kept from
    /// another unit costs the size of the type at each lookup.
    pub fn forget_emptiness() {
        MEMO.with(|m| m.borrow_mut().clear());
        VERDICTS.with(|m| m.borrow_mut().clear());
    }

    /// Whether no value is in `self`.
    pub fn is_empty(&self) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(self).copied()) {
            return b;
        }
        let mut s = Search::default();
        let b = s.solve(self);
        MEMO.with(|m| {
            m.borrow_mut()
                .extend(s.types.iter().cloned().zip(s.answer.iter().copied()))
        });
        b
    }

    /// Whether `self` is empty, shown inhabited by a checked value, or refused: not proved
    /// empty, and no value found. Kept results are not read, since those of `is_empty` carry no
    /// value and would make the outcome depend on the queries before it.
    pub fn verdict(&self) -> Verdict {
        if let Some(v) = VERDICTS.with(|m| m.borrow().get(self).copied()) {
            return v;
        }
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            ..Search::default()
        };
        let b = s.solve(self);
        let decided = s.refused.is_none();
        let v = if decided && b {
            Verdict::Empty
        } else if decided
            && (s.ids.get(self).is_some_and(|t| s.witnessed.contains(t)) || s.rep(self).is_some())
        {
            Verdict::Inhabited
        } else if (Search {
            strict: true,
            ..Search::default()
        })
        .rep(self)
        .is_some()
        {
            // Before a refusal, a value is sought by a search that does not stop at a fork.
            Verdict::Inhabited
        } else {
            Verdict::Refused(s.refused.or(s.gave_up).unwrap_or(Refusal::NoWitness))
        };
        VERDICTS.with(|m| m.borrow_mut().insert(self.clone(), v));
        v
    }

    /// Whether every value of `self` is in `other`: `self <: other`.
    pub fn subtype(&self, other: &Type) -> bool {
        Simulation::default().holds(self, other) || (self - other).is_empty()
    }

    /// The outcome of `self <: other`: `Empty` when it holds, `Inhabited` when a value of `self`
    /// outside `other` was built.
    pub fn subtype_verdict(&self, other: &Type) -> Verdict {
        if Simulation::default().holds(self, other) {
            Verdict::Empty
        } else {
            (self - other).verdict()
        }
    }

    /// Whether `self` and `other` denote one set of values.
    pub fn equiv(&self, other: &Type) -> bool {
        self.subtype(other) && other.subtype(self)
    }
}

/// A proof of `a <: b` for unions of tuple types written without negation, with no box split:
/// the largest relation on pairs of types such that each row of `a` lies column by column under
/// one row of `b`. By induction on a value, a value of `a` is in `b`. It is sufficient only, so a
/// pair outside it goes to `Search`. Each pair is a node; a node that fails is taken out, and
/// each choice of a row that needs it is struck once: a row with no choice left fails its node.
/// So the work after the pairs are made is linear in what they need, as in Horn satisfiability.
/// The pairs met are at most the product of the types, and only those reached are made: a row
/// is compared with the rows of `b` that share its first column, when any do, so unions keyed
/// by a scalar cost one row each.
#[derive(Default)]
struct Simulation {
    pairs: BTreeMap<(Type, Type), usize>,
    nodes: Vec<Pair>,
}

#[derive(Default)]
struct Pair {
    /// For each row of the left side, whether each row that may hold it is struck out.
    struck: Vec<Vec<bool>>,
    /// For each row of the left side, how many rows that may hold it are not struck out.
    left: Vec<usize>,
    /// Each choice that needs this pair: the pair, its row and the choice.
    readers: Vec<(usize, usize, usize)>,
    failed: bool,
}

impl Simulation {
    fn holds(mut self, a: &Type, b: &Type) -> bool {
        let root = self.pair(a, b);
        let mut failed: Vec<usize> = (0..self.nodes.len())
            .filter(|&i| self.nodes[i].failed)
            .collect();
        while let Some(i) = failed.pop() {
            for (r, row, alt) in std::mem::take(&mut self.nodes[i].readers) {
                let n = &mut self.nodes[r];
                if n.failed || std::mem::replace(&mut n.struck[row][alt], true) {
                    continue;
                }
                n.left[row] -= 1;
                if n.left[row] == 0 {
                    n.failed = true;
                    failed.push(r);
                }
            }
        }
        !self.nodes[root].failed
    }

    fn pair(&mut self, a: &Type, b: &Type) -> usize {
        let key = (a.clone(), b.clone());
        if let Some(&i) = self.pairs.get(&key) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push(Pair::default());
        self.pairs.insert(key, i);
        if a != b {
            let Some(needs) = self.rows(a.p(), b.p()) else {
                self.nodes[i].failed = true;
                return i;
            };
            for (row, alts) in needs.iter().enumerate() {
                for (alt, ks) in alts.iter().enumerate() {
                    for &k in ks {
                        self.nodes[k].readers.push((i, row, alt));
                    }
                }
            }
            let n = &mut self.nodes[i];
            n.left = needs.iter().map(Vec::len).collect();
            n.struck = needs.iter().map(|alts| vec![false; alts.len()]).collect();
            n.failed = n.left.contains(&0);
        }
        i
    }

    /// What `a` under `b` needs of pairs, or none if it fails here.
    fn rows(&mut self, a: &Parts, b: &Parts) -> Option<Vec<Vec<Vec<usize>>>> {
        let within = |x: &Lits, y: &Lits| match (x.cofinite, y.cofinite) {
            (false, false) => x.values.iter().all(|v| y.values.contains(v)),
            (false, true) => x.values.iter().all(|v| !y.values.contains(v)),
            (true, true) => y.values.iter().all(|v| x.values.contains(v)),
            (true, false) => false,
        };
        let same = a.bools & !b.bools == 0
            && within(&a.ints, &b.ints)
            && within(&a.rats, &b.rats)
            && within(&a.floats, &b.floats)
            && within(&a.strings, &b.strings)
            && (!a.structs || b.structs)
            && (a.morphisms.is_leaf() == Some(false) || a.morphisms == b.morphisms)
            && (!a.atoms.cofinite || a.atoms == b.atoms)
            && (!a.tuples.rest || a.tuples == b.tuples);
        if !same {
            return None;
        }
        let mut needs = Vec::new();
        if !a.atoms.cofinite {
            for (name, x) in &a.atoms.names {
                match b.atoms.names.get(name) {
                    None if b.atoms.cofinite => {}
                    None => return None,
                    Some(y) if x.bare && !y.bare => return None,
                    Some(y) => needs.push(vec![vec![self.pair(&x.payload, &y.payload)]]),
                }
            }
        }
        if a.tuples.rest {
            return Some(needs);
        }
        for (len, f) in &a.tuples.lens {
            let g = b.tuples.get(*len);
            if g.is_leaf() == Some(true) {
                continue;
            }
            let (xs, ys) = (f.union_rows()?, g.union_rows()?);
            let mut first: BTreeMap<&Type, Vec<&Row>> = BTreeMap::new();
            for y in &ys {
                if *len > 0 {
                    first.entry(&y[0]).or_default().push(y);
                }
            }
            let whole: BTreeSet<&Row> = ys.iter().collect();
            for x in &xs {
                // A row of `b` equal to `x` holds it, whatever the other rows need.
                if whole.contains(x) {
                    continue;
                }
                let near = (*len > 0).then(|| first.get(&x[0])).flatten();
                let tried = near.map_or_else(|| ys.iter().collect(), |r| r.clone());
                let alts = tried
                    .into_iter()
                    .map(|y| (0..*len).map(|j| self.pair(&x[j], &y[j])).collect())
                    .collect();
                needs.push(alts);
            }
        }
        Some(needs)
    }
}

/// One query's state: the types being decided, assumed empty, each with its depth among them;
/// those decided; the types decided on assumptions still being made, in the order they were
/// decided, each with the depths of those assumptions; and the depths of the assumptions the
/// current decision has used.
#[derive(Default)]
struct Search {
    /// Each type read, by its number here; a type built apart from an equal one is compared
    /// with it in full once per read.
    ids: BTreeMap<Type, usize>,
    types: Vec<Type>,
    /// One answer per type: true, empty, until the rule fails for it.
    answer: Vec<bool>,
    /// The type being decided, which reads the answers of others.
    current: Option<usize>,
    readers: Vec<BTreeSet<usize>>,
    /// Types to decide again, since an answer they read changed.
    again: BTreeSet<usize>,
    /// Types shown inhabited by a checked value; permanent.
    witnessed: BTreeSet<usize>,
    reps: BTreeMap<Type, Option<usize>>,
    /// The values shown, each once, by number.
    shown: Vec<Rep>,
    members: BTreeMap<(usize, Type), bool>,
    /// Each type read as the value type of a morphism.
    value_reads: BTreeSet<usize>,
    /// Types proved empty for good: a morphism with such a value type has no value. All other
    /// value types read as inhabited, since a closure can return itself.
    dead: BTreeSet<usize>,
    /// The types being decided, on the stack.
    deciding: BTreeSet<usize>,
    /// For each type, the types it read.
    reads: Vec<Vec<usize>>,
    /// The types whose value is being built, and how many closures rest on one of them.
    building: BTreeSet<Type>,
    resting: usize,
    /// The representatives kept, in order, so those resting on a failed build are dropped.
    built: Vec<Type>,
    /// Whether a closure was tested against a type that holds some morphisms.
    unsure: bool,
    /// Whether a type was settled in the first walk, after answers that read it as inhabited.
    settled: bool,
    /// Whether kept results are left unread and each place a part counts as inhabited with
    /// nothing shown is noted, for a caller that takes `Refused`.
    strict: bool,
    /// Whether a fork of recursive rows ends the search; set for the decision of a verdict, not
    /// for the search of a value after it.
    refuse_forks: bool,
    /// Why the search stopped, when it met a fork; set only when `refuse_forks`.
    refused: Option<Refusal>,
    /// The first place the search let a part count as inhabited with nothing shown: the cause
    /// of a refusal when no value of the root is built.
    gave_up: Option<Refusal>,
    /// How many times a part counted as inhabited with nothing shown.
    give_ups: usize,
    /// Whether this is the first walk over the types, in which what a type read is on record.
    walking: bool,
    /// Whether values are sought only among the tuple types as written.
    seeding: bool,
    /// Key types with no value shown yet.
    keys: BTreeSet<Type>,
    /// What is known of each list type met, by the rule on pure cycles.
    cycles: BTreeMap<Type, Option<Cycle>>,
}

/// A type of lists: `link` atoms holding (`item`, rest), and one `stop` atom, whose lengths
/// are exactly those equal to `at` modulo `period`.
#[derive(Clone, PartialEq, Eq)]
struct Cycle {
    stop: std::sync::Arc<str>,
    link: std::sync::Arc<str>,
    item: Type,
    period: u64,
    at: u64,
}

/// The prime powers of `n`.
fn prime_powers(mut n: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut r = 2;
    while r * r <= n {
        if n.is_multiple_of(r) {
            let mut q = 1;
            while n.is_multiple_of(r) {
                n /= r;
                q *= r;
            }
            out.push((r, q));
        }
        r += 1;
    }
    if n > 1 {
        out.push((n, n));
    }
    out
}

/// A list type made of pure cycles of one item, as the rule on pure cycles reads it: its
/// lengths are those equal to `at` modulo `period` for each of `all` and for none of `none`,
/// and 0 when `bare`.
struct Meet {
    stop: std::sync::Arc<str>,
    link: std::sync::Arc<str>,
    item: Type,
    bare: bool,
    all: Vec<(u64, u64)>,
    none: Vec<(u64, u64)>,
}

/// What the rule on pure cycles says of a set of lengths.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Lengths {
    /// No length is in it.
    None,
    /// Some length is in it.
    Some,
    /// The negated cycles hold more than all the lengths by their shares, and no split on one
    /// prime decides them: whether they cover the lengths is the covering problem for residues,
    /// which is NP-hard.
    Refused,
}

/// The lengths equal to `at` modulo `period` for each of `all`, and for none of `none`. The
/// rule by shares (`shares`) decides most; when the negated classes hold more than all the
/// lengths by their shares, the lengths are split on one prime `r` of their periods into the
/// classes modulo `q0 * r`, `q0` the power of `r` the classes of `all` fix, and each class is
/// decided by shares: some length is left when one class has one, and none when no class has.
/// Classes no negated class tells apart are one class. The primes are tried in order, each
/// split on its own, so the work is polynomial in the classes; what no single split decides is
/// refused. The lengths of lists of integers whose length is not 0 modulo 2 or 3, nor 1 or 5
/// modulo 6, are none: the even ones are 0 modulo 2, and the odd ones are 0, 1 or 2 modulo 3.
fn residues_meet(all: &[(u64, u64)], none: &[(u64, u64)]) -> Lengths {
    let first = shares(all, none);
    if first != Lengths::Refused {
        return first;
    }
    let primes: BTreeSet<u64> = none
        .iter()
        .flat_map(|&(period, _)| prime_powers(period).into_iter().map(|(r, _)| r))
        .collect();
    let mut split = all.to_vec();
    for r in primes {
        // The power of `r` the classes of `all` fix, and the residue there.
        let (q0, at0) = all
            .iter()
            .filter_map(|&(period, at)| {
                let q = prime_powers(period).into_iter().find(|&(p, _)| p == r)?.1;
                Some((q, at % q))
            })
            .max()
            .unwrap_or((1, 0));
        let Some(q) = q0.checked_mul(r) else {
            continue;
        };
        // The classes modulo `q` some negated class meets alone, and one other when they are
        // not all of them.
        let mut tried: BTreeSet<u64> = none
            .iter()
            .filter(|&&(period, at)| {
                let power = prime_powers(period)
                    .into_iter()
                    .find(|&(p, _)| p == r)
                    .map_or(1, |(_, power)| power);
                power >= q && at % q0 == at0
            })
            .map(|&(_, at)| at % q)
            .collect();
        if (tried.len() as u64) < r {
            let free = (0..r)
                .map(|i| at0 + i * q0)
                .find(|b| !tried.contains(b))
                .expect("a class is not tried");
            tried.insert(free);
        }
        let mut all_none = true;
        for b in tried {
            split.push((q, b));
            let l = shares(&split, none);
            split.pop();
            match l {
                Lengths::Some => return Lengths::Some,
                Lengths::None => {}
                Lengths::Refused => all_none = false,
            }
        }
        if all_none {
            return Lengths::None;
        }
    }
    Lengths::Refused
}

/// A length in the lengths of `all` and in none of `none`, sought by the method of conditional
/// expectations: the residue modulo each prime power of the periods is chosen in turn, the one
/// for which the negated classes expected to hold the length are fewest, the residues not yet
/// chosen taken as uniform among those `all` allows. When the shares sum to less than one a
/// length is always found; otherwise one may be missed, and the caller checks it. The work is
/// the residues tried times the classes times the primes, and the length is below the lcm of
/// the periods; `None` when that lcm is above `u64`.
fn greedy_length(all: &[(u64, u64)], none: &[(u64, u64)]) -> Option<u64> {
    let power = |period: u64, r: u64| {
        prime_powers(period)
            .into_iter()
            .find(|&(p, _)| p == r)
            .map_or(1, |(_, q)| q)
    };
    // For each prime: the largest power in the periods, and the power and residue `all` fix.
    let mut primes: BTreeMap<u64, (u64, u64, u64)> = BTreeMap::new();
    for &(period, _) in all.iter().chain(none) {
        for (r, q) in prime_powers(period) {
            let e = primes.entry(r).or_insert((1, 1, 0));
            e.0 = e.0.max(q);
        }
    }
    for &(period, at) in all {
        for (r, q) in prime_powers(period) {
            let e = primes.get_mut(&r).expect("each prime is listed");
            if q > e.1 {
                (e.1, e.2) = (q, at % q);
            }
        }
    }
    // The chance that the class `(period, at)` holds the residue on the prime `r`.
    let chance = |(period, at): (u64, u64), r: u64, chosen: Option<u64>| {
        let (_, q0, a0) = primes[&r];
        let q = power(period, r);
        match chosen {
            Some(d) => f64::from(u8::from(at % q == d % q)),
            None if q <= q0 => f64::from(u8::from(at % q == a0 % q)),
            None if at % q0 == a0 => q0 as f64 / q as f64,
            None => 0.0,
        }
    };
    let mut chosen: BTreeMap<u64, u64> = BTreeMap::new();
    for (&r, &(top, q0, a0)) in &primes {
        let expected = |d: u64| -> f64 {
            none.iter()
                .map(|&c| {
                    primes
                        .keys()
                        .map(|&p| {
                            chance(
                                c,
                                p,
                                if p == r {
                                    Some(d)
                                } else {
                                    chosen.get(&p).copied()
                                },
                            )
                        })
                        .product::<f64>()
                })
                .sum()
        };
        // Complexity tradeoff: every residue modulo the largest power of `r` is tried, each
        // against every negated class on every prime. A period is the number of definitions on
        // its cycle, so the power is at most the size of the type and the work is polynomial in
        // it, up to its cube; trying only the residues the negated classes name, and one other,
        // would drop a factor. This runs only when the rule refuses.
        let d = (0..top / q0)
            .map(|i| a0 + i * q0)
            .min_by(|&a, &b| expected(a).total_cmp(&expected(b)))
            .expect("a residue is tried");
        chosen.insert(r, d);
    }
    // The length below the lcm with the chosen residues, by the Chinese remainder theorem.
    let (mut n, mut m) = (0i128, 1i128);
    for (&r, &d) in &chosen {
        let q = i128::from(primes[&r].0);
        let inv = i128::from(inverse((m % q) as u64, q as u64).unwrap_or(0));
        n += m * ((i128::from(d) - n).rem_euclid(q) * inv % q);
        m = m.checked_mul(q)?;
    }
    u64::try_from(if n == 0 { m } else { n }).ok()
}

/// The rule by shares, by prime powers, so the lcm of the periods, exponential in them, is
/// never computed. Each negated class meeting the lengths of `all` holds a known share of them:
/// when one holds them all there are none; when the shares sum to less than one some remain;
/// when they sum to one, none remain if the classes are pairwise disjoint, and some do if two
/// meet, since what two classes share is a class of its own share, counted twice.
fn shares(all: &[(u64, u64)], none: &[(u64, u64)]) -> Lengths {
    let mut best: BTreeMap<u64, (u64, u64)> = BTreeMap::new();
    for &(period, at) in all {
        for (r, q) in prime_powers(period) {
            let (q0, at0) = *best.entry(r).or_insert((q, at % q));
            let m = q.min(q0);
            if at % m != at0 % m {
                return Lengths::None;
            }
            if q > q0 {
                best.insert(r, (q, at % q));
            }
        }
    }
    let (mut sum, mut denom) = (BigUint::ZERO, BigUint::from(1u32));
    let mut meeting = Vec::new();
    for &(period, at) in none {
        let mut share = 1u64;
        let mut meets = true;
        for (r, q) in prime_powers(period) {
            let (q0, at0) = best.get(&r).copied().unwrap_or((1, 0));
            meets &= at0 % q.min(q0) == at % q.min(q0);
            share *= q / q.min(q0);
        }
        if !meets {
            continue;
        }
        if share == 1 {
            return Lengths::None;
        }
        // sum / denom + 1 / share
        sum = sum * share + &denom;
        denom *= share;
        meeting.push((period, at));
    }
    if sum < denom {
        return Lengths::Some;
    }
    if sum > denom {
        return Lengths::Refused;
    }
    let disjoint = meeting.iter().enumerate().all(|(i, a)| {
        meeting[..i].iter().all(|b| {
            let g = gcd(a.0, b.0);
            a.1 % g != b.1 % g
        })
    });
    if disjoint {
        Lengths::None
    } else {
        Lengths::Some
    }
}
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The inverse of `a` modulo `m`, by the extended Euclidean algorithm: `None` when `a` and `m`
/// share a factor. Modulo 1 it is 0.
fn inverse(a: u64, m: u64) -> Option<u64> {
    let (mut r0, mut r1) = (i128::from(m), i128::from(a % m));
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    match r0 {
        1 => u64::try_from(s0.rem_euclid(i128::from(m))).ok(),
        _ if m == 1 => Some(0),
        _ => None,
    }
}

/// The lengths in all the classes `(period, at)` of `all`, as the least one and their period,
/// by the Chinese remainder theorem: `None` when no length is in all of them, or when their
/// period is above `u64`.
fn crt(all: &[(u64, u64)]) -> Option<(u64, u64)> {
    let (mut n, mut l) = (0u64, 1u64);
    for &(p, at) in all {
        let g = gcd(l, p);
        let gap = i128::from(at % p) - i128::from(n % p);
        if gap.rem_euclid(i128::from(g)) != 0 {
            return None;
        }
        let s = p / g;
        let k = (gap / i128::from(g)).rem_euclid(i128::from(s)) as u128
            * u128::from(inverse(l / g % s, s)?)
            % u128::from(s);
        l = l.checked_mul(s)?;
        n = u64::try_from(u128::from(n) + u128::from(l / s) * k).ok()?;
    }
    Some((n, l))
}

/// The least length from 1 in all the classes of `all` and in none of `none`, and not above
/// `bound`. The lengths of `all` are `n0 + j * l` by `crt`; each class of `none` holds those
/// whose step `j` is in one class modulo `p / gcd(l, p)`, found by the extended Euclidean
/// algorithm. The steps are sieved in windows that double, so the work is the steps passed
/// times one plus the sum of `1 / (p / gcd(l, p))` over `none`, plus the classes times the
/// windows: no length below the result is tested class by class. `None` when no length is
/// found up to `bound`, or above `u64`; with no bound the caller knows a length exists.
fn least_length(all: &[(u64, u64)], none: &[(u64, u64)], bound: Option<u64>) -> Option<u64> {
    let (n0, l) = crt(all)?;
    // For each negated class meeting the lengths: the first step it holds, and its period.
    let steps: Vec<(u64, u64)> = none
        .iter()
        .filter_map(|&(p, at)| {
            let g = gcd(l, p);
            let gap = i128::from(at % p) - i128::from(n0 % p);
            if gap.rem_euclid(i128::from(g)) != 0 {
                return None;
            }
            let s = p / g;
            let j0 = (gap / i128::from(g)).rem_euclid(i128::from(s)) as u128
                * u128::from(inverse(l / g % s, s).expect("l / g and s are coprime"))
                % u128::from(s);
            Some((j0 as u64, s))
        })
        .collect();
    let first = u64::from(n0 == 0);
    let (mut lo, mut hi) = (first, first + 1);
    loop {
        let start = n0.checked_add(lo.checked_mul(l)?)?;
        if bound.is_some_and(|b| start > b) {
            return None;
        }
        let mut held = vec![false; (hi - lo) as usize];
        for &(j0, s) in &steps {
            // The first step from `lo` equal to `j0` modulo `s`.
            let mut j = lo + (j0 + s - lo % s) % s;
            while j < hi {
                held[(j - lo) as usize] = true;
                j += s;
            }
        }
        if let Some(i) = held.iter().position(|&h| !h) {
            let n = n0.checked_add((lo + i as u64).checked_mul(l)?)?;
            return bound.is_none_or(|b| n <= b).then_some(n);
        }
        (lo, hi) = (hi, hi.checked_mul(2)?);
    }
}

/// One distinct type among the components a column's tuple types have, and those tuple types.
/// Whether a tuple type misses or holds a component of the box depends only on its type there,
/// so the cell is tested once for all of them, and all are open on the component or none.
struct Cell {
    ty: Type,
    rows: Vec<usize>,
    open: bool,
}

/// A box of tuples, one type per component, and where each tuple type of a part stands on it
/// component by component: missing it, holding it, or open on it. A tuple type that misses a
/// component of the box, or holds it, still does when the box shrinks, so a component that
/// changed is tested again only against the cells open on it that have a tuple type still in
/// the part, and only when they are next read. Each change is logged, so a piece of the box is
/// tried and the box restored after.
struct Region {
    r: Vec<Type>,
    atoms: Vec<Row>,
    index: BTreeMap<Row, usize>,
    /// For each component, the distinct types the tuple types have there.
    cells: Vec<Vec<Cell>>,
    /// The cell of tuple type `k` in component `j`, at `k * r.len() + j`.
    cell_of: Vec<usize>,
    /// For each tuple type, how many components it misses.
    missed: Vec<usize>,
    /// For each tuple type, how many components it does not hold, and the sum of their
    /// positions, which is the position when there is one.
    loose: Vec<(usize, usize)>,
    /// For each component, how many tuple types are open on it.
    opens: Vec<usize>,
    /// For each component, whether it changed since it was last tested.
    changed: Vec<bool>,
    log: Vec<Change>,
}

enum Change {
    /// A component of the box, its type before, and whether it had changed before.
    Component(usize, Type, bool),
    /// A component tested again.
    Tested(usize),
    /// A cell of a component no longer open on it, and whether it misses it.
    Closed(usize, usize, bool),
}

impl Region {
    /// Whether two of the rows `open` differ in component `j`, each with a recursive type there.
    fn forks(&self, open: &[usize], j: usize) -> bool {
        let mut cells = open
            .iter()
            .map(|&k| &self.atoms[k][j])
            .filter(|c| c.is_recursive());
        cells.next().is_some_and(|c| cells.any(|d| d != c))
    }

    /// Undoes the changes logged after the first `mark`.
    fn restore(&mut self, mark: usize) {
        while self.log.len() > mark {
            match self.log.pop().expect("a change is logged") {
                Change::Component(j, t, changed) => {
                    self.r[j] = t;
                    self.changed[j] = changed;
                }
                Change::Tested(j) => self.changed[j] = true,
                Change::Closed(j, c, missed) => {
                    let cell = &mut self.cells[j][c];
                    cell.open = true;
                    self.opens[j] += cell.rows.len();
                    for &k in &cell.rows {
                        if missed {
                            self.missed[k] -= 1;
                        } else {
                            self.loose[k].0 += 1;
                            self.loose[k].1 += j;
                        }
                    }
                }
            }
        }
    }

    /// Sets component `j` of the box to `t`, which is within it.
    fn shrink(&mut self, j: usize, t: Type) {
        let old = std::mem::replace(&mut self.r[j], t);
        self.log.push(Change::Component(j, old, self.changed[j]));
        self.changed[j] = true;
    }

    /// The cell of tuple type `k` in component `j`.
    fn cell(&self, k: usize, j: usize) -> usize {
        self.cell_of[k * self.r.len() + j]
    }

    /// Whether tuple type `k` is open on component `j`.
    fn is_open(&self, k: usize, j: usize) -> bool {
        self.cells[j][self.cell(k, j)].open
    }

    /// Closes cell `c` of component `j`, open on it, for each of its tuple types: it misses the
    /// component when `missed`, and holds it otherwise.
    fn close(&mut self, j: usize, c: usize, missed: bool) {
        let cell = &mut self.cells[j][c];
        cell.open = false;
        self.opens[j] -= cell.rows.len();
        for &k in &cell.rows {
            if missed {
                self.missed[k] += 1;
            } else {
                self.loose[k].0 -= 1;
                self.loose[k].1 -= j;
            }
        }
        self.log.push(Change::Closed(j, c, missed));
    }

    /// The open cells of component `j` that have one of the tuple types `ks`, in order.
    fn open_cells(&self, j: usize, ks: &[usize]) -> BTreeSet<usize> {
        ks.iter()
            .map(|&k| self.cell(k, j))
            .filter(|&c| self.cells[j][c].open)
            .collect()
    }

    /// Where the tuple type `a` stands on the box, as last tested: `Some(false)` if it misses it, `Some(true)`
    /// if it holds it, `None` if it is open on it.
    fn stand(&self, a: &Row) -> Option<bool> {
        let k = self.index[a];
        if self.missed[k] > 0 {
            Some(false)
        } else if self.loose[k].0 == 0 {
            Some(true)
        } else {
            None
        }
    }
}

/// A value known to be in a type, held as the types of its parts, each with a representative
/// of its own.
#[derive(Clone)]
enum Rep {
    Value(Value),
    Tuple(Vec<usize>),
    /// An atom of this name, whose payload is this tuple.
    Atom(std::sync::Arc<str>, usize),
    /// A closure; it may be recursive. Whether it is in a type is known only when that type
    /// holds all morphisms or none.
    Closure,
    Struct,
}

impl Search {
    /// Decides `root`: phases, in each of which an answer only goes from empty to inhabited;
    /// at the end of a phase each inhabited answer is tried for a checked value, and if a new one
    /// is found the answers without one start again from empty, so a wrong "inhabited" read by
    /// another decision is undone. The last phase gives the answer.
    fn solve(&mut self, root: &Type) -> bool {
        // A value built from the tuple types as written answers at once, and no box is split.
        // Answers read on the way are unfinished, so none is kept. A type with no atoms has no
        // list to walk, and a row tested against every row would cost their square.
        if !root.p().atoms.names.is_empty() {
            self.seeding = true;
            let seed = self.rep(root).is_some();
            self.seeding = false;
            if seed {
                self.types.clear();
                self.answer.clear();
                return false;
            }
            self.reps.retain(|_, r| r.is_some());
        }
        self.walking = true;
        let b = self.empty(root);
        self.walking = false;
        let Some(&r) = self.ids.get(root) else {
            return b;
        };
        loop {
            self.drain();
            let open: Vec<usize> = (0..self.types.len())
                .filter(|&t| !self.answer[t] && !self.witnessed.contains(&t))
                .collect();
            self.reps.retain(|_, r| r.is_some());
            let mut new = false;
            for &t in &open {
                let x = self.types[t].clone();
                if self.rep(&x).is_some() {
                    self.witnessed.insert(t);
                    new = true;
                }
            }
            for k in std::mem::take(&mut self.keys) {
                if self.rep(&k).is_some() {
                    new = true;
                } else {
                    self.keys.insert(k);
                }
            }
            if !self.again.is_empty() {
                continue;
            }
            // Value types still empty with every morphism value read as inhabited are empty:
            // read them so, and start again.
            let fresh: Vec<usize> = (self.value_reads.iter().copied())
                .filter(|&v| self.answer[v] && !self.dead.contains(&v))
                .collect();
            if !fresh.is_empty() || std::mem::take(&mut self.settled) {
                self.dead.extend(fresh);
                for t in 0..self.types.len() {
                    if !self.witnessed.contains(&t) && !self.dead.contains(&t) {
                        self.answer[t] = true;
                        self.again.insert(t);
                    }
                }
                self.reps.retain(|_, r| r.is_some());
                continue;
            }
            if !new {
                return self.answer[r];
            }
            for t in open {
                if !self.witnessed.contains(&t) {
                    self.answer[t] = true;
                    self.again.insert(t);
                }
            }
            if self.again.is_empty() {
                return self.answer[r];
            }
        }
    }

    /// Decides again, in rounds, each type an answer it read has changed under.
    fn drain(&mut self) {
        while !self.again.is_empty() {
            for t in std::mem::take(&mut self.again) {
                if self.answer[t] {
                    self.decide(t);
                }
            }
        }
    }

    /// Notes the first place a part counted as inhabited with nothing shown.
    fn give_up(&mut self, r: Refusal) {
        self.give_ups += 1;
        if self.strict {
            self.gave_up.get_or_insert(r);
        }
    }

    fn decide(&mut self, t: usize) -> bool {
        if self.refused.is_some() {
            return true;
        }
        let outer = self.current.replace(t);
        let ty = self.types[t].clone();
        let b = match self.pure_cycles(&ty) {
            Some(Lengths::None) => true,
            Some(Lengths::Some) => {
                self.witnessed.insert(t);
                false
            }
            Some(Lengths::Refused) => {
                self.give_up(Refusal::Residues);
                false
            }
            None => self.parts(ty.p()),
        };
        self.current = outer;
        if !b {
            self.answer[t] = false;
            self.again.extend(self.readers[t].iter().copied());
        }
        b
    }

    fn empty(&mut self, t: &Type) -> bool {
        // A member of a recursive group is answered by the group's decider (module `rec`).
        if let Some(b) = t.judged() {
            return b;
        }
        // A scalar in the type is a checked value, read off before the type is compared with
        // those met.
        let p = t.p();
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        if p.bools != 0 || lits.iter().any(|l| l.cofinite || !l.values.is_empty()) {
            return false;
        }
        if let Some(&i) = self.ids.get(t) {
            if let Some(c) = self.current
                && self.readers[i].insert(c)
            {
                self.reads[c].push(i);
            }
            return self.answer[i];
        }
        if !self.strict
            && let Some(b) = MEMO.with(|m| m.borrow().get(t).copied())
        {
            return b;
        }
        let i = self.types.len();
        self.ids.insert(t.clone(), i);
        self.types.push(t.clone());
        self.answer.push(true);
        self.readers.push(self.current.into_iter().collect());
        self.reads.push(Vec::new());
        if let Some(c) = self.current {
            self.reads[c].push(i);
        }
        self.deciding.insert(i);
        let b = self.decide(i);
        self.deciding.remove(&i);
        b
    }

    /// Takes as dead the empty types `v` rests on, unless one rests on a type still being
    /// decided: an empty type read is what a proof rests on, and an inhabited one is not.
    fn settle(&mut self, v: usize) {
        let (mut seen, mut stack) = (BTreeSet::from([v]), vec![v]);
        while let Some(x) = stack.pop() {
            for &y in &self.reads[x] {
                if self.deciding.contains(&y) {
                    return;
                }
                if self.answer[y] && !self.dead.contains(&y) && seen.insert(y) {
                    stack.push(y);
                }
            }
        }
        self.dead.extend(seen);
        self.settled = true;
    }

    fn parts(&mut self, p: &Parts) -> bool {
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        p.bools == 0
            && lits.iter().all(|l| !l.cofinite && l.values.is_empty())
            && !p.atoms.cofinite
            && p.atoms
                .names
                .values()
                .all(|a| !a.bare && self.empty(&a.payload))
            && !p.structs
            && !p.tuples.rest
            && p.tuples.lens.iter().all(|(len, b)| {
                // A union of rows is empty when each row has an empty column, and only then.
                if let Some(rows) = b.union_rows() {
                    return rows.iter().all(|a| a.iter().any(|c| self.empty(c)));
                }
                let mut g = self.region(vec![Type::top(); *len], b);
                self.tuples(&mut g, b.clone(), true)
            })
            && match p.morphisms.union_rows() {
                // A union of morphism types is empty when each of them admits nothing.
                Some(rows) => rows.iter().all(|a| self.no_morphism(a)),
                None => self.morphisms(
                    Morphism {
                        guarantee: Type::empty(),
                        permission: Type::top(),
                        value: Type::top(),
                    },
                    p.morphisms.clone(),
                    true,
                ),
            }
    }

    /// The region of the part `f` on the box `r`, each distinct type of each component tested
    /// once.
    fn region(&mut self, r: Vec<Type>, f: &Part<Row>) -> Region {
        let atoms = f.distinct_atoms();
        let n = r.len();
        let mut g = Region {
            cells: (0..n).map(|_| Vec::new()).collect(),
            cell_of: vec![0; atoms.len() * n],
            opens: vec![0; n],
            changed: vec![false; n],
            missed: vec![0; atoms.len()],
            loose: vec![(0, 0); atoms.len()],
            index: BTreeMap::new(),
            atoms: Vec::new(),
            log: Vec::new(),
            r,
        };
        for j in 0..n {
            let mut found: BTreeMap<&Type, usize> = BTreeMap::new();
            for (k, a) in atoms.iter().enumerate() {
                let cells = &mut g.cells[j];
                let c = *found.entry(&a[j]).or_insert_with(|| {
                    cells.push(Cell {
                        ty: a[j].clone(),
                        rows: Vec::new(),
                        open: false,
                    });
                    cells.len() - 1
                });
                cells[c].rows.push(k);
                g.cell_of[k * n + j] = c;
            }
            for c in 0..g.cells[j].len() {
                let cell = &mut g.cells[j][c];
                let missed = self.settles(&g.r[j], &cell.ty, true);
                if !missed && self.settles(&g.r[j], &cell.ty, false) {
                    continue;
                }
                cell.open = !missed;
                if cell.open {
                    g.opens[j] += cell.rows.len();
                }
                for &k in &cell.rows {
                    g.missed[k] += usize::from(missed);
                    g.loose[k].0 += 1;
                    g.loose[k].1 += j;
                }
            }
        }
        for (k, a) in atoms.iter().enumerate() {
            g.index.insert(a.clone(), k);
        }
        g.atoms = atoms;
        g
    }

    /// Whether `x & y`, or `x - y` when `both` is false, is empty. Types of scalars alone are
    /// compared directly, so no type is built for them.
    fn settles(&mut self, x: &Type, y: &Type, both: bool) -> bool {
        match x.scalar_cell(y, both) {
            Some(b) => b,
            None if both => self.empty(&(x & y)),
            None => self.empty(&(x - y)),
        }
    }

    /// Tests each changed component of the box against its open cells that have a tuple type
    /// not yet known to miss the box, and closes those it settles. A tuple type that misses a
    /// component is out of the part, so whether it holds the others is not tested: every
    /// changed component is tested for cells that miss it before any is tested for cells that
    /// hold it, and a cell only such tuple types have is not tested. Tuple types the part no
    /// longer has are not looked up: that costs the size of the part at each call, more than
    /// the tests it saves.
    fn retest(&mut self, g: &mut Region) {
        let changed: Vec<usize> = (0..g.r.len()).filter(|&j| g.changed[j]).collect();
        if changed.is_empty() {
            return;
        }
        for &j in &changed {
            g.changed[j] = false;
            g.log.push(Change::Tested(j));
        }
        for missed in [true, false] {
            for &j in &changed {
                for c in 0..g.cells[j].len() {
                    let cell = &g.cells[j][c];
                    if !cell.open || !cell.rows.iter().any(|&k| g.missed[k] == 0) {
                        continue;
                    }
                    let settled = self.settles(&g.r[j], &cell.ty, missed);
                    if settled {
                        g.close(j, c, missed);
                    }
                }
            }
        }
    }

    /// Narrows the box and the part `f` to what `f` forces on it: a tuple type in every value
    /// of `f` meets the box, and a tuple type in none is taken out of the box when it holds the
    /// box in every component but one. True when `f` is proved empty on the box.
    fn narrow_tuples(&mut self, g: &mut Region, f: &mut Part<Row>) -> bool {
        loop {
            if g.r.iter().any(|t| self.empty(t)) {
                return true;
            }
            self.retest(g);
            *f = f.restrict(&|a| g.stand(a)).settle();
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let (taken, refused) = f.forced();
            // The components changed in this pass.
            let mut shrunk = BTreeSet::new();
            // A component narrowed to a tuple type's own holds it, and one that takes a tuple
            // type out misses it, so its cell there is closed without a test.
            for a in &taken {
                let k = g.index[a];
                for j in 0..g.r.len() {
                    if g.is_open(k, j) {
                        g.shrink(j, &g.r[j] & &a[j]);
                        g.close(j, g.cell(k, j), false);
                        shrunk.insert(j);
                    }
                }
            }
            // The changed components are tested again cell by cell, so where a refused tuple
            // type stands is read off the table, not tested for each tuple type.
            if !shrunk.is_empty() {
                self.retest(g);
            }
            for a in &refused {
                let k = g.index[a];
                let (loose, at) = g.loose[k];
                if g.missed[k] == 0 && loose == 1 {
                    g.shrink(at, &g.r[at] - &a[at]);
                    if g.is_open(k, at) {
                        g.close(at, g.cell(k, at), true);
                    }
                    shrunk.insert(at);
                }
            }
            if shrunk.is_empty() {
                return false;
            }
        }
    }

    /// Whether no tuple in the box is in `f`: `f` is narrowed by what it forces; then, when every
    /// open tuple type is open on a component whose cells fall into classes that share no value
    /// (joined by literal, atom name and tuple length), the box is split by class: the values in
    /// no class first, then the classes in halves, each half deciding `f` with the tuple types
    /// of the other half taken as false, so `k` classes cost `O(k log k)` restrictions of `f`
    /// and a value is sought in each piece the same way; else a component on which every open
    /// tuple type is open, and whose pieces cut by them are
    /// pairwise equal or disjoint, is split into them; else each such piece on which narrowing
    /// alone proves `f` empty is taken out; else, once on each branch, when `f` holds nothing
    /// outside the open tuple types, each of them is decided on its own. What is left counts as
    /// inhabited. A split into disjoint pieces sends each open tuple type to one piece, and a
    /// component split is never split again below, so the nodes are polynomial in the tuple
    /// types. The components tried for a split are those on which the open tuple type open on
    /// fewest is open, so a box most of whose components the tuple types hold is not searched.
    /// Each piece is tried on the box and the box restored after.
    fn tuples(&mut self, g: &mut Region, mut f: Part<Row>, may_cover: bool) -> bool {
        loop {
            if self.narrow_tuples(g, &mut f) {
                return true;
            }
            if f.is_leaf().is_some() {
                return false;
            }
            let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
            if self.refuse_forks && !self.seeding && (0..g.r.len()).any(|j| g.forks(&open, j)) {
                self.refused = Some(Refusal::Fork);
                return true;
            }
            if let Some((j, classes)) = classes(g, &open) {
                return self.split_classes(g, &f, j, &classes, may_cover);
            }
            let fewest = *open
                .iter()
                .min_by_key(|&&k| g.loose[k].0)
                .expect("an open part has a tuple type");
            for j in 0..g.r.len() {
                if !g.is_open(fewest, j)
                    || g.opens[j] < open.len()
                    || open.iter().any(|&k| !g.is_open(k, j))
                {
                    continue;
                }
                let mut cells = BTreeSet::new();
                let mut union = Type::empty();
                let ok = g.open_cells(j, &open).into_iter().all(|c| {
                    let c = &g.cells[j][c].ty & &g.r[j];
                    if cells.contains(&c) {
                        return true;
                    }
                    if !self.empty(&(&c & &union)) {
                        return false;
                    }
                    union = &union | &c;
                    cells.insert(c);
                    true
                });
                if !ok {
                    continue;
                }
                let rest = &g.r[j] - &union;
                if !self.empty(&rest) {
                    cells.insert(rest);
                }
                return cells.into_iter().all(|c| {
                    let mark = g.log.len();
                    g.shrink(j, c);
                    let b = self.tuples(g, f.clone(), may_cover);
                    g.restore(mark);
                    b
                });
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                return open.iter().all(|&k| {
                    let mark = g.log.len();
                    for j in 0..g.r.len() {
                        if g.is_open(k, j) {
                            let t = &g.r[j] & &g.atoms[k][j];
                            g.shrink(j, t);
                            g.close(j, g.cell(k, j), false);
                        }
                    }
                    let b = self.tuples(g, f.clone(), false);
                    g.restore(mark);
                    b
                });
            }
            let mut narrowed = false;
            for j in 0..g.r.len() {
                let mut tried = BTreeSet::new();
                // A cell closed on the component misses or holds it, so its pieces are the
                // component and nothing, and narrow nothing.
                for cell in g.open_cells(j, &open) {
                    let a = &g.cells[j][cell].ty;
                    for c in [a & &g.r[j], &g.r[j] - a] {
                        if tried.contains(&c) || self.empty(&c) || self.empty(&(&g.r[j] - &c)) {
                            continue;
                        }
                        tried.insert(c.clone());
                        let mark = g.log.len();
                        g.shrink(j, c.clone());
                        let hit = self.narrow_tuples(g, &mut f.clone());
                        g.restore(mark);
                        if hit {
                            let t = &g.r[j] - &c;
                            g.shrink(j, t);
                            narrowed = true;
                        }
                    }
                }
            }
            if narrowed {
                continue;
            }
            self.give_up(Refusal::TupleSplit);
            return false;
        }
    }

    /// Whether no tuple in the box of `g` is in `f`, the box split on component `j` into the
    /// piece of each class, the meet of the component with its cells, and the rest, which no
    /// class's cells meet. On the piece of a class, a tuple type with a cell of another class
    /// misses the box, and on the rest every tuple type of a class does, so they are taken out
    /// of `f` before the piece is decided on a box of its own. The classes are halved at each
    /// step and each half takes the other's tuple types out, so each tuple type stays in the
    /// part of O(log k) of the k pieces, and the part is restricted O(log k) times over.
    fn split_classes(
        &mut self,
        g: &Region,
        f: &Part<Row>,
        j: usize,
        classes: &[Class],
        may_cover: bool,
    ) -> bool {
        let class_of: BTreeMap<usize, usize> = (classes.iter().enumerate())
            .flat_map(|(i, (_, ks))| ks.iter().map(move |&k| (k, i)))
            .collect();
        let at = |a: &Row| class_of.get(&g.index[a]).copied();
        let met = classes.iter().fold(Type::empty(), |u, (c, _)| &u | c);
        let rest = &g.r[j] - &met;
        if !self.empty(&rest) {
            let f = f.restrict(&|a| at(a).map(|_| false));
            let mut r = g.r.clone();
            r[j] = rest;
            if !self.piece(r, f, may_cover) {
                return false;
            }
        }
        self.halves(&at, &g.r, f, j, classes, 0, may_cover)
    }

    /// [`Search::split_classes`] on the classes `classes`, which start at index `from`; `f`
    /// holds no tuple type of a class outside them.
    #[allow(clippy::too_many_arguments)]
    fn halves(
        &mut self,
        at: &impl Fn(&Row) -> Option<usize>,
        r: &[Type],
        f: &Part<Row>,
        j: usize,
        classes: &[Class],
        from: usize,
        may_cover: bool,
    ) -> bool {
        if let [(cells, _)] = classes {
            let mut r = r.to_vec();
            r[j] = &r[j] & cells;
            return self.piece(r, f.clone(), may_cover);
        }
        let m = classes.len() / 2;
        let (lo, hi) = (from..from + m, from + m..from + classes.len());
        [(lo.clone(), hi.clone()), (hi, lo)]
            .into_iter()
            .all(|(this, other)| {
                let f = f.restrict(&|a| at(a).filter(|i| other.contains(i)).map(|_| false));
                let these = &classes[this.start - from..this.end - from];
                f.is_leaf() == Some(false)
                    || self.halves(at, r, &f, j, these, this.start, may_cover)
            })
    }

    /// Whether no tuple in the box `r` is in `f`, decided on a region of its own.
    fn piece(&mut self, r: Vec<Type>, f: Part<Row>, may_cover: bool) -> bool {
        if f.is_leaf() == Some(false) {
            return true;
        }
        let mut h = self.region(r, &f);
        self.tuples(&mut h, f, may_cover)
    }

    /// Whether `m` admits no morphism: a key is promised and not permitted, or promised and no
    /// value can be its. A key is promised only when a value is shown in the type: a type not
    /// proved empty may still be empty, and then the empty morphism is admitted.
    fn no_morphism(&mut self, m: &Morphism) -> bool {
        self.shown_key(&(&m.guarantee - &m.permission))
            || (self.shown_key(&m.guarantee) && self.no_value(&m.value))
    }

    /// Whether a value is shown in `k`. A type with none yet is tried again after each
    /// phase, since a value found later changes what was read.
    fn shown_key(&mut self, k: &Type) -> bool {
        let b = self.rep(k).is_some();
        if !b {
            self.keys.insert(k.clone());
        }
        b
    }

    /// Whether no value is in `v`, the value type of a morphism. A value is finite but a closure
    /// may return itself, so a cycle through a morphism proves nothing: a value type counts as
    /// inhabited here until it is empty with all such reads inhabited. That is the greatest
    /// fixed point on these reads over the least on the others. A type whose decision read
    /// nothing still being decided is settled at once, so a nest of morphisms takes one round.
    fn no_value(&mut self, v: &Type) -> bool {
        let b = self.empty(v);
        let Some(&i) = self.ids.get(v) else {
            return b;
        };
        if b && self.walking && !self.deciding.contains(&i) {
            self.walking = false;
            self.drain();
            self.walking = true;
            if self.answer[i] {
                self.settle(i);
            }
        }
        self.value_reads.insert(i);
        self.dead.contains(&i)
    }

    /// The list type `t`, if it is a pure cycle of link atoms with one stop.
    fn cycle(&mut self, t: &Type) -> Option<Cycle> {
        if let Some(c) = self.cycles.get(t) {
            return c.clone();
        }
        self.cycles.insert(t.clone(), None);
        let c = self.find_cycle(t);
        self.cycles.insert(t.clone(), c.clone());
        c
    }

    /// The walk from `t` is fixed, so each type on a pure cycle walks the same cycle: a type
    /// on the walk that is on none puts `t` on none. The types that lead to a type with no
    /// step, or into a cycle they are not on, are on none, and are recorded so; a chain of
    /// lists is then walked once in all, not once from each of its types.
    fn find_cycle(&mut self, t: &Type) -> Option<Cycle> {
        let (mut seen, mut path) = (BTreeMap::new(), Vec::new());
        let (mut x, mut steps) = (t.clone(), 0);
        let (mut stop, mut link, mut item, mut at) = (None, None, None, None);
        loop {
            if x != *t && matches!(self.cycles.get(&x), Some(None)) {
                return None;
            }
            if let Some(&i) = seen.get(&x) {
                for y in path.drain(..i) {
                    self.cycles.insert(y, None);
                }
                return None;
            }
            seen.insert(x.clone(), path.len());
            path.push(x.clone());
            let Some((s, l, e, next)) = list_step(&x) else {
                for y in path {
                    self.cycles.insert(y, None);
                }
                return None;
            };
            if let Some(s) = s {
                if at.is_some() {
                    return None;
                }
                at = Some(steps);
                stop = Some(s);
            }
            if *link.get_or_insert_with(|| l.clone()) != l
                || *item.get_or_insert_with(|| e.clone()) != e
            {
                return None;
            }
            x = next;
            steps += 1;
            if x == *t {
                break;
            }
        }
        Some(Cycle {
            stop: stop?,
            link: link?,
            item: item?,
            period: steps,
            at: at?,
        })
    }

    /// The meet of pure cycles that `t` is, when `t` is a stop atom or not, and a link atom
    /// whose rest is the meet of pure cycles less at most one, all of one item.
    fn cycle_meet(&mut self, t: &Type) -> Option<Meet> {
        let p = t.p();
        if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(p) {
            return None;
        }
        if p.atoms.names.len() > 2 || p.atoms.cofinite {
            return None;
        }
        let (mut bare, mut link) = (None, None);
        for (name, a) in &p.atoms.names {
            match (a.bare, a.payload == Type::empty()) {
                (true, true) => bare = Some(name.clone()),
                (false, true) => {}
                (false, false) => link = Some((name.clone(), a.payload.clone())),
                _ => return None,
            }
        }
        let (name, payload) = link?;
        let q = payload.p();
        if q.tuples.rest || q.tuples.lens.len() != 1 || !q.tuples.lens.contains_key(&2) {
            return None;
        }
        let f = &q.tuples.lens[&2];
        let (taken, refused) = f.forced();
        let atoms = f.distinct_atoms();
        if taken.len() + refused.len() != atoms.len() || atoms.is_empty() {
            return None;
        }
        if !f.eval(&|a| taken.contains(a)) {
            return None;
        }
        let mut stop: Option<std::sync::Arc<str>> = bare;
        let item = atoms[0][0].clone();
        let mut read = |s: &mut Self, a: &Row| -> Option<(u64, u64)> {
            let c = s.cycle(&a[1])?;
            let fits = a[0] == item && c.item == item && c.link == name;
            let same = stop.get_or_insert_with(|| c.stop.clone()) == &c.stop;
            // A length one more than a length of the rest.
            (fits && same).then_some((c.period, (c.at + 1) % c.period))
        };
        let mut all = Vec::with_capacity(taken.len());
        for a in &taken {
            all.push(read(self, a)?);
        }
        let mut none = Vec::with_capacity(refused.len());
        for a in &refused {
            none.push(read(self, a)?);
        }
        if self.empty(&item) {
            return None;
        }
        Some(Meet {
            stop: stop?,
            link: name,
            item,
            bare: p.atoms.names.values().any(|a| a.bare),
            all,
            none,
        })
    }

    /// The answer for `t`, when `t` is a stop atom or not, and a link atom whose rest is the
    /// meet of pure cycles less at most one, all of one item: the lengths are then residues,
    /// and whether one survives is decided without walking their product.
    fn pure_cycles(&mut self, t: &Type) -> Option<Lengths> {
        let m = self.cycle_meet(t)?;
        Some(match m.bare {
            true => Lengths::Some,
            false => residues_meet(&m.all, &m.none),
        })
    }

    /// A list of `m`. When the rule says one exists, the shortest, by `least_length`. When the
    /// rule refuses, the shortest not longer than the length `greedy_length` picks, if that one
    /// fits; none found means only that. The list is built one link at a time, so the cost is
    /// its length plus the work of `least_length`; none is built when the length is above
    /// `u64`.
    fn cycle_rep(&mut self, m: &Meet) -> Option<Rep> {
        let fits = |n: u64| {
            m.all.iter().all(|&(p, at)| n % p == at) && m.none.iter().all(|&(p, at)| n % p != at)
        };
        let n = match residues_meet(&m.all, &m.none) {
            Lengths::Some => least_length(&m.all, &m.none, None)?,
            Lengths::None => return None,
            Lengths::Refused => {
                let bound = greedy_length(&m.all, &m.none).filter(|&n| fits(n))?;
                least_length(&m.all, &m.none, Some(bound))?
            }
        };
        let item = self.rep(&m.item)?;
        self.shown.push(Rep::Value(Value::atom(&m.stop)));
        let mut rest = self.shown.len() - 1;
        for _ in 1..n {
            self.shown.push(Rep::Tuple(vec![item, rest]));
            self.shown
                .push(Rep::Atom(m.link.clone(), self.shown.len() - 1));
            rest = self.shown.len() - 1;
        }
        self.shown.push(Rep::Tuple(vec![item, rest]));
        Some(Rep::Atom(m.link.clone(), self.shown.len() - 1))
    }

    /// A value in `t`, if one is found: a scalar or bare atom of it, or a tuple or atom payload
    /// whose components have representatives and which `t` holds. The tuples tried at each
    /// length are two: the box the tuple types narrow the part to, and its meet with the first
    /// tuple type left open; each is tested against every tuple type of `t`, so a poor choice
    /// costs precision, never soundness. A type met again while its own is sought has none on
    /// that path, since a value is finite; none found means only that, never that `t` is
    /// empty. Each type is tried once and each test of a representative against a type is
    /// made once, so a value nested in shared types is never copied out.
    fn rep(&mut self, t: &Type) -> Option<usize> {
        if let Some(r) = self.reps.get(t) {
            return *r;
        }
        self.reps.insert(t.clone(), None);
        self.building.insert(t.clone());
        let (mark, resting) = (self.built.len(), self.resting);
        let r = self.find_rep(t).map(|v| {
            self.shown.push(v);
            self.shown.len() - 1
        });
        self.building.remove(t);
        self.reps.insert(t.clone(), r);
        if r.is_some() {
            self.built.push(t.clone());
        } else if self.resting > resting {
            // What was built here rests on a value that does not exist.
            for x in self.built.split_off(mark) {
                self.reps.remove(&x);
            }
        }
        r
    }

    /// Whether a closure can return a value of `v`.
    fn returnable(&mut self, v: &Type) -> bool {
        if self.building.contains(v) {
            self.resting += 1;
            return true;
        }
        self.rep(v).is_some()
    }

    /// The representatives of the row, if each component has one, when they make a tuple of `f`.
    fn row_rep(&mut self, row: &[Type], f: &Part<Row>) -> Option<Rep> {
        let mut vs = Vec::with_capacity(row.len());
        for x in row {
            vs.push(self.rep(x)?);
        }
        self.holds(&vs, f).then_some(Rep::Tuple(vs))
    }

    fn find_rep(&mut self, t: &Type) -> Option<Rep> {
        // A bare atom is a value: the empty list of a list type.
        if let Some(name) = t
            .p()
            .atoms
            .names
            .iter()
            .find_map(|(n, a)| a.bare.then_some(n))
        {
            return Some(Rep::Value(Value::atom(name)));
        }
        // A list of pure cycles with no stop in it: its shortest list.
        if let Some(m) = self.cycle_meet(t) {
            return self.cycle_rep(&m);
        }
        let p = t.p();
        if p.bools != 0 {
            return Some(Rep::Value(Value::Bool(p.bools & 1 == 0)));
        }
        type Fresh = Option<fn(i64) -> Value>;
        let fresh: [(&Lits, Fresh); 4] = [
            (&p.ints, Some(Value::Int)),
            (&p.strings, Some(|i| Value::str(&i.to_string()))),
            (&p.rats, None),
            (&p.floats, None),
        ];
        for (l, make) in fresh {
            let v = match (l.cofinite, make) {
                (false, _) => l.values.iter().next().cloned(),
                (true, Some(make)) => (0..).map(make).find(|v| !l.values.contains(v)),
                (true, None) => None,
            };
            if let Some(v) = v {
                return Some(Rep::Value(v));
            }
        }
        if p.atoms.cofinite {
            let name = (0..)
                .map(|i| format!("a{i}"))
                .find(|n| !p.atoms.names.contains_key(n.as_str()));
            return Some(Rep::Value(Value::atom(&name.expect("a name is free"))));
        }
        for (name, a) in &p.atoms.names {
            if a.bare {
                return Some(Rep::Value(Value::atom(name)));
            }
            if let Some(r) = self.rep(&a.payload)
                && matches!(self.shown[r], Rep::Tuple(_))
            {
                return Some(Rep::Atom(name.clone(), r));
            }
        }
        if p.structs {
            return Some(Rep::Struct);
        }
        if p.morphisms.is_leaf() != Some(false) {
            let top = Morphism {
                guarantee: Type::empty(),
                permission: Type::top(),
                value: Type::top(),
            };
            // A closure is shown only for a meet of morphism types whose keys are all
            // permitted as written and whose value type has a value, which may be one being
            // built here, holding this closure: a closure can return itself.
            let (taken, refused) = p.morphisms.forced();
            let whole = refused.is_empty() && taken.len() == p.morphisms.distinct_atoms().len();
            let meets: Vec<Morphism> = match (whole, p.morphisms.union_rows()) {
                (true, _) => vec![taken.iter().fold(top, |r, a| meet(&r, a))],
                (false, Some(rows)) => rows,
                (false, None) => Vec::new(),
            };
            for m in &meets {
                let permitted = m.guarantee == m.permission
                    || m.guarantee == Type::empty()
                    || m.permission == Type::top();
                if !permitted {
                    continue;
                }
                // What the closure returns may hold the closure, at any depth.
                let mark = self.built.len();
                self.shown.push(Rep::Closure);
                self.reps.insert(t.clone(), Some(self.shown.len() - 1));
                let returns = self.returnable(&m.value);
                self.reps.insert(t.clone(), None);
                if returns {
                    return Some(Rep::Closure);
                }
                for x in self.built.split_off(mark) {
                    self.reps.remove(&x);
                }
            }
        }
        if p.tuples.rest {
            let len = (0..)
                .find(|n| !p.tuples.lens.contains_key(n))
                .expect("a length is free");
            let row = vec![Type::top(); len];
            let mut vs = Vec::with_capacity(len);
            for x in &row {
                vs.push(self.rep(x)?);
            }
            return Some(Rep::Tuple(vs));
        }
        for f in p.tuples.lens.values() {
            for row in f.union_rows().unwrap_or_default() {
                let vs: Option<Vec<usize>> = row.iter().map(|x| self.rep(x)).collect();
                if let Some(vs) = vs {
                    return Some(Rep::Tuple(vs));
                }
            }
        }
        if self.seeding {
            for f in p.tuples.lens.values() {
                for row in f.distinct_atoms() {
                    if let Some(v) = self.row_rep(&row, f) {
                        return Some(v);
                    }
                }
            }
            return None;
        }
        for (len, f) in &p.tuples.lens {
            if f.union_rows().is_some() {
                continue;
            }
            let (mut b, mut g) = (self.region(vec![Type::top(); *len], f), f.clone());
            if self.narrow_tuples(&mut b, &mut g) {
                continue;
            }
            if let Some(v) = self.row_rep(&b.r.clone(), f) {
                return Some(v);
            }
            if let Some(found) = self.class_rep(&b, &g, *len) {
                match found {
                    Some(v) => return Some(v),
                    None => continue,
                }
            }
            // One candidate for each tuple type left, narrowed by what the part says of it.
            for a in g.distinct_atoms() {
                let k = b.index[&a];
                let mark = b.log.len();
                for j in 0..b.r.len() {
                    if b.is_open(k, j) {
                        let t = &b.r[j] & &a[j];
                        b.shrink(j, t);
                        b.close(j, b.cell(k, j), false);
                    }
                }
                let mut h = g.clone();
                let row = (!self.narrow_tuples(&mut b, &mut h)).then(|| b.r.clone());
                b.restore(mark);
                if let Some(v) = row.and_then(|r| self.row_rep(&r, f)) {
                    return Some(v);
                }
            }
            // One candidate for each component: the box with that component outside every
            // tuple type the part excludes, so the tuple is in none of them. Pairs of a list
            // and an integer without those of lists of only 1s or only 2s hold `([0], 0)`,
            // whose list is in neither excluded list type.
            let (_, excluded) = g.forced();
            for j in 0..b.r.len() {
                let out = excluded.iter().fold(b.r[j].clone(), |t, a| &t - &a[j]);
                if out == b.r[j] {
                    continue;
                }
                let mut row = b.r.clone();
                row[j] = out;
                if let Some(v) = self.row_rep(&row, f) {
                    return Some(v);
                }
            }
            if let Some(row) = self.refine(*len, f)
                && let Some(v) = self.row_rep(&row, f)
            {
                return Some(v);
            }
        }
        None
    }

    /// A value of the tuple part `g` of length `len` on the box of `b`, sought piece by piece
    /// when the open tuple types fall into classes on a component, as `split_classes` decides
    /// them: the rest, which no class meets, then each half of the classes, each piece a type
    /// of its own whose part holds no tuple type of the other half. Each half is split again
    /// when its value is sought, so each tuple type is in the part of O(log k) of the pieces.
    /// Nothing when there are no such classes; `Some(None)` when no piece has a value found.
    fn class_rep(&mut self, b: &Region, g: &Part<Row>, len: usize) -> Option<Option<Rep>> {
        let open: Vec<usize> = g.distinct_atoms().iter().map(|a| b.index[a]).collect();
        let (j, classes) = classes(b, &open)?;
        let m = classes.len() / 2;
        let union = |cs: &[Class]| cs.iter().fold(Type::empty(), |u, (c, _)| &u | c);
        let atoms = |cs: &[Class]| -> BTreeSet<usize> {
            cs.iter().flat_map(|(_, ks)| ks.iter().copied()).collect()
        };
        let (lo, hi) = classes.split_at(m);
        let pieces = [
            (&b.r[j] - &union(&classes), atoms(&classes)),
            (&b.r[j] & &union(lo), atoms(hi)),
            (&b.r[j] & &union(hi), atoms(lo)),
        ];
        for (cell, out) in pieces {
            let part = g.restrict(&|a| out.contains(&b.index[a]).then_some(false));
            if part.is_leaf() == Some(false) || cell == Type::empty() {
                continue;
            }
            let mut row = b.r.clone();
            row[j] = cell;
            let piece = &Type::tuple(row)
                & &Type::with(|p| {
                    p.tuples.lens.insert(len, part);
                });
            if let Some(r) = self.rep(&piece) {
                return Some(Some(self.shown[r].clone()));
            }
        }
        Some(None)
    }

    /// A box within the tuple part `f` of length `len`, found by splitting each component, one
    /// tuple type at a time, into the piece inside that tuple type and the piece outside it,
    /// and keeping a piece the search shows inhabited, else one it does not prove empty. Each
    /// step is at most two searches, so the searches are at most twice the tuple types times
    /// the components, and the box ends closed on every tuple type: the part then holds all of
    /// it or none.
    fn refine(&mut self, len: usize, f: &Part<Row>) -> Option<Vec<Type>> {
        let refuse_forks = std::mem::replace(&mut self.refuse_forks, false);
        let mut g = self.region(vec![Type::top(); len], f);
        let mut h = f.clone();
        let mut empty = self.narrow_tuples(&mut g, &mut h);
        for j in 0..len {
            for k in 0..g.atoms.len() {
                if empty || !g.is_open(k, j) {
                    continue;
                }
                let inside = &g.r[j] & &g.atoms[k][j];
                let outside = &g.r[j] - &g.atoms[k][j];
                // Whether the search proves the piece empty, and whether it shows it inhabited.
                let try_piece = |s: &mut Self, g: &mut Region, piece: &Type| {
                    let (mark, give_ups) = (g.log.len(), s.give_ups);
                    g.shrink(j, piece.clone());
                    let none = s.tuples(g, h.clone(), true);
                    g.restore(mark);
                    (none, !none && s.give_ups == give_ups)
                };
                let piece = match try_piece(self, &mut g, &inside) {
                    (true, _) => outside,
                    (_, true) => inside,
                    _ => match try_piece(self, &mut g, &outside) {
                        (false, true) => outside,
                        _ => inside,
                    },
                };
                g.shrink(j, piece);
                empty = self.narrow_tuples(&mut g, &mut h);
            }
        }
        self.refuse_forks = refuse_forks;
        (!empty && h.is_leaf() == Some(true)).then_some(g.r)
    }

    /// Whether the tuple `vs` is in `f`.
    fn holds(&mut self, vs: &[usize], f: &Part<Row>) -> bool {
        let mut fits = BTreeSet::new();
        for a in f.distinct_atoms() {
            if vs.iter().zip(a.iter()).all(|(v, y)| self.member(*v, y)) {
                fits.insert(a);
            }
        }
        let b = f.eval(&|a| fits.contains(a));
        b && !std::mem::take(&mut self.unsure)
    }

    /// Whether the value numbered `v` is in `u`.
    fn member(&mut self, v: usize, u: &Type) -> bool {
        if let Rep::Value(x) = &self.shown[v] {
            return u.contains(x);
        }
        let key = (v, u.clone());
        if let Some(b) = self.members.get(&key) {
            return *b;
        }
        let b = match self.shown[v].clone() {
            Rep::Value(_) => unreachable!("a value was read above"),
            Rep::Closure => {
                let b = u.p().morphisms.is_leaf();
                self.unsure |= b.is_none();
                b == Some(true)
            }
            Rep::Struct => u.p().structs,
            Rep::Tuple(vs) => self.holds(&vs, &u.p().tuples.get(vs.len())),
            Rep::Atom(name, payload) => match u.p().atoms.names.get(&name) {
                None => u.p().atoms.cofinite,
                Some(a) => self.member(payload, &a.payload.clone()),
            },
        };
        self.members.insert(key, b);
        b
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    fn within(&mut self, m: &Morphism, n: &Morphism) -> bool {
        let no_value = self.no_value(&m.value);
        self.empty(&(&n.guarantee - &m.guarantee))
            && (no_value || self.empty(&(&m.permission - &n.permission)))
            && (no_value || self.empty(&m.permission) || self.empty(&(&m.value - &n.value)))
    }

    /// Whether no morphism `r` admits is in `f`, decided as for tuples: `r` meets the morphism
    /// types in every value of `f`, and, once on each branch, when `f` holds nothing outside
    /// the open morphism types, each is decided on its own. Morphism types are closed under
    /// meet but not under difference, so a type in no value of `f` narrows nothing.
    fn morphisms(&mut self, mut r: Morphism, mut f: Part<Morphism>, may_cover: bool) -> bool {
        loop {
            if self.no_morphism(&r) {
                return true;
            }
            let st: BTreeMap<Morphism, Option<bool>> = f
                .distinct_atoms()
                .into_iter()
                .map(|a| {
                    let s = if self.no_morphism(&meet(&r, &a)) {
                        Some(false)
                    } else if self.within(&r, &a) {
                        Some(true)
                    } else {
                        None
                    };
                    (a, s)
                })
                .collect();
            f = f.restrict(&|a| st.get(a).copied().flatten()).settle();
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let (taken, _) = f.forced();
            if !taken.is_empty() {
                r = taken.iter().fold(r, |r, a| meet(&r, a));
                continue;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                return f
                    .distinct_atoms()
                    .iter()
                    .all(|a| self.morphisms(meet(&r, a), f.clone(), false));
            }
            self.give_up(Refusal::MorphismSplit);
            return false;
        }
    }
}

/// A class of cells on one component: the union of its cells, and its open tuple types.
type Class = (Type, BTreeSet<usize>);

/// The first component on which every tuple type of `open` is open and their cells fall into
/// two or more classes, two cells of different classes sharing no value: each class as the
/// union of its cells and its tuple types among `open`, in the order of their first cells.
/// Each tuple type then goes to one piece of the split, as in the split into disjoint pieces,
/// so the pieces below a split hold each tuple type at most once and the nodes stay linear in
/// the tuple types; a tuple type that held the component would go to every piece, and splits
/// in turn on each component would be a search over all of them.
fn classes(g: &Region, open: &[usize]) -> Option<(usize, Vec<Class>)> {
    (0..g.r.len()).find_map(|j| {
        if g.opens[j] < open.len() || open.iter().any(|&k| !g.is_open(k, j)) {
            return None;
        }
        let cells: Vec<usize> = g.open_cells(j, open).into_iter().collect();
        let groups = overlaps(cells.iter().map(|&c| g.cells[j][c].ty.p()));
        if groups.len() < 2 {
            return None;
        }
        let open: BTreeSet<usize> = open.iter().copied().collect();
        let classes = groups.into_iter().map(|is| {
            let cells = is.iter().map(|&i| &g.cells[j][cells[i]]);
            let ty = cells.clone().fold(Type::empty(), |u, c| &u | &c.ty);
            let ks = cells
                .flat_map(|c| c.rows.iter().copied())
                .filter(|k| open.contains(k));
            (ty, ks.collect())
        });
        Some((j, classes.collect()))
    })
}

/// What a value of a type can be equal to, per universe: a literal or atom name, or the whole
/// universe. Two types with no key in common are disjoint.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Bool(u8),
    Lit(usize, Value),
    Atom(std::sync::Arc<str>),
    Len(usize),
    /// A whole universe: 0 to 3 the literals of `Lits`, 4 the atoms, 5 the tuples, 6 the
    /// structs, 7 the morphisms.
    All(usize),
}

/// The types `ps` in classes, by index in order of their first members, joined when they share
/// a key: two types of different classes are disjoint. A universe in which one of them has a
/// cofinite set is one key for all of them, so the keys are found in two passes.
// Complexity tradeoff: types are joined by what they could share, not by their meet, so two
// types that share a key but are disjoint (`int \ 3` and `3`, `#a(1)` and `#a(2)`, two tuple
// types of one length) land in one class and the split is coarser. Keys cost the size of the
// types, where testing each pair's meet costs their square. Test:
// `l01_23_subtyping::scaling::a_union_of_disjoint_pinwheels_is_decided_piece_by_piece`.
fn overlaps<'a>(ps: impl Iterator<Item = &'a Parts> + Clone) -> Vec<Vec<usize>> {
    let lits = |p: &'a Parts| [&p.ints, &p.rats, &p.floats, &p.strings];
    let mut wide = [false; 6];
    for p in ps.clone() {
        for (s, l) in lits(p).into_iter().enumerate() {
            wide[s] |= l.cofinite;
        }
        wide[4] |= p.atoms.cofinite;
        wide[5] |= p.tuples.rest;
    }
    let mut first: BTreeMap<Key, usize> = BTreeMap::new();
    let mut parent: Vec<usize> = Vec::new();
    fn root(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    for (i, p) in ps.enumerate() {
        parent.push(i);
        let mut keys: Vec<Key> = (0..2u8)
            .filter(|b| p.bools >> b & 1 == 1)
            .map(Key::Bool)
            .collect();
        for (s, l) in lits(p).into_iter().enumerate() {
            match wide[s] {
                true if l.cofinite || !l.values.is_empty() => keys.push(Key::All(s)),
                true => {}
                false => keys.extend(l.values.iter().map(|v| Key::Lit(s, v.clone()))),
            }
        }
        match wide[4] {
            true if p.atoms.cofinite || !p.atoms.names.is_empty() => keys.push(Key::All(4)),
            true => {}
            false => keys.extend(p.atoms.names.keys().map(|n| Key::Atom(n.clone()))),
        }
        match wide[5] {
            true if p.tuples.rest || !p.tuples.lens.is_empty() => keys.push(Key::All(5)),
            true => {}
            false => keys.extend(p.tuples.lens.keys().map(|&n| Key::Len(n))),
        }
        if p.structs {
            keys.push(Key::All(6));
        }
        if p.morphisms.is_leaf() != Some(false) {
            keys.push(Key::All(7));
        }
        for k in keys {
            let j = *first.entry(k).or_insert(i);
            let (a, b) = (root(&mut parent, i), root(&mut parent, j));
            parent[a.max(b)] = a.min(b);
        }
    }
    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..parent.len() {
        let r = root(&mut parent, i);
        groups.entry(r).or_default().push(i);
    }
    groups.into_values().collect()
}

/// Whether `p` has no value but atoms.
fn only_atoms(p: &Parts) -> bool {
    let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
    p.bools == 0
        && lits.iter().all(|l| !l.cofinite && l.values.is_empty())
        && p.morphisms.is_leaf() == Some(false)
}

/// The parts of one step of a list, as [`list_step`] gives them.
type Step = (Option<std::sync::Arc<str>>, std::sync::Arc<str>, Type, Type);

/// One step of a list: the stop atom of `t` if it has one, the link atom, its item, and the
/// rest; none when `t` is not of that shape.
fn list_step(t: &Type) -> Option<Step> {
    let p = t.p();
    if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(p) || p.atoms.cofinite
    {
        return None;
    }
    let (mut stop, mut link) = (None, None);
    for (name, a) in &p.atoms.names {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) => stop = Some(name.clone()),
            (false, true) => {}
            (false, false) => link = Some((name.clone(), a.payload.clone())),
            _ => return None,
        }
    }
    let (name, payload) = link?;
    let q = payload.p();
    let f = q.tuples.lens.get(&2)?;
    let atoms = f.distinct_atoms();
    if q.tuples.rest || q.tuples.lens.len() != 1 || atoms.len() != 1 || !f.eval(&|_| true) {
        return None;
    }
    if f.eval(&|_| false) {
        return None;
    }
    Some((stop, name, atoms[0][0].clone(), atoms[0][1].clone()))
}

/// The morphisms both `a` and `b` admit.
fn meet(a: &Morphism, b: &Morphism) -> Morphism {
    Morphism {
        guarantee: &a.guarantee | &b.guarantee,
        permission: &a.permission & &b.permission,
        value: &a.value & &b.value,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `inverse`, `crt` and `least_length` against a scan of the lengths from 1, on every
    /// choice of at most two classes of `all` and three of `none` with periods 1 to 6, from a
    /// fixed sequence.
    #[test]
    fn the_least_length_agrees_with_a_scan() {
        for m in 1..40u64 {
            for a in 0..m {
                let found = inverse(a, m);
                let scanned = (0..m).find(|&x| a * x % m == 1 % m);
                assert_eq!(found, scanned, "the inverse of {a} modulo {m}");
            }
        }
        let mut seed = 7u64;
        let mut next = |below: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % below
        };
        for _ in 0..20_000 {
            let (a, b) = (next(3), next(4));
            let mut classes: Vec<(u64, u64)> = (0..a + b)
                .map(|_| {
                    let p = 1 + next(6);
                    (p, next(p))
                })
                .collect();
            let none = classes.split_off(a as usize);
            let all = classes;
            let fits = |n: u64| {
                all.iter().all(|&(p, at)| n % p == at) && none.iter().all(|&(p, at)| n % p != at)
            };
            // Every class repeats within the lcm of the periods, at most 60.
            let scanned = (1..=120).find(|&n| fits(n));
            let first = (0..60).find(|&n| all.iter().all(|&(p, at)| n % p == at));
            assert_eq!(crt(&all).map(|c| c.0), first, "{all:?}");
            assert_eq!(
                least_length(&all, &none, Some(120)),
                scanned,
                "{all:?} {none:?}"
            );
            if let Some(n) = scanned {
                assert_eq!(least_length(&all, &none, None), Some(n));
                assert_eq!(least_length(&all, &none, Some(n - 1)), None);
            }
        }
    }

    /// In `(a - b) | (b - a)` the diagram tests `b` on two nodes; the region gives each tuple
    /// type one entry, so each is tested once and counted once among those open on a component.
    #[test]
    fn a_region_lists_each_tuple_type_once() {
        let a = Type::tuple(vec![Type::int(), Type::top()]);
        let b = Type::tuple(vec![Type::top(), Type::int()]);
        let t = &(&a - &b) | &(&b - &a);
        let f = &t.p().tuples.lens[&2];
        let mut nodes = 0;
        f.atoms(&mut |_| {
            nodes += 1;
            true
        });
        assert!(nodes >= 3);
        let g = Search::default().region(vec![Type::top(); 2], f);
        assert_eq!((g.atoms.len(), g.missed.len()), (2, 2));
        assert_eq!(g.opens, [1, 1]);
    }

    /// Tuple types with one type in a component share its cell there, which is tested once
    /// for all of them; a type that holds the box there is closed, and one open on it is open.
    #[test]
    fn tuple_types_with_one_component_type_share_its_cell() {
        let lit = |i| Type::lit(&Value::Int(i)).unwrap();
        let ints = Type::int();
        let rows: Vec<Type> = (0..4)
            .map(|i| Type::tuple(vec![lit(i), ints.clone(), lit(i % 2)]))
            .collect();
        let t = Type::union_all(rows);
        let f = &t.p().tuples.lens[&3];
        let g = Search::default().region(vec![Type::top(); 3], f);
        let sizes: Vec<Vec<usize>> = g
            .cells
            .iter()
            .map(|cells| cells.iter().map(|c| c.rows.len()).collect())
            .collect();
        assert_eq!(sizes, [vec![1, 1, 1, 1], vec![4], vec![2, 2]]);
        assert_eq!(g.opens, [4, 4, 4]);
        let mut h = Search::default().region(vec![Type::top(), Type::int(), Type::top()], f);
        assert_eq!(h.opens, [4, 0, 4]);
        assert!(h.loose.iter().all(|&(n, at)| (n, at) == (2, 2)));
        // Narrowing the last component to `0` closes the cell `1` as missed for both of its
        // tuple types at once, and leaves `0` to be tested again.
        h.shrink(2, lit(0));
        let mut s = Search::default();
        s.retest(&mut h);
        for (k, a) in h.atoms.iter().enumerate() {
            assert_eq!(h.missed[k], usize::from(a[2] == lit(1)), "{k}");
        }
        assert_eq!(h.opens, [4, 0, 0]);
    }
}
