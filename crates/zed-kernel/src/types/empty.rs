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
//! proves empty counts as inhabited for `is_empty`, and `Type::verdict` answers
//! `Refused(TupleSplit)` for it unless a value is found first: a subtyping check then fails,
//! and the error names the types and the cause, so the program states the case split itself
//! (DESIGN.md L1.23).
//!
//! Complexity tradeoff: what is given up, why and the trigger are the paragraph above: a
//! part that only a split of the box in two or more components at once proves empty counts as
//! inhabited, and `verdict` answers `Refused(TupleSplit)` (a subtyping check fails; the
//! representative search of `no_morphism` likewise answers "none found", never "empty"). The
//! site comment at `give_up(Refusal::TupleSplit)` names the steps tried first. Tests:
//! `l01_23_subtyping::scaling::a_type_not_proved_empty_promises_no_key` (four pigeons in three
//! holes, empty and not proved so) and `l01_23_subtyping::refusals::each_refusal_names_its_cause`
//! (`box_cover`). COMPLEXITY.md rows K1 and K2, and the Kept row
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

use std::cell::{RefCell, RefMut};
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::future::Future;
use std::ops::{ControlFlow, Range};
use std::pin::Pin;

use num_bigint::BigUint;

use super::bdd::{Bdd, Form, Part};
use super::{Lits, Morphism, Node, Parts, Row, Type};
use crate::frames::{Deep, Stack};
use crate::value::Value;

thread_local! {
    static MEMO: RefCell<BTreeMap<Type, bool>> = const { RefCell::new(BTreeMap::new()) };
    /// The verdict of each type asked. A verdict is decided by a search that reads no kept
    /// result, or with the other members of its recursive group ([`group_verdicts`]), so it is
    /// a function of the type alone, and keeping it changes no answer: these
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

/// Keeps the verdicts of `members`, the recursive members of one group, for each member its
/// group's decider (module `bes`) decides: a member decided empty is `Empty`, and one decided
/// inhabited is `Inhabited` once a value of it is built and checked. The values are built by one
/// search for all members, in definition order, which keeps each value it builds, so a type
/// shared by members is given its value once: the verdicts of a group of n cost what one search
/// over the group does, where a search for each member would read the group n times. A member
/// with no value built here is given the verdict of a search of its own. Each verdict is a
/// function of the group, which every member names, whichever member is asked first.
fn group_verdicts(members: &[Type]) {
    let mut s = Search {
        strict: true,
        ..Search::default()
    };
    for m in members {
        let v = match m.judged() {
            Some(true) => Verdict::Empty,
            Some(false) if s.rep(m).is_some() => Verdict::Inhabited,
            // Complexity tradeoff: a member decided inhabited whose value the shared search does
            // not build gets a search of its own, which may read the whole group again; the X14
            // groups of 1024 and 2048 definitions measured for plan item VERDICT-group-share
            // needed none.
            Some(false) => m.verdict_alone(),
            None => continue,
        };
        VERDICTS.with(|k| k.borrow_mut().insert(m.clone(), v));
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
        // A type of scalars alone is empty when its parts list none, which costs less than
        // finding the type among those kept.
        if let Node::Parts(p, _) = &*self.0
            && p.scalars_only()
        {
            return !p.has_scalars();
        }
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
    /// value and would make the outcome depend on the queries before it. A member of a recursive
    /// group that its decider decides gets its verdict with the other members
    /// ([`group_verdicts`]).
    pub fn verdict(&self) -> Verdict {
        let kept = || VERDICTS.with(|m| m.borrow().get(self).copied());
        if let Some(v) = kept() {
            return v;
        }
        // Complexity tradeoff: a member its decider does not decide (a refusal, or a recursive
        // occurrence under `&`, `\` or a complement) gets a search of its own, which reads no
        // result of another member, so the verdicts of every member of such a group of n cost n
        // searches of the group, O(n^2). Trigger: `judged` is none. COMPLEXITY.md row K55.
        if self.judged().is_some()
            && let Some(members) = self.group_members()
        {
            group_verdicts(&members);
            if let Some(v) = kept() {
                return v;
            }
        }
        let v = self.verdict_alone();
        VERDICTS.with(|m| m.borrow_mut().insert(self.clone(), v));
        v
    }

    /// The verdict of `self` by a search of its own.
    fn verdict_alone(&self) -> Verdict {
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            ..Search::default()
        };
        let b = s.solve(self);
        let decided = s.refused.is_none();
        if decided && b {
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
            // Complexity tradeoff: a type the search neither proved empty nor showed inhabited by
            // a built value is refused, never called empty or inhabited, so a verdict is never
            // wrong; it gives up the answer itself. Why: the search is incomplete (the tradeoffs
            // at the Fork, Residues, TupleSplit and MorphismSplit sites), and the value builder
            // shows only values it can check: a closure is built only when a value of its value
            // type is built, or when its key type is known empty without a search (the empty
            // type, or a recursive type its group decided empty), so it is never called. A key
            // type only a search proves empty, such as `bool -> empty`, gets no closure, so
            // `(bool -> empty) -> empty` is refused. Trigger: no refusal was named, and neither
            // search built a value. Tests:
            // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`morphism_between`),
            // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length` and
            // `l01_23_subtyping::judgments::a_morphism_cycle_through_an_empty_part_is_empty`.
            // COMPLEXITY.md Kept row "emptiness and subtyping of tuple and morphism parts". A
            // complete solution needs a value builder for every kind of type (closures included,
            // L2), the emptiness of each key type decided within the search that reads it, and a
            // complete search.
            Verdict::Refused(s.refused.or(s.gave_up).unwrap_or(Refusal::NoWitness))
        }
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
    /// The pairs made and not yet compared row by row, with their number. They are compared
    /// from this stack rather than when made, so a type nested to any depth takes no more of
    /// the thread's stack than a shallow one; the answer does not depend on the order, since
    /// failures are spread only once every pair reached is made.
    todo: Vec<(usize, Type, Type)>,
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
        while let Some((i, a, b)) = self.todo.pop() {
            self.compare(i, &a, &b);
        }
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
            self.todo.push((i, a.clone(), b.clone()));
        }
        i
    }

    /// Compares the pair numbered `i`, of `a` under `b`, row by row: what it needs of other
    /// pairs, which are made, and whether it fails here.
    fn compare(&mut self, i: usize, a: &Type, b: &Type) {
        let Some(needs) = self.rows(a.p(), b.p()) else {
            self.nodes[i].failed = true;
            return;
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
    members: BTreeMap<(usize, Type), Option<bool>>,
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
    /// The types whose missing value the build under way has read.
    read: Vec<Type>,
    /// For each type, the kept failures that read its missing value: they are sought again when
    /// it gets one ([`Searching::retry`]).
    waiting: BTreeMap<Type, Vec<Type>>,
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
    /// The meet (`true`) or difference (`false`) of each pair of nodes `settles` tested, built
    /// once, by the nodes' addresses; the operands are kept with it, so no address is reused.
    cuts: BTreeMap<(usize, usize, bool), (Type, Type, Type)>,
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
///
/// Complexity tradeoff: one prime split at a time, never several at once, so what only a
/// joint split decides is `Refused`; the covering problem for residues is NP-hard. Trigger,
/// tests, row and a complete solution: the comment at the `Refusal::Residues` site in
/// `Search::decide`.
fn residues_meet(all: &[(u64, u64)], none: &[(u64, u64)]) -> Lengths {
    residue_classes(all, none).0
}

/// As `residues_meet`, with the classes whose lengths it found to hold one when it answers
/// `Some`: `all`, or `all` and the class of the split that has one.
fn residue_classes(all: &[(u64, u64)], none: &[(u64, u64)]) -> (Lengths, Vec<(u64, u64)>) {
    let first = shares(all, none);
    if first != Lengths::Refused {
        return (first, all.to_vec());
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
                Lengths::Some => {
                    split.push((q, b));
                    return (Lengths::Some, split);
                }
                Lengths::None => {}
                Lengths::Refused => all_none = false,
            }
        }
        if all_none {
            return (Lengths::None, Vec::new());
        }
    }
    (Lengths::Refused, Vec::new())
}

/// A length in the lengths of `all` and in none of `none`, sought by the method of conditional
/// expectations: the residue modulo each prime power of the periods is chosen in turn, the one
/// for which the negated classes expected to hold the length are fewest, the residues not yet
/// chosen taken as uniform among those `all` allows. When the shares sum to less than one a
/// length is always found; otherwise one may be missed, and the caller checks it. The work is
/// the residues tried times the classes times the primes, and the length is at most the lcm of
/// the periods, a number of as many digits as the periods have together.
fn greedy_length(all: &[(u64, u64)], none: &[(u64, u64)]) -> BigUint {
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
    let (mut n, mut m) = (BigUint::ZERO, BigUint::from(1u32));
    for (&r, &d) in &chosen {
        let q = primes[&r].0;
        let below = |x: &BigUint| u64::try_from(x % q).expect("a residue is below q");
        let inv = inverse(below(&m), q).unwrap_or(0);
        let gap = (d % q + q - below(&n)) % q;
        let step = u128::from(gap) * u128::from(inv) % u128::from(q);
        n += &m * u64::try_from(step).expect("a residue is below q");
        m *= q;
    }
    if n == BigUint::ZERO { m } else { n }
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

/// A length in all the classes of `all` and in none of `none`: the one `greedy_length` picks on
/// the classes `residue_classes` found to hold one (on `all` when it refuses), checked against
/// every class. The work is that of the two, polynomial in the classes; the length, up to the
/// lcm of the periods and so exponential in them, is a number and no list of it is walked.
fn residue_length(all: &[(u64, u64)], none: &[(u64, u64)]) -> Option<BigUint> {
    let fits = |n: &BigUint| {
        all.iter().all(|&(p, at)| n % p == BigUint::from(at))
            && none.iter().all(|&(p, at)| n % p != BigUint::from(at))
    };
    let (lengths, classes) = residue_classes(all, none);
    let classes = if lengths == Lengths::Some {
        classes
    } else {
        all.to_vec()
    };
    // Complexity tradeoff: the length is one choice by conditional expectations, not the least
    // length, and when the shares of the negated classes sum to one or more (they meet, or a
    // split on one prime was needed) the choice can fall in a negated class; then no length is
    // given, and a list of the type is not shown, though the rule proves one exists. The type
    // itself is still inhabited by the rule (`Search::decide`); a tuple or atom holding such a
    // list can get no value, and its verdict is then `Refused(NoWitness)`. The least length,
    // found by sieving the steps from 1 (the former `least_length`), costs the steps passed,
    // up to the lcm of the periods, exponential in the number of cycles: the meet of
    // `period(p, p - 1)` over the first nine primes took 31 s. Tests:
    // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length` and
    // `the_meet_of_prime_cycles_scales`; COMPLEXITY.md K34. A complete solution would search
    // the residues modulo each prime power with backtracking, exponential in the primes in the
    // worst case, since the covering problem for residues is NP-hard.
    Some(greedy_length(&classes, none)).filter(fits)
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
#[derive(Default)]
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
    /// A list of `len` links, each a `link` atom holding the item numbered `item` and the rest,
    /// ending in the atom `stop`. It is kept as its length, never built link by link: the
    /// length of a meet of pure cycles can be exponential in the number of cycles.
    List {
        stop: std::sync::Arc<str>,
        link: std::sync::Arc<str>,
        item: usize,
        len: BigUint,
    },
    /// A closure; it may be recursive. Whether it is in a type is known only when that type
    /// holds all morphisms or none.
    Closure,
    Struct,
}

/// A [`Search`] running on an explicit stack on the heap (module [`crate::frames`]). The
/// methods that may recurse through a type's parts are `async` here, so a type nested to any
/// depth is decided with no more of the thread's stack than a shallow one; those that start a
/// frame of their own return a [`Deep`]: `empty`, `decide`, `rep`, `member_known`, `tuples` and
/// `morphisms`, through one of which every cycle of calls passes. The others are awaited in the
/// frame that calls them. Calls are made in the order of the recursive form, so the answers and
/// all that is recorded on the way are the same.
///
/// The async form, rather than an enum of frames per method, is used because the methods are
/// about thirty, mutually recursive, with recursive calls inside loops, short-circuiting
/// conditions and searches that restore the box after each piece: the compiler writes each
/// resume point and its saved locals, which a hand-written machine would list by hand at each
/// call, and the code keeps the shape of the recursion it replaces.
///
/// Complexity tradeoff: each frame is a boxed future and each borrow of the state a check of
/// the `RefCell`, a constant factor over the recursive form (1.2 to 2.5 times the time on
/// types 20,000 deep, measured against c277b594) for an O(depth) heap in place of the thread's
/// stack; the order of the work is unchanged.
struct Searching<'m> {
    stack: Stack<'m>,
    /// The search's state, borrowed by one statement at a time, never across an `await`, since
    /// the call awaited borrows it too.
    s: &'m RefCell<Search>,
}

/// What [`Searching::split_classes`] does with each piece of the box: decides it, or seeks a
/// value in it, the tuple part of length `len` cut to the piece.
enum Each<'a> {
    Decide {
        may_cover: bool,
    },
    Seek {
        len: usize,
        found: &'a mut Option<usize>,
    },
}

impl Search {
    /// Runs `root` and the calls it makes on a stack of their own, on this search's state.
    fn run<V: Unpin + 'static>(
        &mut self,
        root: impl for<'m> FnOnce(&'m Searching<'m>) -> Pin<Box<dyn Future<Output = V> + 'm>>,
    ) -> V {
        let s = RefCell::new(std::mem::take(self));
        let v = {
            let d = Searching {
                stack: Stack::default(),
                s: &s,
            };
            d.stack.run(root(&d))
        };
        *self = s.into_inner();
        v
    }

    /// Decides `root` ([`Searching::solve`]).
    fn solve(&mut self, root: &Type) -> bool {
        let root = root.clone();
        self.run(|d| Box::pin(async move { d.solve(&root).await }))
    }

    /// A value in `t`, if one is found ([`Searching::rep`]).
    fn rep(&mut self, t: &Type) -> Option<usize> {
        let t = t.clone();
        self.run(|d| Box::pin(d.rep(&t)))
    }

    /// Drops every kept failure, between phases of a search, when no value is being built.
    fn forget_failures(&mut self) {
        self.reps.retain(|_, r| r.is_some());
        self.waiting.clear();
        self.read.clear();
    }

    /// The end of a phase of [`Searching::solve`], once each inhabited answer was tried for a
    /// value, `new` when one was found: the answer for the root, numbered `r`, when the phases
    /// are over, or none when another starts.
    fn end_phase(&mut self, open: Vec<usize>, new: bool, r: usize) -> Option<bool> {
        if !self.again.is_empty() {
            return None;
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
            self.forget_failures();
            return None;
        }
        if !new {
            return Some(self.answer[r]);
        }
        for t in open {
            if !self.witnessed.contains(&t) {
                self.answer[t] = true;
                self.again.insert(t);
            }
        }
        if self.again.is_empty() {
            return Some(self.answer[r]);
        }
        None
    }

    /// Notes the first place a part counted as inhabited with nothing shown.
    fn give_up(&mut self, r: Refusal) {
        self.give_ups += 1;
        if self.strict {
            self.gave_up.get_or_insert(r);
        }
    }

    /// The answer for `t` when it is known: a type met before in this search, read by the type
    /// being decided, or one kept from an earlier search. Otherwise `t` is numbered, read by the
    /// type being decided and marked as being decided itself, and its number is given.
    fn met(&mut self, t: &Type) -> ControlFlow<bool, usize> {
        if let Some(&i) = self.ids.get(t) {
            if let Some(c) = self.current
                && self.readers[i].insert(c)
            {
                self.reads[c].push(i);
            }
            return ControlFlow::Break(self.answer[i]);
        }
        if !self.strict
            && let Some(b) = MEMO.with(|m| m.borrow().get(t).copied())
        {
            return ControlFlow::Break(b);
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
        ControlFlow::Continue(i)
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

    /// Keeps `v` among the values shown, and gives its number.
    fn show(&mut self, v: Rep) -> usize {
        self.shown.push(v);
        self.shown.len() - 1
    }

    /// Component `i` of the tuple numbered `v` among the values shown.
    fn tuple_item(&self, v: usize, i: usize) -> usize {
        match &self.shown[v] {
            Rep::Tuple(vs) => vs[i],
            _ => unreachable!("the value numbered {v} is read as a tuple and is not one"),
        }
    }

    /// The stop atom, link atom and length of the list numbered `v` among the values shown.
    fn list_parts(&self, v: usize) -> (&std::sync::Arc<str>, &std::sync::Arc<str>, &BigUint) {
        match &self.shown[v] {
            Rep::List {
                stop, link, len, ..
            } => (stop, link, len),
            _ => unreachable!("the value numbered {v} is read as a list and is not one"),
        }
    }
}

impl<'m> Searching<'m> {
    /// The search's state, for one statement or a scope with no `await` in it.
    fn s(&self) -> RefMut<'m, Search> {
        self.s.borrow_mut()
    }

    /// Decides `root`: phases, in each of which an answer only goes from empty to inhabited;
    /// at the end of a phase each inhabited answer is tried for a checked value, and if a new one
    /// is found the answers without one start again from empty, so a wrong "inhabited" read by
    /// another decision is undone. The last phase gives the answer.
    async fn solve(&'m self, root: &Type) -> bool {
        // A value built from the tuple types as written answers at once, and no box is split.
        // Answers read on the way are unfinished, so none is kept. A type with no atoms has no
        // list to walk, and a row tested against every row would cost their square.
        if !root.p().atoms.names.is_empty() {
            self.s().seeding = true;
            let seed = self.rep(root).await.is_some();
            let mut s = self.s();
            s.seeding = false;
            if seed {
                s.types.clear();
                s.answer.clear();
                return false;
            }
            s.forget_failures();
        }
        self.s().walking = true;
        let b = self.empty(root).await;
        self.s().walking = false;
        let Some(r) = self.s().ids.get(root).copied() else {
            return b;
        };
        loop {
            self.drain().await;
            let open: Vec<usize> = {
                let mut s = self.s();
                let open = (0..s.types.len())
                    .filter(|&t| !s.answer[t] && !s.witnessed.contains(&t))
                    .collect();
                s.forget_failures();
                open
            };
            let mut new = false;
            for &t in &open {
                let x = self.s().types[t].clone();
                if self.rep(&x).await.is_some() {
                    self.s().witnessed.insert(t);
                    new = true;
                }
            }
            let keys = std::mem::take(&mut self.s().keys);
            for k in keys {
                if self.rep(&k).await.is_some() {
                    new = true;
                } else {
                    self.s().keys.insert(k);
                }
            }
            if let Some(b) = self.s().end_phase(open, new, r) {
                return b;
            }
        }
    }

    /// Decides again, in rounds, each type an answer it read has changed under.
    async fn drain(&'m self) {
        loop {
            let again = std::mem::take(&mut self.s().again);
            if again.is_empty() {
                return;
            }
            for t in again {
                let open = self.s().answer[t];
                if open {
                    self.decide(t).await;
                }
            }
        }
    }

    /// Decides the type numbered `t` on a frame of its own.
    fn decide(&'m self, t: usize) -> Deep<'m, bool> {
        self.stack.call(move || self.decided(t))
    }

    async fn decided(&'m self, t: usize) -> bool {
        if self.s().refused.is_some() {
            return true;
        }
        let (outer, ty) = {
            let mut s = self.s();
            (s.current.replace(t), s.types[t].clone())
        };
        let b = match self.pure_cycles(&ty).await {
            Some(Lengths::None) => true,
            Some(Lengths::Some) => {
                self.s().witnessed.insert(t);
                false
            }
            Some(Lengths::Refused) => {
                // Complexity tradeoff: the lengths whose emptiness only a split on two or more
                // primes at once decides are refused (counted inhabited by `is_empty`), so the
                // work stays polynomial in the residue classes. Why: whether residue classes
                // cover the lengths is the covering problem for residues, NP-hard. Trigger:
                // `residues_meet` answers `Refused`. Tests:
                // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`erdos_cover`) and
                // `covering_residues_are_decided_by_a_split_on_one_prime`. COMPLEXITY.md K34 and
                // the Kept row "emptiness and subtyping of tuple and morphism parts". A complete
                // solution needs a backtracking split over several primes at once, exponential in
                // the primes, or a SAT encoding of the cover.
                self.s().give_up(Refusal::Residues);
                false
            }
            None => self.parts(ty.p()).await,
        };
        let mut guard = self.s();
        let s = &mut *guard;
        s.current = outer;
        if !b {
            s.answer[t] = false;
            s.again.extend(s.readers[t].iter().copied());
        }
        b
    }

    fn empty(&'m self, t: &Type) -> Deep<'m, bool> {
        // A member of a recursive group is answered by the group's decider (module `rec`).
        if let Some(b) = t.judged() {
            return Stack::ready(b);
        }
        // A scalar in the type is a checked value, read off before the type is compared with
        // those met.
        let p = t.p();
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        if p.bools != 0 || lits.iter().any(|l| l.cofinite || !l.values.is_empty()) {
            return Stack::ready(false);
        }
        let i = match self.s().met(t) {
            ControlFlow::Break(b) => return Stack::ready(b),
            ControlFlow::Continue(i) => i,
        };
        self.stack.call(move || async move {
            let b = self.decided(i).await;
            self.s().deciding.remove(&i);
            b
        })
    }

    /// Whether one of `ts` is empty, tried in order up to the first that is.
    async fn any_empty(&'m self, ts: &[Type]) -> bool {
        for t in ts {
            if self.empty(t).await {
                return true;
            }
        }
        false
    }

    async fn parts(&'m self, p: &Parts) -> bool {
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        if p.bools != 0
            || lits.iter().any(|l| l.cofinite || !l.values.is_empty())
            || p.atoms.cofinite
        {
            return false;
        }
        for a in p.atoms.names.values() {
            if a.bare || !self.empty(&a.payload).await {
                return false;
            }
        }
        if p.structs || p.tuples.rest {
            return false;
        }
        for (len, b) in &p.tuples.lens {
            let empty = match b.union_rows() {
                // A union of rows is empty when each row has an empty column, and only then.
                Some(rows) => {
                    let mut all = true;
                    for a in &rows {
                        if !self.any_empty(a).await {
                            all = false;
                            break;
                        }
                    }
                    all
                }
                None => {
                    let g = self.region(vec![Type::top(); *len], b).await;
                    self.tuples(g, b.clone(), true).await.0
                }
            };
            if !empty {
                return false;
            }
        }
        match p.morphisms.union_rows() {
            // A union of morphism types is empty when each of them admits nothing.
            Some(rows) => {
                for a in &rows {
                    if !self.no_morphism(a).await {
                        return false;
                    }
                }
                true
            }
            None => {
                self.morphisms(
                    Morphism {
                        guarantee: Type::empty(),
                        permission: Type::top(),
                        value: Type::top(),
                    },
                    p.morphisms.clone(),
                    true,
                )
                .await
            }
        }
    }

    /// The region of the part `f` on the box `r`, each distinct type of each component tested
    /// once.
    async fn region(&'m self, r: Vec<Type>, f: &Part<Row>) -> Region {
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
                let missed = self.settles(&g.r[j], &cell.ty, true).await;
                if !missed && self.settles(&g.r[j], &cell.ty, false).await {
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
    /// compared directly, so no type is built for them. Each meet or difference is built once
    /// per pair of nodes and kept in `cuts`: the regions of one search test the same cell against
    /// the same component many times over, and a type built again is a node of its own, which
    /// `empty` then compares in full with the one kept.
    ///
    /// Complexity tradeoff: `cuts` is keyed by the operands' nodes, not by their contents. Keyed
    /// by contents, each hit on an operand equal to a kept one but built apart compared the two in
    /// full, and `n` shapes held together cost order `n^2` (47.6 times the instructions from 64 to
    /// 512 in `a_tuple_that_shapes_hold_only_together_is_checked_in_the_size_of_the_union`). Keyed
    /// by node, such an operand misses and its type is built again, as before the memo; what is
    /// given up is the hits on equal operands built apart. COMPLEXITY.md K51.
    async fn settles(&'m self, x: &Type, y: &Type, both: bool) -> bool {
        if let Some(b) = x.scalar_cell(y, both) {
            return b;
        }
        let key = (x.node_addr(), y.node_addr(), both);
        let t = self
            .s()
            .cuts
            .entry(key)
            .or_insert_with(|| {
                let t = if both { x & y } else { x - y };
                (x.clone(), y.clone(), t)
            })
            .2
            .clone();
        self.empty(&t).await
    }

    /// Tests each changed component of the box against its open cells that have a tuple type
    /// not yet known to miss the box, and closes those it settles. A tuple type that misses a
    /// component is out of the part, so whether it holds the others is not tested: every
    /// changed component is tested for cells that miss it before any is tested for cells that
    /// hold it, and a cell only such tuple types have is not tested. Tuple types the part no
    /// longer has are not looked up: that costs the size of the part at each call, more than
    /// the tests it saves.
    async fn retest(&'m self, g: &mut Region) {
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
                    let settled = self.settles(&g.r[j], &cell.ty, missed).await;
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
    async fn narrow_tuples(&'m self, g: &mut Region, f: &mut Part<Row>) -> bool {
        loop {
            if self.any_empty(&g.r).await {
                return true;
            }
            self.retest(g).await;
            // `f` stays exact. Its settled form holds every value of `f` and may hold more, so
            // it proves `f` empty and shows what `f` forces, but its `true` shows no tuple in `f`.
            *f = f.restrict(&|a| g.stand(a));
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let settled = f.settle();
            if settled.is_leaf() == Some(false) {
                return true;
            }
            let (taken, refused) = settled.forced();
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
                self.retest(g).await;
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
    /// Each piece is tried on the box and the box restored after; the box is given back with the
    /// answer.
    fn tuples(&'m self, mut g: Region, f: Part<Row>, may_cover: bool) -> Deep<'m, (bool, Region)> {
        self.stack.call(move || async move {
            let b = self.tuples_on(&mut g, f, may_cover).await;
            (b, g)
        })
    }

    /// [`Searching::tuples`] on the box `g`, decided on a frame of its own for each piece.
    async fn tuples_on(&'m self, g: &mut Region, mut f: Part<Row>, may_cover: bool) -> bool {
        loop {
            if self.narrow_tuples(g, &mut f).await {
                return true;
            }
            if f.is_leaf().is_some() {
                return false;
            }
            let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
            let forking = {
                let s = self.s();
                s.refuse_forks && !s.seeding
            };
            if forking && (0..g.r.len()).any(|j| g.forks(&open, j)) {
                // Complexity tradeoff: `verdict` refuses a part in which two open tuple types
                // differ in a recursive component on one box, instead of following both. Why:
                // following both is the subset construction, exponential in the recursive types;
                // `is_empty` goes on and counts what it cannot settle as inhabited. Trigger: a
                // component on which the open tuple types fork, outside seeding. Tests:
                // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`fork_empty`) and
                // `a_value_is_sought_before_a_refusal` (`fork`). COMPLEXITY.md K26 and the Kept
                // row "emptiness and subtyping of tuple and morphism parts". A complete solution
                // needs the subset construction over the forked rows (a tree automaton
                // determinized on demand), exponential in the rows of the fork.
                self.s().refused = Some(Refusal::Fork);
                return true;
            }
            if let Some(found) = self.two_sat(g, &f).await {
                return found.is_none();
            }
            if let Some((j, classes)) = classes(g, &open) {
                let mut each = Each::Decide { may_cover };
                return self.split_classes(g, &f, j, &classes, &mut each).await;
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
                let mut ok = true;
                for c in g.open_cells(j, &open) {
                    let c = &g.cells[j][c].ty & &g.r[j];
                    if cells.contains(&c) {
                        continue;
                    }
                    if !self.empty(&(&c & &union)).await {
                        ok = false;
                        break;
                    }
                    union = &union | &c;
                    cells.insert(c);
                }
                if !ok {
                    continue;
                }
                let rest = &g.r[j] - &union;
                if !self.empty(&rest).await {
                    cells.insert(rest);
                }
                for c in cells {
                    let mark = g.log.len();
                    g.shrink(j, c);
                    let (b, back) = self.tuples(std::mem::take(g), f.clone(), may_cover).await;
                    *g = back;
                    g.restore(mark);
                    if !b {
                        return false;
                    }
                }
                return true;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                for &k in &open {
                    let mark = g.log.len();
                    for j in 0..g.r.len() {
                        if g.is_open(k, j) {
                            let t = &g.r[j] & &g.atoms[k][j];
                            g.shrink(j, t);
                            g.close(j, g.cell(k, j), false);
                        }
                    }
                    let (b, back) = self.tuples(std::mem::take(g), f.clone(), false).await;
                    *g = back;
                    g.restore(mark);
                    if !b {
                        return false;
                    }
                }
                return true;
            }
            let mut narrowed = false;
            for j in 0..g.r.len() {
                let mut tried = BTreeSet::new();
                // A cell closed on the component misses or holds it, so its pieces are the
                // component and nothing, and narrow nothing.
                for cell in g.open_cells(j, &open) {
                    let a = &g.cells[j][cell].ty;
                    for c in [a & &g.r[j], &g.r[j] - a] {
                        if tried.contains(&c)
                            || self.empty(&c).await
                            || self.empty(&(&g.r[j] - &c)).await
                        {
                            continue;
                        }
                        tried.insert(c.clone());
                        let mark = g.log.len();
                        g.shrink(j, c.clone());
                        let hit = self.narrow_tuples(g, &mut f.clone()).await;
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
            // Complexity tradeoff: a tuple part that neither narrowing, nor the split by class,
            // nor one split per branch into its open tuple types, nor one cut of a component
            // decides counts as inhabited for `is_empty`, and `verdict` answers
            // `Refused(TupleSplit)` unless `Searching::refine` finds a value first; the checker
            // adds the cause to the rejection. Why: emptiness of Boolean combinations of tuple
            // types is coNP-hard (a cover of the box by tuple types is a DNF tautology), and one
            // split per branch keeps the search polynomial. Trigger: a part that only a split of
            // the box in two or more components at once proves empty. Tests:
            // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`box_cover`),
            // `a_call_whose_check_was_refused_says_why` and
            // `l01_23_subtyping::scaling::a_type_not_proved_empty_promises_no_key`. COMPLEXITY.md
            // K2 and the Kept row "emptiness and subtyping of tuple and morphism parts". A
            // complete solution needs a split of the box in every component (a DPLL search over
            // the tuple types, exponential in them), or a SAT encoding.
            self.s().give_up(Refusal::TupleSplit);
            return false;
        }
    }

    /// Whether no tuple in the box of `g` is in `f`, the box split on component `j` into the
    /// piece of each class, the meet of the component with its cells, and the rest, which no
    /// class's cells meet. On the piece of a class, a tuple type with a cell of another class
    /// misses the box, and on the rest every tuple type of a class does, so they are taken out
    /// of `f` before the piece is decided on a box of its own. The classes are halved at each
    /// step and each half takes the other's tuple types out, so each tuple type stays in the
    /// part of O(log k) of the k pieces, and the part is restricted O(log k) times over. Each
    /// piece's box holds in component `j` only the values of its own class, so a test of a cell
    /// against it costs the size of the class, not of the component. `each` is done with the box
    /// and the part of each piece whose part is not `false`, and answers whether to go on.
    /// The halves are walked on a stack of their own, the lower half first, each restricted
    /// when it is reached.
    async fn split_classes(
        &'m self,
        g: &Region,
        f: &Part<Row>,
        j: usize,
        classes: &[Class],
        each: &mut Each<'_>,
    ) -> bool {
        let class_of: BTreeMap<usize, usize> = (classes.iter().enumerate())
            .flat_map(|(i, (_, ks))| ks.iter().map(move |&k| (k, i)))
            .collect();
        let at = |a: &Row| class_of.get(&g.index[a]).copied();
        let met = Type::union_all(classes.iter().map(|(c, _)| c.clone()));
        let rest = &g.r[j] - &met;
        if !self.empty(&rest).await {
            let f = f.restrict(&|a| at(a).map(|_| false));
            let mut r = g.r.clone();
            r[j] = rest;
            if f.is_leaf() != Some(false) && !self.each(each, r, f).await {
                return false;
            }
        }
        // Each entry: the part of the halves above, the classes of this half, and those of the
        // other half, whose tuple types this half takes out of the part (none at the top).
        let mut halves = vec![(f.clone(), 0..classes.len(), None::<Range<usize>>)];
        while let Some((f, this, other)) = halves.pop() {
            let f = match other {
                None => f,
                Some(other) => {
                    let f = f.restrict(&|a| at(a).filter(|i| other.contains(i)).map(|_| false));
                    if f.is_leaf() == Some(false) {
                        continue;
                    }
                    f
                }
            };
            if this.len() == 1 {
                let mut r = g.r.clone();
                r[j] = &r[j] & &classes[this.start].0;
                if f.is_leaf() != Some(false) && !self.each(each, r, f).await {
                    return false;
                }
                continue;
            }
            let m = this.start + this.len() / 2;
            let (lo, hi) = (this.start..m, m..this.end);
            halves.push((f.clone(), hi.clone(), Some(lo.clone())));
            halves.push((f, lo, Some(hi)));
        }
        true
    }

    /// Does `each` with the piece of the box `r` and its part `f`, and answers whether to go on.
    async fn each(&'m self, each: &mut Each<'_>, r: Vec<Type>, f: Part<Row>) -> bool {
        match each {
            Each::Decide { may_cover } => self.piece(r, f, *may_cover).await,
            Each::Seek { len, found } => {
                let piece = &Type::tuple(r)
                    & &Type::with(|p| {
                        p.tuples.lens.insert(*len, f);
                    });
                **found = self.rep(&piece).await;
                found.is_none()
            }
        }
    }

    /// The tuple part `f` on the box of `g`, narrowed, decided as a 2-CNF when it is one by its
    /// structure (step T6-2sat): each open tuple type is open on one component alone, so it is
    /// a literal of that component; the open tuple types of one component cut it into the same
    /// two pieces, each the cell of one of them or its complement in the component, so the
    /// component is a variable (a finite Boolean component, the values `0` and `1`, is one);
    /// and the part read over those literals is a 2-CNF ([`read_two_sat`]). The components are
    /// independent, so a tuple of the box is in `f` exactly when its pieces solve the 2-CNF,
    /// and [`TwoSat::solve`] decides it in time linear in the part. `None` when the part is not
    /// of that structure; `Some(None)` when no tuple of the box is in `f`; else the box with
    /// each variable's component cut to the piece the solution chooses, all of whose tuples
    /// are in `f`. Each cell is compared with its component's pieces once.
    async fn two_sat(&'m self, g: &Region, f: &Part<Row>) -> Option<Option<Vec<Type>>> {
        // For each component cut, its variable, the piece its literal `true` stands for, and
        // the rest of the component.
        let mut cut: BTreeMap<usize, (usize, Type, Type)> = BTreeMap::new();
        let mut cells: BTreeMap<(usize, usize), Literal2> = BTreeMap::new();
        let mut literals: Vec<Option<Literal2>> = vec![None; g.atoms.len()];
        for a in f.distinct_atoms() {
            let k = g.index[&a];
            let (loose, j) = g.loose[k];
            if g.missed[k] != 0 || loose != 1 {
                return None;
            }
            let c = g.cell(k, j);
            let l = match cells.get(&(j, c)) {
                Some(&l) => l,
                None => {
                    let ty = &g.cells[j][c].ty;
                    let l = match cut.get(&j) {
                        None => {
                            let (v, piece) = (cut.len(), &g.r[j] & ty);
                            let rest = &g.r[j] - &piece;
                            cut.insert(j, (v, piece, rest));
                            2 * v
                        }
                        Some((v, piece, rest)) => {
                            if self.settles(piece, ty, false).await
                                && self.settles(rest, ty, true).await
                            {
                                2 * v
                            } else if self.settles(piece, ty, true).await
                                && self.settles(rest, ty, false).await
                            {
                                2 * v + 1
                            } else {
                                return None;
                            }
                        }
                    };
                    cells.insert((j, c), l);
                    l
                }
            };
            literals[k] = Some(l);
        }
        // Complexity tradeoff: a part with a clause of three or more literals, or a tuple type
        // open on two components, is no 2-CNF and goes on to the search below, as before this
        // step; deciding it is NP-complete in general (pigeonhole is one), so no linear method
        // covers it, and the search may refuse it. Test:
        // `l01_23_subtyping::two_sat::pigeonhole_is_left_to_the_search`; COMPLEXITY.md K54. A
        // complete solution needs a SAT procedure, exponential in the variables in the worst case.
        let s = read_two_sat(f, cut.len(), &|a| literals[g.index[a]])?;
        let Some(values) = s.solve() else {
            return Some(None);
        };
        let mut r = g.r.clone();
        for (j, (v, piece, rest)) in cut {
            r[j] = if values[v] { piece } else { rest };
        }
        Some(Some(r))
    }

    /// Whether no tuple in the box `r` is in `f`, decided on a region of its own.
    async fn piece(&'m self, r: Vec<Type>, f: Part<Row>, may_cover: bool) -> bool {
        if f.is_leaf() == Some(false) {
            return true;
        }
        let h = self.region(r, &f).await;
        self.tuples(h, f, may_cover).await.0
    }

    /// Whether `m` admits no morphism: a key is promised and not permitted, or promised and no
    /// value can be its. A key is promised only when a value is shown in the type: a type not
    /// proved empty may still be empty, and then the empty morphism is admitted.
    async fn no_morphism(&'m self, m: &Morphism) -> bool {
        self.shown_key(&(&m.guarantee - &m.permission)).await
            || (self.shown_key(&m.guarantee).await && self.no_value(&m.value).await)
    }

    /// Whether a value is shown in `k`. A type with none yet is tried again after each
    /// phase, since a value found later changes what was read.
    async fn shown_key(&'m self, k: &Type) -> bool {
        let b = self.rep(k).await.is_some();
        if !b {
            self.s().keys.insert(k.clone());
        }
        b
    }

    /// Whether no value is in `v`, the value type of a morphism. A value is finite but a closure
    /// may return itself, so a cycle through a morphism proves nothing: a value type counts as
    /// inhabited here until it is empty with all such reads inhabited. That is the greatest
    /// fixed point on these reads over the least on the others. A type whose decision read
    /// nothing still being decided is settled at once, so a nest of morphisms takes one round.
    async fn no_value(&'m self, v: &Type) -> bool {
        let b = self.empty(v).await;
        let Some(i) = self.s().ids.get(v).copied() else {
            return b;
        };
        let walking = {
            let s = self.s();
            b && s.walking && !s.deciding.contains(&i)
        };
        if walking {
            self.s().walking = false;
            self.drain().await;
            let mut s = self.s();
            s.walking = true;
            if s.answer[i] {
                s.settle(i);
            }
        }
        let mut s = self.s();
        s.value_reads.insert(i);
        s.dead.contains(&i)
    }

    /// The meet of pure cycles that `t` is, when `t` is a stop atom or not, and a link atom
    /// whose rest is the meet of pure cycles less at most one, all of one item.
    async fn cycle_meet(&'m self, t: &Type) -> Option<Meet> {
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
        let mut all = Vec::with_capacity(taken.len());
        let mut none = Vec::with_capacity(refused.len());
        {
            let mut s = self.s();
            let mut read = |s: &mut Search, a: &Row| -> Option<(u64, u64)> {
                let c = s.cycle(&a[1])?;
                let fits = a[0] == item && c.item == item && c.link == name;
                let same = stop.get_or_insert_with(|| c.stop.clone()) == &c.stop;
                // A length one more than a length of the rest.
                (fits && same).then_some((c.period, (c.at + 1) % c.period))
            };
            for a in &taken {
                all.push(read(&mut s, a)?);
            }
            for a in &refused {
                none.push(read(&mut s, a)?);
            }
        }
        if self.empty(&item).await {
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
    async fn pure_cycles(&'m self, t: &Type) -> Option<Lengths> {
        let m = self.cycle_meet(t).await?;
        Some(match m.bare {
            true => Lengths::Some,
            false => residues_meet(&m.all, &m.none),
        })
    }

    /// A list of `m`, of the length `residue_length` gives, kept as that length: the work is
    /// that of the rule on residues, polynomial in the cycles, whatever the length.
    async fn cycle_rep(&'m self, m: &Meet) -> Option<usize> {
        let len = residue_length(&m.all, &m.none)?;
        let item = self.rep(&m.item).await?;
        Some(self.s().show(Rep::List {
            stop: m.stop.clone(),
            link: m.link.clone(),
            item,
            len,
        }))
    }

    /// Whether the list numbered `v` among the values shown, of `len` links of the item
    /// numbered `item`, ending in `stop`, is in `u`; `None` when that is not known. The walk
    /// follows the rest type link by link; at a meet of pure cycles of the same atoms the rule
    /// on residues answers at once, and a rest type met again cuts the length left to its
    /// remainder modulo the steps between, so no type is walked twice and the length is never
    /// walked.
    async fn list_member(&'m self, v: usize, item: usize, u: &Type) -> Option<bool> {
        let (mut x, mut left) = (u.clone(), self.s().list_parts(v).2.clone());
        let mut seen: BTreeMap<Type, BigUint> = BTreeMap::new();
        loop {
            if left == BigUint::ZERO {
                return Some(x.contains(&Value::atom(self.s().list_parts(v).0)));
            }
            if let Some(m) = self.cycle_meet(&x).await {
                let same = {
                    let s = self.s();
                    let (stop, link, _) = s.list_parts(v);
                    m.link == *link && m.stop == *stop
                };
                if same {
                    let fits = m.all.iter().all(|&(p, at)| &left % p == BigUint::from(at))
                        && m.none.iter().all(|&(p, at)| &left % p != BigUint::from(at));
                    return Some(fits && self.member(item, &m.item).await);
                }
            }
            if let Some(before) = seen.insert(x.clone(), left.clone()) {
                // `x` again after `before - left` links: the rest of each length is in `x`
                // exactly when the rest that many links shorter is.
                left %= before - &left;
                seen.clear();
                continue;
            }
            let p = x.p();
            let Some(a) = p.atoms.names.get(self.s().list_parts(v).1) else {
                return Some(p.atoms.cofinite);
            };
            let f = a.payload.p().tuples.get(2);
            if f.is_leaf() == Some(true) {
                return Some(true);
            }
            // The rest types of the rows whose item type holds the item; the rest is in `x`
            // exactly when it is in one of them.
            let mut next: Option<Type> = None;
            for row in f.union_rows()? {
                if self.member(item, &row[0]).await {
                    match &next {
                        None => next = Some(row[1].clone()),
                        Some(y) if *y == row[1] => {}
                        // Complexity tradeoff: two rest types to follow would make the walk a
                        // set of types per link, and the sets met before one repeats can be
                        // as many as the lcm of the cycles they pass through, exponential in
                        // them; so the membership is not known and the list is not shown as a
                        // value of this type (a value is sought elsewhere, or the verdict is
                        // `Refused(NoWitness)`). The trigger is a union of list types whose
                        // rows hold the same item and differ in the rest. Test:
                        // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length`;
                        // COMPLEXITY.md K34. A complete solution would give each type its set of
                        // lengths as residues and combine them, which is the covering problem
                        // for residues when a negation is met.
                        Some(_) => return None,
                    }
                }
            }
            let Some(y) = next else {
                return Some(false);
            };
            x = y;
            left -= 1u32;
        }
    }

    /// A value in `t`, if one is found: a scalar or bare atom of it, or a tuple or atom payload
    /// whose components have representatives and which `t` holds. The tuples tried at each
    /// length are two: the box the tuple types narrow the part to, and its meet with the first
    /// tuple type left open; each is tested against every tuple type of `t`, so a poor choice
    /// costs precision, never soundness. A type met again while its own is sought has none on
    /// that path, since a value is finite; none found means only that, never that `t` is
    /// empty. A value found is kept for good. A failure is kept with the types whose missing
    /// values it read, and is sought again when one of them gets a value ([`Searching::retry`]),
    /// so a type is tried again once a type its value needs has one: the value of a member of a
    /// chain whose next member was being built when it was first tried. Each test of a
    /// representative against a type is made once, so a value nested in shared types is never
    /// copied out.
    fn rep(&'m self, t: &Type) -> Deep<'m, Option<usize>> {
        {
            let mut s = self.s();
            if let Some(&r) = s.reps.get(t) {
                if r.is_none() {
                    s.read.push(t.clone());
                }
                return Stack::ready(r);
            }
        }
        let t = t.clone();
        self.stack.call(move || async move {
            let (mark, resting, outer) = {
                let mut s = self.s();
                s.reps.insert(t.clone(), None);
                s.building.insert(t.clone());
                (s.built.len(), s.resting, std::mem::take(&mut s.read))
            };
            let r = self.find_rep(&t).await;
            let again = {
                let mut s = self.s();
                s.building.remove(&t);
                s.reps.insert(t.clone(), r);
                let read = std::mem::replace(&mut s.read, outer);
                if r.is_none() {
                    if s.resting > resting {
                        // What was built here rests on a value that does not exist.
                        for x in s.built.split_off(mark) {
                            s.reps.remove(&x);
                        }
                    }
                    // A type read while it had no value, which got one before this build ended:
                    // its retry has passed, so this build is sought again now.
                    let again =
                        (read.iter()).any(|x| *x != t && matches!(s.reps.get(x), Some(Some(_))));
                    if again {
                        s.reps.remove(&t);
                    } else {
                        for x in read.into_iter().filter(|x| *x != t) {
                            s.waiting.entry(x).or_default().push(t.clone());
                        }
                        s.read.push(t.clone());
                    }
                    Some(again)
                } else {
                    s.built.push(t.clone());
                    None
                }
            };
            match again {
                Some(true) => return self.rep(&t).await,
                Some(false) => return r,
                None => {}
            }
            self.retry(&t).await;
            r
        })
    }

    /// Seeks again, at once, each kept failure that read the missing value of `t`, which now
    /// has one: a failure sought again that finds a value does the same for those that read
    /// it, so values spread back as in a worklist, and each failure is sought again once for
    /// each type it read that gets a value.
    async fn retry(&'m self, t: &Type) {
        let waiting = self.s().waiting.remove(t).unwrap_or_default();
        for y in waiting {
            let outer = {
                let mut s = self.s();
                if s.reps.get(&y) != Some(&None) || s.building.contains(&y) {
                    continue;
                }
                s.reps.remove(&y);
                std::mem::take(&mut s.read)
            };
            // Read by no build under way: what it reads is its own.
            self.rep(&y).await;
            self.s().read = outer;
        }
    }

    /// The representatives of `ts`, if each has one, sought in order up to the first that has
    /// none.
    async fn reps(&'m self, ts: &[Type]) -> Option<Vec<usize>> {
        let mut vs = Vec::with_capacity(ts.len());
        for x in ts {
            vs.push(self.rep(x).await?);
        }
        Some(vs)
    }

    /// Whether a closure can return a value of `v`: one built here, one being built (the closure
    /// may be part of it), or one its group decided `v` has, which the closure, never called
    /// here, does not need built.
    async fn returnable(&'m self, v: &Type) -> bool {
        if v.judged() == Some(false) {
            return true;
        }
        {
            let mut s = self.s();
            if s.building.contains(v) {
                s.resting += 1;
                return true;
            }
        }
        self.rep(v).await.is_some()
    }

    /// The representatives of the row, if each component has one, when they make a tuple of `f`.
    async fn row_rep(&'m self, row: &[Type], f: &Part<Row>) -> Option<usize> {
        let vs = self.reps(row).await?;
        if !self.holds(&vs, f).await {
            return None;
        }
        Some(self.s().show(Rep::Tuple(vs)))
    }

    async fn find_rep(&'m self, t: &Type) -> Option<usize> {
        // A bare atom is a value: the empty list of a list type.
        if let Some(name) = t
            .p()
            .atoms
            .names
            .iter()
            .find_map(|(n, a)| a.bare.then_some(n))
        {
            return Some(self.s().show(Rep::Value(Value::atom(name))));
        }
        // A list of pure cycles with no stop in it: a list of it, kept as its length.
        if let Some(m) = self.cycle_meet(t).await {
            return self.cycle_rep(&m).await;
        }
        let p = t.p();
        if p.bools != 0 {
            return Some(self.s().show(Rep::Value(Value::Bool(p.bools & 1 == 0))));
        }
        // A cofinite set of a carrier holds one of the first values not listed in it.
        type Fresh = fn(i64) -> Value;
        let fresh: [(&Lits, Fresh); 4] = [
            (&p.ints, Value::Int),
            (&p.strings, |i| Value::str(&i.to_string())),
            (&p.rats, |i| Value::rat(crate::Rat::int(i.into()))),
            (&p.floats, |i| Value::float(i as f64)),
        ];
        for (l, make) in fresh {
            let v = if l.cofinite {
                (0..).map(make).find(|v| !l.values.contains(v))
            } else {
                l.values.iter().next().cloned()
            };
            if let Some(v) = v {
                return Some(self.s().show(Rep::Value(v)));
            }
        }
        if p.atoms.cofinite {
            let name = (0..)
                .map(|i| format!("a{i}"))
                .find(|n| !p.atoms.names.contains_key(n.as_str()));
            let name = name.expect("a name is free");
            return Some(self.s().show(Rep::Value(Value::atom(&name))));
        }
        for (name, a) in &p.atoms.names {
            if a.bare {
                return Some(self.s().show(Rep::Value(Value::atom(name))));
            }
            if let Some(r) = self.rep(&a.payload).await {
                let tuple = matches!(self.s().shown[r], Rep::Tuple(_));
                if tuple {
                    return Some(self.s().show(Rep::Atom(name.clone(), r)));
                }
            }
        }
        if p.structs {
            return Some(self.s().show(Rep::Struct));
        }
        if p.morphisms.is_leaf() != Some(false) {
            let top = Morphism {
                guarantee: Type::empty(),
                permission: Type::top(),
                value: Type::top(),
            };
            // A closure is shown only for a meet of morphism types whose keys are all
            // permitted as written and whose value type has a value, which may be one being
            // built here, holding this closure: a closure can return itself. A closure whose
            // keys are known empty is shown for any value type, since it is never called. The
            // keys of a meet are the union of its morphism types' keys, so they are empty when
            // each of those is; each is read as written, since a recursive type and its
            // unfolding are compared as different types. A meet of one morphism type is that type
            // as written: its meet with the top one would give the unfolding of a recursive value
            // type, which is neither the type being built nor one its group decided.
            let (taken, refused) = p.morphisms.forced();
            let whole = refused.is_empty() && taken.len() == p.morphisms.distinct_atoms().len();
            let meets: Vec<(Morphism, bool)> = match (whole, p.morphisms.union_rows()) {
                (true, _) => vec![(
                    match taken.split_first() {
                        Some((a, rest)) => rest.iter().fold(a.clone(), |r, b| meet(&r, b)),
                        None => top,
                    },
                    taken.iter().all(|a| known_empty(&a.guarantee)),
                )],
                (false, Some(rows)) => (rows.into_iter())
                    .map(|m| {
                        let keyless = known_empty(&m.guarantee);
                        (m, keyless)
                    })
                    .collect(),
                (false, None) => Vec::new(),
            };
            for (m, keyless) in &meets {
                if *keyless {
                    return Some(self.s().show(Rep::Closure));
                }
                let permitted = m.guarantee == m.permission
                    || m.guarantee == Type::empty()
                    || m.permission == Type::top();
                if !permitted {
                    continue;
                }
                // What the closure returns may hold the closure, at any depth.
                let mark = {
                    let mut s = self.s();
                    let mark = s.built.len();
                    let closure = s.show(Rep::Closure);
                    s.reps.insert(t.clone(), Some(closure));
                    mark
                };
                let returns = self.returnable(&m.value).await;
                let mut s = self.s();
                s.reps.insert(t.clone(), None);
                if returns {
                    return Some(s.show(Rep::Closure));
                }
                for x in s.built.split_off(mark) {
                    s.reps.remove(&x);
                }
            }
        }
        if p.tuples.rest {
            let len = (0..)
                .find(|n| !p.tuples.lens.contains_key(n))
                .expect("a length is free");
            let vs = self.reps(&vec![Type::top(); len]).await?;
            return Some(self.s().show(Rep::Tuple(vs)));
        }
        for f in p.tuples.lens.values() {
            for row in f.union_rows().unwrap_or_default() {
                if let Some(vs) = self.reps(&row).await {
                    return Some(self.s().show(Rep::Tuple(vs)));
                }
            }
        }
        if self.s().seeding {
            for f in p.tuples.lens.values() {
                for row in f.distinct_atoms() {
                    if let Some(v) = self.row_rep(&row, f).await {
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
            let (mut b, mut g) = (self.region(vec![Type::top(); *len], f).await, f.clone());
            if self.narrow_tuples(&mut b, &mut g).await {
                continue;
            }
            if let Some(v) = self.row_rep(&b.r, f).await {
                return Some(v);
            }
            // A 2-CNF's solution, checked as any candidate is.
            match self.two_sat(&b, &g).await {
                Some(None) => continue,
                Some(Some(row)) => {
                    if let Some(v) = self.row_rep(&row, f).await {
                        return Some(v);
                    }
                }
                None => {}
            }
            if let Some(found) = self.class_rep(&b, &g, *len).await {
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
                let row = (!self.narrow_tuples(&mut b, &mut h).await).then(|| b.r.clone());
                b.restore(mark);
                if let Some(r) = row
                    && let Some(v) = self.row_rep(&r, f).await
                {
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
                if let Some(v) = self.row_rep(&row, f).await {
                    return Some(v);
                }
            }
            if let Some(row) = self.refine(*len, f).await
                && let Some(v) = self.row_rep(&row, f).await
            {
                return Some(v);
            }
        }
        None
    }

    /// A value of the tuple part `g` of length `len` on the box of `b`, sought piece by piece
    /// when the open tuple types fall into classes on a component: on the pieces of
    /// [`Searching::split_classes`], the rest, which no class meets, then one piece per class,
    /// each a type of its own whose box holds only its class in that component. Nothing when
    /// there are no such classes; `Some(None)` when no piece has a value found.
    async fn class_rep(&'m self, b: &Region, g: &Part<Row>, len: usize) -> Option<Option<usize>> {
        let open: Vec<usize> = g.distinct_atoms().iter().map(|a| b.index[a]).collect();
        let (j, classes) = classes(b, &open)?;
        let mut found = None;
        let mut each = Each::Seek {
            len,
            found: &mut found,
        };
        self.split_classes(b, g, j, &classes, &mut each).await;
        Some(found)
    }

    /// A box within the tuple part `f` of length `len`, found by splitting each component, one
    /// tuple type at a time, into the piece inside that tuple type and the piece outside it,
    /// and keeping a piece the search shows inhabited, else one it does not prove empty. Each
    /// step is at most two searches, so the searches are at most twice the tuple types times
    /// the components, and the box ends closed on every tuple type: the part then holds all of
    /// it or none.
    async fn refine(&'m self, len: usize, f: &Part<Row>) -> Option<Vec<Type>> {
        let refuse_forks = std::mem::replace(&mut self.s().refuse_forks, false);
        let mut g = self.region(vec![Type::top(); len], f).await;
        let mut h = f.clone();
        let mut empty = self.narrow_tuples(&mut g, &mut h).await;
        for j in 0..len {
            for k in 0..g.atoms.len() {
                if empty || !g.is_open(k, j) {
                    continue;
                }
                let inside = &g.r[j] & &g.atoms[k][j];
                let outside = &g.r[j] - &g.atoms[k][j];
                let piece = match self.try_piece(&mut g, &h, j, &inside).await {
                    (true, _) => outside,
                    (_, true) => inside,
                    _ => match self.try_piece(&mut g, &h, j, &outside).await {
                        (false, true) => outside,
                        _ => inside,
                    },
                };
                g.shrink(j, piece);
                empty = self.narrow_tuples(&mut g, &mut h).await;
            }
        }
        self.s().refuse_forks = refuse_forks;
        (!empty && h.is_leaf() == Some(true)).then_some(g.r)
    }

    /// For [`Searching::refine`]: whether the search proves the box `g` with component `j` cut
    /// to `piece` empty for the part `h`, and whether it shows it inhabited.
    async fn try_piece(
        &'m self,
        g: &mut Region,
        h: &Part<Row>,
        j: usize,
        piece: &Type,
    ) -> (bool, bool) {
        let (mark, give_ups) = (g.log.len(), self.s().give_ups);
        g.shrink(j, piece.clone());
        let (none, back) = self.tuples(std::mem::take(g), h.clone(), true).await;
        *g = back;
        g.restore(mark);
        (none, !none && self.s().give_ups == give_ups)
    }

    /// Whether the tuple `vs` is in `f`; false when that is not known.
    async fn holds(&'m self, vs: &[usize], f: &Part<Row>) -> bool {
        self.holds_known(|_, i| vs[i], f).await == Some(true)
    }

    /// Whether the tuple whose component `i` is the value numbered `item(search, i)` is in `f`;
    /// `None` when the membership of a component in a tuple type is not known, since `f` may
    /// hold that tuple type negated. A component is read by number when it is tested, so a
    /// tuple among the values shown is read in place while the tests add to the search.
    async fn holds_known(
        &'m self,
        item: impl Fn(&Search, usize) -> usize,
        f: &Part<Row>,
    ) -> Option<bool> {
        let outer = std::mem::take(&mut self.s().unsure);
        let mut fits = BTreeSet::new();
        for a in f.distinct_atoms() {
            let mut all = true;
            for (i, y) in a.iter().enumerate() {
                let v = item(&self.s(), i);
                if !self.member(v, y).await {
                    all = false;
                    break;
                }
            }
            if all {
                fits.insert(a);
            }
        }
        let b = f.eval(&|a| fits.contains(a));
        let unsure = std::mem::replace(&mut self.s().unsure, outer);
        (!unsure).then_some(b)
    }

    /// Whether the value numbered `v` is in `u`; false, with `unsure` set, when that is not
    /// known.
    async fn member(&'m self, v: usize, u: &Type) -> bool {
        let known = self.member_known(v, u).await;
        self.s().unsure |= known.is_none();
        known == Some(true)
    }

    /// Whether the value numbered `v` is in `u`, or `None` when that is not known. What is not
    /// known is kept as such, so a second test of the pair is not read as a sure "no".
    fn member_known(&'m self, v: usize, u: &Type) -> Deep<'m, Option<bool>> {
        {
            let s = self.s();
            if let Rep::Value(x) = &s.shown[v] {
                return Stack::ready(Some(u.contains(x)));
            }
        }
        let key = (v, u.clone());
        if let Some(&b) = self.s().members.get(&key) {
            return Stack::ready(b);
        }
        self.stack.call(move || async move {
            let b = {
                let u = &key.1;
                // What the value is, read before any test that adds to the values shown.
                enum Shape<'u> {
                    Known(Option<bool>),
                    Tuple(Part<Row>),
                    Payload(usize, &'u Type),
                    List(usize),
                }
                let shape = match &self.s().shown[v] {
                    Rep::Value(_) => unreachable!("a value was read above"),
                    Rep::Closure => Shape::Known(u.p().morphisms.is_leaf()),
                    Rep::Struct => Shape::Known(Some(u.p().structs)),
                    Rep::Tuple(vs) => Shape::Tuple(u.p().tuples.get(vs.len())),
                    Rep::Atom(name, payload) => match u.p().atoms.names.get(name) {
                        None => Shape::Known(Some(u.p().atoms.cofinite)),
                        Some(a) => Shape::Payload(*payload, &a.payload),
                    },
                    Rep::List { item, .. } => Shape::List(*item),
                };
                match shape {
                    Shape::Known(b) => b,
                    Shape::Tuple(f) => self.holds_known(|s, i| s.tuple_item(v, i), &f).await,
                    Shape::Payload(payload, a) => self.member_known(payload, a).await,
                    Shape::List(item) => self.list_member(v, item, u).await,
                }
            };
            self.s().members.insert(key, b);
            b
        })
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    async fn within(&'m self, m: &Morphism, n: &Morphism) -> bool {
        let no_value = self.no_value(&m.value).await;
        self.empty(&(&n.guarantee - &m.guarantee)).await
            && (no_value || self.empty(&(&m.permission - &n.permission)).await)
            && (no_value
                || self.empty(&m.permission).await
                || self.empty(&(&m.value - &n.value)).await)
    }

    /// Whether no morphism `r` admits is in `f`, decided as for tuples: `r` meets the morphism
    /// types in every value of `f`, and, once on each branch, when `f` holds nothing outside
    /// the open morphism types, each is decided on its own. Morphism types are closed under
    /// meet but not under difference, so a type in no value of `f` narrows nothing.
    fn morphisms(
        &'m self,
        mut r: Morphism,
        mut f: Part<Morphism>,
        may_cover: bool,
    ) -> Deep<'m, bool> {
        self.stack.call(move || async move {
            loop {
                if self.no_morphism(&r).await {
                    return true;
                }
                let mut st: BTreeMap<Morphism, Option<bool>> = BTreeMap::new();
                for a in f.distinct_atoms() {
                    let s = if self.no_morphism(&meet(&r, &a)).await {
                        Some(false)
                    } else if self.within(&r, &a).await {
                        Some(true)
                    } else {
                        None
                    };
                    st.insert(a, s);
                }
                // `f` stays exact, as in `narrow_tuples`: its settled form proves emptiness and
                // what is forced, but its `true` shows no morphism in `f`.
                f = f.restrict(&|a| st.get(a).copied().flatten());
                if let Some(b) = f.is_leaf() {
                    return !b;
                }
                let settled = f.settle();
                if settled.is_leaf() == Some(false) {
                    return true;
                }
                let (taken, _) = settled.forced();
                if !taken.is_empty() {
                    r = taken.iter().fold(r, |r, a| meet(&r, a));
                    continue;
                }
                if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                    for a in f.distinct_atoms().iter() {
                        if !self.morphisms(meet(&r, a), f.clone(), false).await {
                            return false;
                        }
                    }
                    return true;
                }
                // Complexity tradeoff: a morphism part that neither the meets it forces nor one
                // split into its morphism types decides is counted inhabited and refused by
                // `verdict`. Why: emptiness of Boolean combinations of morphism types is
                // coNP-hard, like that of tuple types, and one split per branch keeps the search
                // polynomial. Trigger: no atom is forced and the split was spent or does not
                // apply. Tests: `l01_23_subtyping::refusals::each_refusal_names_its_cause`
                // (`morphism_split`) and `a_morphism_type_whose_bound_check_was_refused_says_why`.
                // COMPLEXITY.md Kept row "emptiness and subtyping of tuple and morphism parts". A
                // complete solution needs a split of the guarantee, permission and value type in
                // every combination (exponential in the morphism types), or a SAT encoding.
                self.s().give_up(Refusal::MorphismSplit);
                return false;
            }
        })
    }
}

/// A literal of a 2-CNF: variable `v` true is `2 * v`, false is `2 * v + 1`, so `l ^ 1` is the
/// complement of `l`.
type Literal2 = usize;

/// A 2-CNF read from a tuple part (step T6-2sat): its variables, and its clauses, each one or
/// two literals (a clause of one literal holds it twice).
struct TwoSat {
    vars: usize,
    clauses: Vec<(Literal2, Literal2)>,
    /// The variable of each meet under an `or`, by the key of its node ([`At::key`]).
    meets: HashMap<(u64, bool, u8), Literal2>,
}

/// A node of a tuple part as [`read_two_sat`] meets it: a part, a diagram, or one arm of a
/// diagram node, `atom & hi` when `true`, `!atom & lo` when `false`.
#[derive(Clone, Copy)]
enum At<'p> {
    Part(&'p Part<Row>),
    Bdd(&'p Bdd<Row>),
    Arm(&'p Bdd<Row>, bool),
}

impl At<'_> {
    /// The key of the node read as itself (`pos`) or as its complement: its id, and which arm.
    fn key(self, pos: bool) -> (u64, bool, u8) {
        match self {
            At::Part(p) => (p.id(), pos, 0),
            At::Bdd(b) => (b.id(), pos, 0),
            At::Arm(b, hi) => (b.id(), pos, 1 + u8::from(hi)),
        }
    }
}

/// An operand of a connective in [`Shape`]: a literal, or a node read as itself or as its
/// complement.
#[derive(Clone, Copy)]
enum Operand<'p> {
    Literal(Literal2),
    Node(At<'p>, bool),
}

/// A node read one step down, its negations pushed to the atoms.
enum Shape<'p> {
    Leaf(bool),
    Literal(Literal2),
    And(Operand<'p>, Operand<'p>),
    Or(Operand<'p>, Operand<'p>),
}

/// The shape of the node `at` read as itself (`pos`) or as its complement, each atom the
/// literal `literal` gives it; `None` for an atom it gives none. A diagram node `c ? hi : lo`
/// whose branches are not leaves is the union of its two arms.
fn shape<'p>(
    mut at: At<'p>,
    mut pos: bool,
    literal: &impl Fn(&Row) -> Option<Literal2>,
) -> Option<Shape<'p>> {
    loop {
        match at {
            At::Part(p) => match p.view() {
                Ok(b) => at = At::Bdd(b),
                Err(Form::Not(q)) => (at, pos) = (At::Part(q), !pos),
                Err(Form::Or(a, b) | Form::And(a, b)) => {
                    let (x, y) = (
                        Operand::Node(At::Part(a), pos),
                        Operand::Node(At::Part(b), pos),
                    );
                    // `!(a | b)` is `!a & !b`, and `!(a & b)` is `!a | !b`.
                    let or = matches!(p.view(), Err(Form::Or(..))) == pos;
                    return Some(if or {
                        Shape::Or(x, y)
                    } else {
                        Shape::And(x, y)
                    });
                }
            },
            At::Bdd(b) => {
                let (_, a, hi, lo) = match b.branch() {
                    Err(v) => return Some(Shape::Leaf(v == pos)),
                    Ok(n) => n,
                };
                let l = literal(a)?;
                let leaf = |x: &Bdd<Row>| x.branch().err().map(|v| v == pos);
                let node = |x| Operand::Node(At::Bdd(x), pos);
                return Some(match (leaf(hi), leaf(lo)) {
                    (Some(h), Some(_)) => Shape::Literal(if h { l } else { l ^ 1 }),
                    (_, Some(false)) => Shape::And(Operand::Literal(l), node(hi)),
                    (Some(false), _) => Shape::And(Operand::Literal(l ^ 1), node(lo)),
                    (Some(true), _) => Shape::Or(Operand::Literal(l), node(lo)),
                    (_, Some(true)) => Shape::Or(Operand::Literal(l ^ 1), node(hi)),
                    _ => Shape::Or(
                        Operand::Node(At::Arm(b, true), pos),
                        Operand::Node(At::Arm(b, false), pos),
                    ),
                });
            }
            At::Arm(b, hi) => {
                let (_, a, h, lo) = b.branch().ok()?;
                let l = literal(a)?;
                return Some(if hi {
                    Shape::And(Operand::Literal(l), Operand::Node(At::Bdd(h), pos))
                } else {
                    Shape::And(Operand::Literal(l ^ 1), Operand::Node(At::Bdd(lo), pos))
                });
            }
        }
    }
}

/// The 2-CNF of the tuple part `f` over `vars` variables, each atom the literal `literal`
/// gives it, when `f` is one by its structure: from the root through `and`s, each `or` has at
/// most two operands that are not `false`, and each of those is a literal or a meet of literals
/// through `and`s alone. `None` for any other part, and for an atom with no literal.
///
/// A meet under an `or` takes a variable of its own, `g`, with the clauses `!g | x` for each
/// operand `x`, so the `or` is the clause of the two variables, and a meet reached from many
/// `or`s is read once (Plaisted and Greenbaum's encoding: `g` true forces the meet, and a
/// value of `f` sets `g` to the meet's value, so the 2-CNF is satisfiable exactly when `f` is,
/// and a solution sets the first `vars` variables to a value of `f`). Each node and arm is read
/// once from the root and once as a meet, from a stack, so the time and the clauses are
/// linear in the part's nodes.
fn read_two_sat(
    f: &Part<Row>,
    vars: usize,
    literal: &impl Fn(&Row) -> Option<Literal2>,
) -> Option<TwoSat> {
    let mut s = TwoSat {
        vars,
        clauses: Vec::new(),
        meets: HashMap::new(),
    };
    // The operands that hold, and the nodes read from them.
    let mut holds = vec![Operand::Node(At::Part(f), true)];
    let mut read = std::collections::HashSet::new();
    // Each meet's variable with an operand the meet forces.
    let mut forces: Vec<(Literal2, Operand)> = Vec::new();
    while let Some(x) = holds.pop() {
        let (at, pos) = match x {
            Operand::Literal(l) => {
                s.clauses.push((l, l));
                continue;
            }
            Operand::Node(at, pos) => (at, pos),
        };
        if !read.insert(at.key(pos)) {
            continue;
        }
        match shape(at, pos, literal)? {
            Shape::Leaf(true) => {}
            Shape::Leaf(false) => s.contradiction(),
            Shape::Literal(l) => s.clauses.push((l, l)),
            Shape::And(x, y) => holds.extend([x, y]),
            Shape::Or(x, y) => {
                // The operands of the `or` and of the `or`s under it, the `false` ones left out.
                let (mut out, mut under, mut always) = (Vec::new(), vec![x, y], false);
                while let Some(d) = under.pop() {
                    let l = match d {
                        Operand::Literal(l) => l,
                        Operand::Node(at, pos) => match shape(at, pos, literal)? {
                            Shape::Leaf(b) => {
                                always |= b;
                                continue;
                            }
                            Shape::Literal(l) => l,
                            Shape::Or(x, y) => {
                                under.extend([x, y]);
                                continue;
                            }
                            Shape::And(x, y) => s.meet(at.key(pos), [x, y], &mut forces),
                        },
                    };
                    out.push(l);
                    if out.len() > 2 {
                        break;
                    }
                }
                match (always, &out[..]) {
                    (true, _) => {}
                    (false, []) => s.contradiction(),
                    (false, &[a]) => s.clauses.push((a, a)),
                    (false, &[a, b]) => s.clauses.push((a, b)),
                    _ => return None,
                }
            }
        }
    }
    while let Some((g, x)) = forces.pop() {
        let l = match x {
            Operand::Literal(l) => l,
            Operand::Node(at, pos) => match shape(at, pos, literal)? {
                Shape::Leaf(true) => continue,
                Shape::Leaf(false) => g ^ 1,
                Shape::Literal(l) => l,
                Shape::And(x, y) => s.meet(at.key(pos), [x, y], &mut forces),
                Shape::Or(..) => return None,
            },
        };
        s.clauses.push((g ^ 1, l));
    }
    Some(s)
}

impl TwoSat {
    /// A variable of its own, as its literal `true`.
    fn fresh(&mut self) -> Literal2 {
        self.vars += 1;
        2 * (self.vars - 1)
    }

    /// Clauses no value holds: a fresh variable both true and false.
    fn contradiction(&mut self) {
        let g = self.fresh();
        self.clauses.extend([(g, g), (g ^ 1, g ^ 1)]);
    }

    /// The variable of the meet with the key `key` and operands `xs`, made the first time, with
    /// each operand put on `forces`.
    fn meet<'p>(
        &mut self,
        key: (u64, bool, u8),
        xs: [Operand<'p>; 2],
        forces: &mut Vec<(Literal2, Operand<'p>)>,
    ) -> Literal2 {
        if let Some(&g) = self.meets.get(&key) {
            return g;
        }
        let g = self.fresh();
        self.meets.insert(key, g);
        forces.extend(xs.map(|x| (g, x)));
        g
    }

    /// A value of each variable that holds every clause, or `None` when there is none: a
    /// variable and its complement in one strongly connected component of the implication
    /// graph (`!a -> b` and `!b -> a` for each clause `a | b`). The components are found by
    /// Tarjan's algorithm on an explicit stack, each completed after every component it
    /// reaches, so a literal is set true when its component is completed before its
    /// complement's: then nothing true implies anything false. Time linear in the variables
    /// and clauses.
    fn solve(&self) -> Option<Vec<bool>> {
        let n = 2 * self.vars;
        // The edges out of each literal, as one list cut at `start`.
        let mut start = vec![0usize; n + 1];
        for &(a, b) in &self.clauses {
            start[(a ^ 1) + 1] += 1;
            start[(b ^ 1) + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let mut next = start.clone();
        let mut to = vec![0usize; start[n]];
        for &(a, b) in &self.clauses {
            for (from, x) in [(a ^ 1, b), (b ^ 1, a)] {
                to[next[from]] = x;
                next[from] += 1;
            }
        }
        const NONE: usize = usize::MAX;
        let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0; n], vec![NONE; n]);
        let (mut found, mut comps) = (0, 0);
        let mut on: Vec<usize> = Vec::new();
        // The walk: each literal entered and the position of its next edge.
        let mut walk: Vec<(usize, usize)> = Vec::new();
        for root in 0..n {
            if index[root] != NONE {
                continue;
            }
            index[root] = found;
            low[root] = found;
            found += 1;
            on.push(root);
            walk.push((root, start[root]));
            while let Some(&(v, e)) = walk.last() {
                if e < start[v + 1] {
                    let w = to[e];
                    let top = walk.len() - 1;
                    walk[top].1 += 1;
                    if index[w] == NONE {
                        index[w] = found;
                        low[w] = found;
                        found += 1;
                        on.push(w);
                        walk.push((w, start[w]));
                    } else if comp[w] == NONE {
                        low[v] = low[v].min(index[w]);
                    }
                    continue;
                }
                walk.pop();
                if let Some(&(u, _)) = walk.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    while let Some(w) = on.pop() {
                        comp[w] = comps;
                        if w == v {
                            break;
                        }
                    }
                    comps += 1;
                }
            }
        }
        (0..self.vars)
            .map(|v| (comp[2 * v] != comp[2 * v + 1]).then(|| comp[2 * v] < comp[2 * v + 1]))
            .collect()
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
            let ty = Type::union_all(cells.clone().map(|c| c.ty.clone()));
            let ks = cells
                .flat_map(|c| c.rows.iter().copied())
                .filter(|k| open.contains(k));
            (ty, ks.collect())
        });
        Some((j, classes.collect()))
    })
}

/// What a value of a type can be equal to, at one node of the trie `overlaps` builds: a
/// literal, the bare atom of the node's name, or a whole universe. An atom name and a tuple
/// length label the node below, which holds the keys of the payloads of that name or of the
/// first components of the tuples of that length. Two types with no key in common are disjoint.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Key<'a> {
    Bool(u8),
    Lit(usize, &'a Value),
    Atom(&'a std::sync::Arc<str>),
    Len(usize),
    /// The bare atom of the name of the node.
    Bare,
    /// A whole universe: 0 to 3 the literals of `Lits`, 4 the atoms, 5 the tuples, 6 the
    /// structs, 7 the morphisms.
    All(usize),
}

/// The keys `p` lists in universe `u` (0 to 3 the literals of `Lits`, 4 the atoms, 5 the
/// tuples), each with whether `p` holds a value of it, and whether `p` is cofinite there: it
/// then holds every value of each key it does not list. `none` is the empty type.
fn listed<'a>(p: &'a Parts, u: usize, none: &Type) -> (bool, Vec<(Key<'a>, bool)>) {
    match u {
        0..4 => {
            let l = [&p.ints, &p.rats, &p.floats, &p.strings][u];
            let ks = l.values.iter().map(|v| (Key::Lit(u, v), !l.cofinite));
            (l.cofinite, ks.collect())
        }
        4 => {
            let ks = p.atoms.names.iter();
            let ks = ks.map(|(n, a)| (Key::Atom(n), a.bare || a.payload != *none));
            (p.atoms.cofinite, ks.collect())
        }
        _ => {
            let ks = p.tuples.lens.iter();
            let ks = ks.map(|(&n, f)| (Key::Len(n), f.is_leaf() != Some(false)));
            (p.tuples.rest, ks.collect())
        }
    }
}

/// An edge of the trie `overlaps` builds: an atom name or a tuple length.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Edge<'a> {
    Atom(&'a std::sync::Arc<str>),
    Len(usize),
}

/// The trie of keys: node 0 is the whole type; below a node, one node per atom name and per
/// tuple length that a type holds there. Two nodes merged are one node from then on, and so
/// are their children by each edge.
struct Trie<'a> {
    /// Each node's children by edge; a merged node's children are its class root's.
    kids: Vec<HashMap<Edge<'a>, usize>>,
    /// The union-find of merged nodes.
    same: Vec<usize>,
}

impl<'a> Trie<'a> {
    fn find(&mut self, x: usize) -> usize {
        root(&mut self.same, x)
    }

    fn child(&mut self, x: usize, e: Edge<'a>) -> usize {
        let x = self.find(x);
        let next = self.kids.len();
        let y = *self.kids[x].entry(e).or_insert(next);
        if y == next {
            self.kids.push(HashMap::new());
            self.same.push(next);
        }
        self.find(y)
    }

    /// Makes `x` and `y` one node, and their children by each edge, in turn. The smaller map
    /// of children moves into the larger, so each child moves O(log n) times over all merges.
    fn merge(&mut self, x: usize, y: usize) {
        let mut todo = vec![(x, y)];
        while let Some((x, y)) = todo.pop() {
            let (x, y) = (self.find(x), self.find(y));
            if x == y {
                continue;
            }
            let (big, small) = match self.kids[x].len() >= self.kids[y].len() {
                true => (x, y),
                false => (y, x),
            };
            self.same[small] = big;
            for (e, c) in std::mem::take(&mut self.kids[small]) {
                match self.kids[big].entry(e) {
                    Entry::Vacant(v) => {
                        v.insert(c);
                    }
                    Entry::Occupied(o) => todo.push((*o.get(), c)),
                }
            }
        }
    }
}

/// What one type puts in the trie, found by a walk over the types inside it: the keys it holds
/// at each node, what it lists in each universe at each node, and the nodes under which it holds
/// every value.
struct Walk<'a> {
    /// Each type inside met so far, by structure, and the node it was first met at.
    seen: HashMap<&'a Type, usize>,
    /// The types inside still to walk, with their nodes.
    todo: Vec<(usize, &'a Parts)>,
}

impl<'a> Walk<'a> {
    /// Puts the values of `t` under node `y`. A type met again adds nothing: met at another
    /// node, that node and the first are merged, so its keys under the first are its keys
    /// under both.
    fn enter(&mut self, trie: &mut Trie<'a>, y: usize, t: &'a Type) {
        match self.seen.entry(t) {
            Entry::Vacant(v) => {
                v.insert(y);
                self.todo.push((y, t.p()));
            }
            Entry::Occupied(o) => trie.merge(*o.get(), y),
        }
    }
}

/// The root of `i` in the union-find `parent`, halving the path.
fn root(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

/// Joins the classes of `a` and `b`; the smaller index is the root.
fn join(parent: &mut [usize], a: usize, b: usize) {
    let (a, b) = (root(parent, a), root(parent, b));
    parent[a.max(b)] = a.min(b);
}

/// The types `ps` in classes, by index in order of their first members, joined when they share
/// a key: two types of different classes are disjoint. The keys sit in a trie: the atoms of
/// one name are keyed by their payload's keys under the node of the name, and the tuples of one
/// length by the keys of their first component under the node of the length, so `#a((1,))` and
/// `#a((2,))`, or `(1,)` and `(2,)`, share no key. A type that holds every value under a node,
/// such as every tuple of a length, shares a key with each type that holds a key under it. At
/// each node, the cofinite types of a universe share it whole. A finite type meets one of them
/// exactly when it holds a key that one does not list, so it shares the whole universe when it
/// holds a key outside those every cofinite type lists; that set is the meet of their lists,
/// taken from the shortest. Each type inside a type is walked once for it, found by its
/// structure, so the classes do not depend on whether equal types are one shared type; met
/// again at another node, it merges that node with the first. The work is the size of the
/// types times the log of the keys, and each child of a merged node moves O(log n) times.
// Complexity tradeoff: the keys are coarser than the meet of two types in three cases, each of
// which joins disjoint types: tuples are keyed by their first component only, so `(1, 2)` and
// `(1, 3)` land in one class; a tuple part that is not within its tuple types (a negated tuple
// type outside any other) holds every tuple of its length, so it joins every type under that
// node; and a type met at two nodes inside one type merges the two, so `(2,)` and `#e((2,))`
// are joined beside `(1,) | #e((1,))`. Joined types get the later steps of `tuples` on the part
// whole; where those steps do not decide it, the part counts as inhabited for `is_empty`, and
// `verdict` answers `Refused(TupleSplit)` (a subtyping check fails and names the types). The
// cost of a joined class is that of deciding it whole: k pinwheels joined in one class by the
// first two cases cost order k^2 (78,974M instructions at k = 128 with one end outside every
// tuple type, 19,555M at k = 64; 62,927M and 15,893M with one first component), while merged
// nodes join only types that hold one key under them, and k pinwheels whose ends repeat one
// integer under a tuple and a payload stay k classes (4,508M instructions at k = 512, 9.0
// times k = 64). Why: the meet of two tuple types
// is an emptiness check in each component, and testing it for each pair costs their square and
// a search each, while one component's keys cost the size of the types; a tuple part outside
// its tuple types meets another type exactly when that type is not within the union of the
// part's negated tuple types, which is itself an emptiness check; walking a type inside a type
// once per node it is met at would unfold a shared type, exponential in its nesting. Trigger:
// cells on the split component that differ only after the first component of a tuple, a
// negated tuple type, or one type reached by two paths inside a cell. Tests:
// `types::empty::tests::classes_are_exact_on_cofinite_sets_names_and_lengths_and_join_tuples_by_first_component`
// (`(1, 2)` and `(1, 3)` in one class, `#a((1,))` and `#a((2,))` apart, cofinite sets joined
// only where they meet),
// `types::empty::tests::classes_join_under_a_tuple_part_outside_its_types_and_merge_the_nodes_of_a_type_met_twice`,
// and in `l01_23_subtyping::scaling`: `pinwheels_whose_ends_share_a_first_component_are_decided`,
// `pinwheels_with_an_end_outside_every_tuple_type_are_decided`,
// `pinwheels_joined_in_one_class_are_decided_at_quadratic_cost` (order k^2 at k = 8 and 64),
// `pinwheels_whose_ends_repeat_an_integer_agree_with_the_model` and `…_scale` (k = 64 and 512,
// shared and built apart), and `payload_and_one_tuple_pinwheels_scale`. COMPLEXITY.md K36. A
// complete solution needs the connected parts of the graph in which two types meet: for tuples
// that is the intersection graph of boxes, whose edges can number the square of the types, and
// each edge an emptiness check.
fn overlaps<'a>(ps: impl Iterator<Item = &'a Parts>) -> Vec<Vec<usize>> {
    let none = Type::empty();
    let mut trie = Trie {
        kids: vec![HashMap::new()],
        same: vec![0],
    };
    // Each type's keys, as (node, key, type).
    let mut points: Vec<(usize, Key<'a>, usize)> = Vec::new();
    // Each type's lists, as (node, universe, cofinite, keys, type).
    #[allow(clippy::type_complexity)]
    let mut lists: Vec<(usize, usize, bool, Vec<(Key<'a>, bool)>, usize)> = Vec::new();
    // The nodes under which a type holds every value, as (node, type).
    let mut wholes: Vec<(usize, usize)> = Vec::new();
    let mut parent: Vec<usize> = Vec::new();
    for (i, p) in ps.enumerate() {
        parent.push(i);
        let mut walk = Walk {
            seen: HashMap::new(),
            todo: vec![(0, p)],
        };
        while let Some((x, p)) = walk.todo.pop() {
            let bools = (0..2u8).filter(|b| p.bools >> b & 1 == 1);
            points.extend(bools.map(|b| (x, Key::Bool(b), i)));
            if p.structs {
                points.push((x, Key::All(6), i));
            }
            if p.morphisms.is_leaf() != Some(false) {
                points.push((x, Key::All(7), i));
            }
            for (n, a) in &p.atoms.names {
                if !a.bare && a.payload == none {
                    continue;
                }
                let y = trie.child(x, Edge::Atom(n));
                if a.bare {
                    points.push((y, Key::Bare, i));
                }
                if a.payload != none {
                    walk.enter(&mut trie, y, &a.payload);
                }
            }
            for (&n, f) in &p.tuples.lens {
                if f.is_leaf() == Some(false) {
                    continue;
                }
                let y = trie.child(x, Edge::Len(n));
                // Every value of a part `false` outside its tuple types is in one of them.
                if n == 0 || f.eval3(&|_| Some(false)) != Some(false) {
                    wholes.push((y, i));
                    continue;
                }
                f.atoms(&mut |row: &'a Row| {
                    walk.enter(&mut trie, y, &row[0]);
                    true
                });
            }
            for u in 0..6 {
                let (cofinite, ks) = listed(p, u, &none);
                let lits = ks
                    .iter()
                    .filter(|(k, held)| *held && matches!(k, Key::Lit(..)));
                points.extend(lits.map(|&(k, _)| (x, k, i)));
                lists.push((x, u, cofinite, ks, i));
            }
        }
    }
    // Each node's merged node, from here on its name.
    let at: Vec<usize> = (0..trie.same.len()).map(|x| trie.find(x)).collect();
    // Per node and universe with a cofinite type, the keys every cofinite type there lists.
    let mut cofinites: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for (l, (x, u, cofinite, _, _)) in lists.iter().enumerate() {
        if *cofinite {
            cofinites.entry((at[*x], *u)).or_default().push(l);
        }
    }
    let shut: BTreeMap<(usize, usize), BTreeSet<Key<'a>>> = cofinites
        .into_iter()
        .map(|(at, ls)| {
            let shortest = *ls
                .iter()
                .min_by_key(|&&l| lists[l].3.len())
                .expect("a group has a list");
            let mut meet: BTreeSet<Key<'a>> = lists[shortest].3.iter().map(|&(k, _)| k).collect();
            for &l in &ls {
                if l != shortest {
                    let ks: BTreeSet<Key<'a>> = lists[l].3.iter().map(|&(k, _)| k).collect();
                    meet.retain(|k| ks.contains(k));
                }
            }
            (at, meet)
        })
        .collect();
    for (x, u, cofinite, ks, i) in &lists {
        let outside = |s: &BTreeSet<Key>| ks.iter().any(|(k, held)| *held && !s.contains(k));
        if *cofinite || shut.get(&(at[*x], *u)).is_some_and(outside) {
            points.push((*x, Key::All(*u), *i));
        }
    }
    // Per node, a type that holds every value under it or under a node above it. Merged nodes
    // can make a node the child of several nodes, or of one below it, so each node gets a type
    // once and passes it to its children once.
    let mut whole: Vec<Option<usize>> = vec![None; at.len()];
    let mut down = Vec::new();
    for &(x, i) in &wholes {
        match whole[at[x]] {
            Some(w) => join(&mut parent, w, i),
            None => {
                whole[at[x]] = Some(i);
                down.push(at[x]);
            }
        }
    }
    while let Some(x) = down.pop() {
        let w = whole[x].expect("a node passed down has a type");
        for &c in trie.kids[x].values() {
            match whole[at[c]] {
                Some(v) => join(&mut parent, v, w),
                None => {
                    whole[at[c]] = Some(w);
                    down.push(at[c]);
                }
            }
        }
    }
    let mut first: BTreeMap<(usize, Key<'a>), usize> = BTreeMap::new();
    for (x, k, i) in points {
        let x = at[x];
        let j = *first.entry((x, k)).or_insert(i);
        join(&mut parent, i, j);
        if let Some(w) = whole[x] {
            join(&mut parent, i, w);
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

/// Whether `k` is known empty for good without a search: the empty type, or a recursive type
/// its group decided empty. A type the search reads is not taken, since its answer may rest on
/// an assumption the search later drops.
fn known_empty(k: &Type) -> bool {
    *k == Type::empty() || k.judged() == Some(true)
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

    /// The region of the part `f` on the box `r`, made by a search of its own.
    fn region(r: Vec<Type>, f: &Part<Row>) -> Region {
        let f = f.clone();
        Search::default().run(move |d| Box::pin(async move { d.region(r, &f).await }))
    }

    /// The classes of `overlaps` on everyday types: a finite set and a cofinite one are joined
    /// exactly when they meet, at the top and inside an atom payload; two types of one atom
    /// name or tuple length are apart when they are disjoint inside it, a payload of a payload
    /// too; two tuples that share a first component are joined even when they are disjoint
    /// (the tradeoff at `overlaps`).
    #[test]
    fn classes_are_exact_on_cofinite_sets_names_and_lengths_and_join_tuples_by_first_component() {
        let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
        let one = |t: Type| Type::tuple(vec![t]);
        let ts = [
            lit(3),                              // 0, in no cofinite set
            &Type::int() - &lit(3),              // 1, meets 2, 7 and 8
            lit(4),                              // 2
            Type::atom_with("a", &one(lit(1))),  // 3, disjoint from 4 and 14
            Type::atom_with("a", &one(lit(2))),  // 4
            one(lit(1)),                         // 5, disjoint from 6
            one(lit(2)),                         // 6
            &Type::int() - &(&lit(3) | &lit(5)), // 7
            lit(5),                              // 8, in 1, not in 7
            // 9, every atom but `#a`, `#a(..)`, `#b` and `#b(..)`, so apart from 12 and 13
            &(&(&(&Type::with(|p| p.atoms.cofinite = true) - &Type::atom_with("a", &Type::top()))
                - &Type::atom("a"))
                - &Type::atom_with("b", &Type::top()))
                - &Type::atom("b"),
            Type::tuple(vec![lit(1), lit(2)]), // 10, disjoint from 11 and joined with it
            Type::tuple(vec![lit(1), lit(3)]), // 11
            Type::atom_with("b", &one(Type::atom_with("c", &one(lit(1))))), // 12, apart from 13
            Type::atom_with("b", &one(Type::atom_with("c", &one(lit(2))))), // 13
            Type::atom_with("a", &one(&Type::int() - &lit(1))), // 14, meets 4, not 3
        ];
        let classes = overlaps(ts.iter().map(Type::p));
        let expected: Vec<Vec<usize>> = vec![
            vec![0],
            vec![1, 2, 7, 8],
            vec![3],
            vec![4, 14],
            vec![5],
            vec![6],
            vec![9],
            vec![10, 11],
            vec![12],
            vec![13],
        ];
        assert_eq!(classes, expected);
    }

    /// The other two cases of the tradeoff at `overlaps`. A tuple part outside its tuple types,
    /// `(int,) \ (1,)`, holds every one-tuple, so it is joined with `(1,)` although the two are
    /// disjoint. A type met at two nodes inside one type, the `1` of `(1,) | #e((1,))`, merges
    /// the two nodes, so `(2,)` and `#e((2,))` are joined although they are disjoint; `(3,)`
    /// stays apart, and so do the classes of disjoint types under the merged node. The classes
    /// do not depend on whether the two `1`s are one shared type or two equal ones. A recursive
    /// type that holds itself as a first component merges a node with one below it.
    #[test]
    fn classes_join_under_a_tuple_part_outside_its_types_and_merge_the_nodes_of_a_type_met_twice() {
        use super::super::rec::{Def, Expr, Group};
        let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
        let one = |t: Type| Type::tuple(vec![t]);
        let e = |t: Type| Type::atom_with("e", &one(t));
        let negated = [one(lit(1)), &one(Type::int()) - &one(lit(1)), one(lit(2))];
        let classes = overlaps(negated.iter().map(Type::p));
        assert_eq!(classes, vec![vec![0, 1, 2]]);
        let shared = lit(1);
        for twice in [
            &one(shared.clone()) | &e(shared.clone()),
            &one(lit(1)) | &e(lit(1)),
        ] {
            let ts = [twice, one(lit(2)), e(lit(2)), one(lit(3)), e(lit(4))];
            let classes = overlaps(ts.iter().map(Type::p));
            assert_eq!(classes, vec![vec![0], vec![1, 2], vec![3], vec![4]]);
        }
        // `T = #nil | #cons((T, int))`.
        let cons = Expr::Atom(
            "cons".into(),
            vec![Expr::Ref(0, vec![]), Expr::Type(Type::int())],
        );
        let def = Def {
            name: "T".into(),
            params: vec![],
            body: Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
        };
        let t = Group::new(vec![def])
            .expect("a group")
            .instance(vec![])
            .remove(0);
        let ts = [t, Type::atom("nil"), Type::atom("x"), lit(5)];
        let classes = overlaps(ts.iter().map(Type::p));
        assert_eq!(classes, vec![vec![0, 1], vec![2], vec![3]]);
    }

    /// `inverse` against a scan, and `residue_length` against a scan of the lengths from 1 on
    /// every choice of at most two classes of `all` and three of `none` with periods 1 to 6,
    /// from a fixed sequence: a length it gives is in every class of `all` and in none of
    /// `none`; it gives one whenever the shares of `none` sum to less than one; and it gives one
    /// only when the scan finds one.
    #[test]
    fn the_residue_length_agrees_with_a_scan() {
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
        let (mut exists, mut given) = (0, 0);
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
            let scanned = (1..=60).find(|&n| fits(n));
            let found = residue_length(&all, &none);
            if let Some(n) = &found {
                let n = u64::try_from(n).expect("below the lcm");
                assert!(n >= 1 && fits(n), "{all:?} {none:?}: {n}");
            }
            assert!(found.is_none() || scanned.is_some(), "{all:?} {none:?}");
            let sum: f64 = none
                .iter()
                .filter(|&&(p, at)| (1..=60).any(|n| fits_all(&all, n) && n % p == at))
                .map(|&(p, _)| {
                    let l = all.iter().fold(1, |l, &(q, _)| l / gcd(l, q) * q);
                    gcd(l, p) as f64 / p as f64
                })
                .sum();
            if sum < 1.0 && scanned.is_some() {
                assert!(found.is_some(), "{all:?} {none:?}: shares {sum}");
            }
            exists += usize::from(scanned.is_some());
            given += usize::from(found.is_some());
        }
        // The choice misses a length only when the shares sum to one or more.
        assert!(given * 10 >= exists * 9, "{given} of {exists}");
    }

    fn fits_all(all: &[(u64, u64)], n: u64) -> bool {
        all.iter().all(|&(p, at)| n % p == at)
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
        let g = region(vec![Type::top(); 2], f);
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
        let g = region(vec![Type::top(); 3], f);
        let sizes: Vec<Vec<usize>> = g
            .cells
            .iter()
            .map(|cells| cells.iter().map(|c| c.rows.len()).collect())
            .collect();
        assert_eq!(sizes, [vec![1, 1, 1, 1], vec![4], vec![2, 2]]);
        assert_eq!(g.opens, [4, 4, 4]);
        let mut h = region(vec![Type::top(), Type::int(), Type::top()], f);
        assert_eq!(h.opens, [4, 0, 4]);
        assert!(h.loose.iter().all(|&(n, at)| (n, at) == (2, 2)));
        // Narrowing the last component to `0` closes the cell `1` as missed for both of its
        // tuple types at once, and leaves `0` to be tested again.
        h.shrink(2, lit(0));
        let h = Search::default().run(move |d| {
            Box::pin(async move {
                let mut h = h;
                d.retest(&mut h).await;
                h
            })
        });
        for (k, a) in h.atoms.iter().enumerate() {
            assert_eq!(h.missed[k], usize::from(a[2] == lit(1)), "{k}");
        }
        assert_eq!(h.opens, [4, 0, 0]);
    }

    /// A small generator for the tests below: xorshift.
    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    /// Random clauses of one and two literals on `vars` variables.
    fn clauses(s: &mut u64, vars: usize) -> Vec<(Literal2, Literal2)> {
        let m = 1 + next(s) as usize % (3 * vars);
        let lit = |s: &mut u64| next(s) as usize % (2 * vars);
        (0..m)
            .map(|_| {
                let a = lit(s);
                if next(s).is_multiple_of(3) {
                    (a, a)
                } else {
                    (a, lit(s))
                }
            })
            .collect()
    }

    /// Whether the literal `l` holds of the values `x`.
    fn holds2(x: &[bool], l: Literal2) -> bool {
        x[l / 2] == l.is_multiple_of(2)
    }

    /// `TwoSat::solve` answers as enumeration does on random clause sets of up to 12
    /// variables, and each solution it gives holds every clause.
    #[test]
    fn two_sat_solve_agrees_with_enumeration_and_its_solutions_hold() {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        let mut seen = [0usize; 2];
        for vars in 1..=12 {
            for _ in 0..40 {
                let cs = clauses(&mut s, vars);
                let sat = (0u64..1 << vars).any(|m| {
                    let x: Vec<bool> = (0..vars).map(|v| m >> v & 1 == 1).collect();
                    cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b))
                });
                let t = TwoSat {
                    vars,
                    clauses: cs.clone(),
                    meets: HashMap::new(),
                };
                let x = t.solve();
                assert_eq!(x.is_some(), sat, "{vars} variables, {cs:?}");
                if let Some(x) = x {
                    assert!(cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b)));
                }
                seen[usize::from(sat)] += 1;
            }
        }
        assert!(seen[0] > 20 && seen[1] > 20, "{seen:?}");
    }

    /// The value the search shows for a satisfiable 2-CNF of 48 bits is a tuple of 48 bits
    /// that holds every clause, read from the values shown, not from the search's own check.
    #[test]
    fn the_value_shown_for_a_two_cnf_holds_every_clause() {
        let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
        let vars = 48;
        let mut s = 0x2545_f491_4f6c_dd1d;
        let mut shown = 0;
        for _ in 0..12 {
            let cs: Vec<(Literal2, Literal2)> = (0..vars)
                .map(|_| {
                    let mut l = || next(&mut s) as usize % (2 * vars);
                    (l(), l())
                })
                .collect();
            let cylinder = |l: Literal2| {
                let mut c = vec![Type::top(); vars];
                c[l / 2] = lit(i64::from(l.is_multiple_of(2)));
                Type::tuple(c)
            };
            let mut t = Type::tuple(vec![&lit(0) | &lit(1); vars]);
            for &(a, b) in &cs {
                t = &t & &(&cylinder(a) | &cylinder(b));
            }
            let sat = TwoSat {
                vars,
                clauses: cs.clone(),
                meets: HashMap::new(),
            }
            .solve()
            .is_some();
            let mut search = Search {
                strict: true,
                refuse_forks: true,
                ..Search::default()
            };
            let Some(v) = search.rep(&t) else {
                assert!(!sat, "{cs:?}");
                continue;
            };
            let Rep::Tuple(vs) = &search.shown[v] else {
                panic!("a tuple is shown")
            };
            let x: Vec<bool> = (vs.iter())
                .map(|&i| match &search.shown[i] {
                    Rep::Value(Value::Int(1)) => true,
                    Rep::Value(Value::Int(0)) => false,
                    _ => panic!("a bit is shown"),
                })
                .collect();
            assert!(cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b)));
            shown += 1;
        }
        assert!(shown > 0);
    }
}
